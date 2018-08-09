# Copyright (c) 2018-present Nuno Lopes.
# Distributed under the MIT license that can be found in the LICENSE file.

from z3 import *

# TODO:
# * add support for address spaces

gbl_maybe_observed = {}

def abs(x):
  return If(x >= 0, x, -x)


class pointer:
  def __init__(self, name = None):
    self.name = name
    # 00 - logic, 01 -- physical, 1x -- poison
    self.ty    = BitVec(name + '_ty', 2)
    self.lid   = BitVec(name + '_lid', 3)
    self.off   = BitVec(name + '_off', 8)
    self.addrs = BitVecVal(0,1) ## TODO

  def is_logic(self):
    return self.ty == 0

  def is_physical(self):
    return self.ty == 1

  def is_poison(self):
    return Extract(1, 1, self.ty) == 1

  def logic_id(self):
    return self.lid

  def offset(self):
    return self.off

  def addrspace(self):
    return self.addrs

  def size(self):
    return size_id(self.logic_id())

  def observed(self):
    return observed_id(self.logic_id())

  def phy_base_addr(self):
    global gbl_maybe_observed
    gbl_maybe_observed[self.name] = self
    return addr_id(self.logic_id())

  def phy_addr(self):
    return self.phy_base_addr() + self.offset()

  def is_null(self):
    return And(self.is_physical(), self.offset() == 0)

  def eq_except_offset(self, q):
    return And(
      self.ty    == q.ty,
      Implies(self.is_logic(), self.lid == q.lid),
      self.addrs == q.addrs
    )

  def __eq__(self, other):
    lme,c1  = blockof(self)
    loth,c2 = blockof(other)
    return And(
      self.eq_except_offset(other),
      self.off == other.off,
      # accessing both pointers should have same behavior, so assume logic ids
      # have to be the same (since there are 2 possible ones for the p+n case)
      Implies(self.is_physical(), And(c1, c2, lme.logic_id() == loth.logic_id()))
    )

  def eval(self, m):
    access = m.eval(access_size(self.name))
    if m.eval(self.is_logic()):
      return "Log(%s, %s), phy=%s, sz=%s" %\
               (m.eval(self.logic_id()), m.eval(self.offset()).as_signed_long(),
                m.eval(self.phy_addr()), access)

    if m.eval(self.is_poison()):
      return "poison"

    assert(m.eval(self.is_physical()))
    l, _ = blockof(self)
    return "Phy(%s), block=%s, sz=%s" % (m.eval(self.offset()),
                                         m.eval(l.logic_id()), access)


def observed_id(id):
  return Function('is_observed', id.sort(), BoolSort())(id)

def size_id(id):
  return Function('size', id.sort(), BitVecSort(8))(id)

def addr_id(id):
  return Function('phy', id.sort(), BitVecSort(8))(id)

def max_size():
  return BitVecVal(-1, 8)

def access_size(name):
  return BitVec('s'+name, 8)

def offsetvar(name):
  return BitVec(name, 8)

def blockof(p):
  t = pointer('blockof_' + p.name)
  return t, And(
    t.is_logic(),
    t.observed(),
    t.offset() == p.offset() - t.phy_base_addr(),
    UGE(p.offset(), t.phy_base_addr()),
    ULE(p.offset(), t.phy_base_addr() + t.size())
  )

# p == x + w
def gep(p, x, w):
  return And(
    p.offset() == x.offset() + w,
    p.eq_except_offset(x))

# p == x + w
def gep_inbounds(p, x, w):
  lp, cnstrp = blockof(p)
  lx, cnstrx = blockof(x)
  return And(
    gep(p, x, w),
    SignExt(1, x.offset() + w) == SignExt(1, x.offset()) + SignExt(1, w),

    If(x.is_logic(),
       And(ULE(x.offset(), x.size()),
           ULE(x.offset() + w, x.size())),

       And(cnstrp,
           cnstrx,
           lp.logic_id() == lx.logic_id()
       ))
  )

def overlap(op,sp,oq,sq):
  return And(sp != 0, sq != 0,
             If(ULE(op, oq),
                ULT(oq - op, sp),
                ULT(op - oq, sq)
             )
         )

def ub_logic(p,sp):
  return Or(UGT(p.offset(), p.size()),
            And(sp != max_size(), UGT(sp, p.size() - p.offset()))
           )

def ub_phy(p,sp):
  lp, cnstr = blockof(p)
  return Or(
    And(p.addrspace() == 0, p.offset() == 0),

    # an access can only touch 1 block
    Not(cnstr),
    And(sp != max_size(), UGT(sp, lp.size() - lp.offset()))
  )

def not_ub(p,sp):
  return And(
    Not(p.is_poison()),
    If(p.is_logic(), Not(ub_logic(p,sp)), Not(ub_phy(p,sp)))
  )

def truncate_access(p, s):
  return If(s == max_size(), p.size() - p.offset(), s)

def ptr_ty_cases(p, sp, q, sq, bothlogic, onelogic, bothphy):
  return If(p.is_logic(),
            If(q.is_logic(),
               bothlogic,
               onelogic(p, sp, q, sq)),
            If(q.is_logic(),
               onelogic(q, sq, p, sp),
               bothphy)
            )

def noalias(p,sp,q,sq):
  max = max_size()

  # p logical, q physical
  def logphy(p,sp,q,sq):
    lq, cnstr = blockof(q)
    return Or(ub_logic(p,sp),
              ub_phy(q,sq),
              Not(p.observed()),
              Not(cnstr),
              Not(overlap(p.phy_addr(), truncate_access(p, sp),
                          q.offset(), truncate_access(lq, sq)))
            )

  lp, cnstrp = blockof(p)
  lq, cnstrq = blockof(q)

  return Or(p.is_poison(),
            q.is_poison(),
            ptr_ty_cases(p,sp,q,sq,
              # both logical
              Or(ub_logic(p,sp),
                 ub_logic(q,sq),
                 p.logic_id() != q.logic_id(),
                 Not(overlap(p.offset(), truncate_access(p, sp),
                             q.offset(), truncate_access(q, sq)))
              ),

              # p logical, q physical
              logphy,

              # both physical
              Or(ub_phy(p,sp),
                 ub_phy(q,sq),
                 Not(cnstrp),
                 Not(cnstrq),
                 Not(overlap(p.offset(), truncate_access(lp, sp),
                             q.offset(), truncate_access(lq, sq)))
              )
            ))

def mustalias(p,sp,q,sq):
  # p logical, q physical
  def logphy(p,sp,q,sq):
    return And(p.observed(),
               p.phy_addr() == q.offset())

  return ptr_ty_cases(p,sp,q,sq,
    # both logical
    And(p.logic_id() == q.logic_id(),
        p.offset() == q.offset()),

      # p logical, q physical
      logphy,

      # both physical
      p.offset() == q.offset()
  )

def partialalias(p,sp,q,sq):
  # p logical, q physical
  def logphy(p,sp,q,sq):
    lq, cnstr = blockof(q)
    return And(p.observed(),
               cnstr,
               overlap(p.phy_addr(), truncate_access(p, sp),
                       q.offset(), truncate_access(lq, sq)))

  lp, cnstrp = blockof(p)
  lq, cnstrq = blockof(q)
  return ptr_ty_cases(p,sp,q,sq,
    # both logical
    And(p.logic_id() == q.logic_id(),
        overlap(p.offset(), truncate_access(p, sp),
                q.offset(), truncate_access(q, sq))),

    # p logical, q physical
    logphy,

    # both physical
    And(cnstrp,
        cnstrq,
        overlap(p.offset(), truncate_access(lp, sp),
                q.offset(), truncate_access(lq, sq)))
  )

def alias(p,sp,q,sq):
  return If(noalias(p,sp,q,sq),
            BitVecVal(0, 2),
            If(mustalias(p,sp,q,sq),
               BitVecVal(1, 2),
               If(partialalias(p,sp,q,sq),
                  BitVecVal(2, 2),
                  BitVecVal(3, 2))))

def merge_alias(a, b):
  return If(a == b,
            a,
            # must /\ partial -> partial
            If(Or(And(a == 1, b == 2),
                  And(a == 2, b == 1)),
               BitVecVal(2, 2),
               BitVecVal(3, 2)))

def run_alias(v,p,sp,q,sq):
  return If(v == 0,
            noalias(p,sp,q,sq),
            If(v == 1,
               mustalias(p,sp,q,sq),
               If(v == 2,
                  partialalias(p,sp,q,sq),
                  True)))


def gen_side_pre():
  global gbl_maybe_observed
  ret = []
  # addrs should not overflow
  for p in gbl_maybe_observed.values():
    ret.append(
      Implies(p.is_logic(),
              And(Implies(p.addrspace() == 0, p.phy_base_addr() != 0),
              ULT(p.phy_base_addr(), -p.size()),
              # can only allocate up to half addr space
              ULE(p.size(), 127)
             )))

  # all phy addrs must be disjoint
  vars = list(gbl_maybe_observed.values())
  for i in range(0, len(vars)):
    for j in range(i+1, len(vars)):
      p = vars[i]
      q = vars[j]
      ret.append(Implies(
        And(p.logic_id() != q.logic_id(), p.is_logic(), q.is_logic()),
        Not(overlap(p.phy_base_addr(), p.size(), q.phy_base_addr(), q.size()))
      ))
  return ret


def print_model(m):
  print('\nPointers:')
  for p in gbl_maybe_observed.values():
    if p.name.startswith('blockof_'):
      continue
    print("%s: %s" % (p.name, p.eval(m)))

  print('\nMemory blocks:')
  seen = set()
  for p in gbl_maybe_observed.values():
    id = m.eval(p.logic_id())
    if id in seen:
      continue
    seen.add(id)
    print('Block %s -> base = %s, sz = %s%s' %
          (id, m.eval(addr_id(id)), m.eval(size_id(id)),
           ', observed' if m.eval(observed_id(id)) else ''))

gbl_proof_num = 0

def prove(e, buggy=False):
  global gbl_maybe_observed, gbl_proof_num
  gbl_proof_num += 1

  if len(sys.argv) > 1 and sys.argv[1] != str(gbl_proof_num):
    print('%d: Skip' % gbl_proof_num)

  else:
    s = Then('ackermannize_bv', 'qfbv').solver()
    s.add(gen_side_pre())
    s.add(Not(e))
    #with open('bench.smt2', 'w') as f:
    #  f.write(s.to_smt2())
    r = s.check()
    if r != unsat:
      if r == sat:
        if buggy:
          print('%d: Bug found' % gbl_proof_num)
        else:
          print('%d: Proof failed' % gbl_proof_num)
          print(e)
          print(s.model())
          print_model(s.model())
          exit(-1)
      else:
        assert(r == unknown)
        print('%d: Solver returned unknown' % gbl_proof_num)
        print(e)
    elif not buggy:
      print('%d: Correct' % gbl_proof_num)
    else:
      print('%d: Expect bug but verified' % gbl_proof_num)
      print(e)
      exit(-1)
  gbl_maybe_observed = {}


p = pointer('p')
sp = access_size('p')
q = pointer('q')
sq = access_size('q')
x = pointer('x')
y = pointer('y')
w = offsetvar('w')
z = offsetvar('z')
p1 = pointer('p1')
p2 = pointer('p2')
q1 = pointer('q1')
q2 = pointer('q2')
c = Bool('c')


#######################

# 1
prove(Implies(
  And(
    not_ub(p,sp),
    not_ub(q,sq),
    sp != 0,
    sq != 0,
    sp != max_size(),
    sq != max_size(),
    noalias(p,sp,q,sq)),
  Not(mustalias(p,sp,q,sq))
))

#######################

# 2
prove(Implies(
  And(
    not_ub(p,sp),
    not_ub(q,sq),
    noalias(p,sp,q,sq)),
  Not(partialalias(p,sp,q,sq))
))

#######################

# 3
prove(Implies(
  And(
    not_ub(p,sp),
    not_ub(q,sq),
    sp != 0,
    sq != 0,
    sp != max_size(),
    sq != max_size(),
    mustalias(p,sp,q,sq)
  ),
  partialalias(p,sp,q,sq)
))

#######################

# 4
prove(Implies(
  Or(sp == 0, sq == 0),
  noalias(p, sp, q, sq)))

#######################

# 5
prove(Implies(
  Or(p.is_poison(), q.is_poison()),
  noalias(p, sp, q, sq)))

#######################

# 6
print("FIXME: should be ok: null + x -> UB")
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      Or(And(x.is_null(), x.addrspace() == 0),
         And(y.is_null(), y.addrspace() == 0))
    ),
  noalias(p, sp, q, sq)), True)

#######################

# 7
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      x.is_logic(),
      y.is_logic(),
      x.logic_id() != y.logic_id()
    ),
  noalias(p, sp, q, sq)))

#######################

# 8
prove(Implies(
  And(not_ub(p,sp),
      not_ub(q,sq),
      sp != max_size(),
      q.is_logic(),
      UGT(sp, q.size())
    ),
  noalias(p, sp, q, sq)))

#######################

# 9
prove(Implies(
  And(gep(p, x, w),
      gep(q, x, z),
      x.is_logic(),
      sp == x.size(),
      sp != max_size(),
      not_ub(p, sp),
      not_ub(q, sq),
      sq != 0
    ),
  partialalias(p, sp, q, sq)), True)

#######################

# 10
prove(True)
## TODO
"""
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      x.is_argument(), # ??
      y.is_locally_allocated()  # ??
    ),
  noalias(p, sp, q, sq)))
"""

#######################

# 11
prove(True)
## TODO
"""
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      x.must_escape(), # ??
      y.is_locally_allocated(),  # ??
      Not(y.may_escape()) #?
    ),
  noalias(p, sp, q, sq)))
"""

#######################

# 12
prove(True)
## TODO
"""
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      x.is_const(), # ??
      q.is_logic(),
      Not(q.is_const_obj()) # ??
    ),
  noalias(p, sp, q, sq)))
"""

#######################

# 13
prove(Implies(
  And(If(c, p == p1, p == p2),
      If(c, q == q1, q == q2)
    ),
  run_alias(merge_alias(alias(p1,sp,q1,sq),
                        alias(p2,sp,q2,sq)),
            p,sp,q,sq)))

#######################

#14
prove(Implies(
  If(c, p == p1, p == p2),
  run_alias(merge_alias(alias(p1,sp,q,sq),
                        alias(p2,sp,q,sq)),
            p,sp,q,sq)))

#######################

#15
prove(Implies(
  And(gep_inbounds(p, x, w),
      q.is_logic(),
      w >= q.offset() + sq,
      sq != max_size()
    ),
  noalias(p, sp, q, sq)))

#######################

#16
# TODO: report bug
prove(Implies(
  And(gep(p, x, w),
      noalias(x, max_size(), q, max_size())
    ),
  noalias(p, sp, q, sq)), True)

#######################

#17
# TODO: report bug
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      noalias(x, max_size(), y, max_size())
    ),
  noalias(p, sp, q, sq)), True)

#######################

#18
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      # this is implicit in DecomposeGEPExpression
      x.is_logic(),
      y.is_logic(),
      x.offset() == 0,
      y.offset() == 0,
      noalias(x, sp, y, sq),
      sp == sq,
      w == z
    ),
  noalias(p, sp, q, sq)))

#######################

#19
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      x == y,
      sp == sq,
      #w != z
      UGE(abs(w - z), sp)
    ),
  noalias(p, sp, q, sq)))

#######################

#20
#TODO
prove(True)

#######################

#21
prove(Implies(
  And(gep(p, x, w),
      mustalias(x, max_size(), q, max_size()),
      w == 0,
      sp != 0,
      sq != 0
    ),
  mustalias(p, sp, q, sq)))

#######################

#22
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      mustalias(x, max_size(), y, max_size()),
      w == z,
      sp != 0,
      sq != 0
    ),
  mustalias(p, sp, q, sq)))

#######################

#23
prove(Implies(
  And(not_ub(p,sp),
      not_ub(q,sq),
      gep(p, x, w),
      mustalias(x, max_size(), q, max_size()),
      w > 0,
      sp != 0,
      sq != max_size(),
      ULT(w, sq)
    ),
  partialalias(p, sp, q, sq)))

#######################

#24
prove(Implies(
  And(gep(p, x, w),
      mustalias(x, max_size(), q, max_size()),
      w > 0,
      sp != max_size(),
      sq != max_size(),
      UGE(w, sq)
    ),
  noalias(p, sp, q, sq)))

#######################

#25
prove(Implies(
  And(not_ub(p,sp),
      not_ub(q,sq),
      gep(p, x, w),
      gep(q, y, z),
      mustalias(x, max_size(), y, max_size()),
      w - z > 0,
      sp != max_size(),
      sq != max_size(),
      ULT(w - z, sq),
      sp != 0
    ),
  partialalias(p, sp, q, sq)))

#######################

#26
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      mustalias(x, max_size(), y, max_size()),
      w - z > 0,
      sp != max_size(),
      sq != max_size(),
      UGE(w - z, sq)
    ),
  noalias(p, sp, q, sq)))

#######################

#27
prove(Implies(
  And(not_ub(p,sp),
      not_ub(q,sq),
      gep(p, x, w),
      mustalias(x, max_size(), q, max_size()),
      w < 0,
      sp != max_size(),
      sq != max_size(),
      sq != 0,
      ULT(-w, sp)
    ),
  partialalias(p, sp, q, sq)))

#######################

#28
prove(Implies(
  And(gep(p, x, w),
      mustalias(x, max_size(), q, max_size()),
      w < 0,
      sp != max_size(),
      sq != max_size(),
      UGE(-w, sp)
    ),
  noalias(p, sp, q, sq)))

#######################

#29
prove(Implies(
  And(not_ub(p,sp),
      not_ub(q,sq),
      gep(p, x, w),
      gep(q, y, z),
      mustalias(x, max_size(), y, max_size()),
      (w - z) < 0,
      sp != max_size(),
      sq != max_size(),
      sq != 0,
      ULT(-(w - z), sp)
    ),
  partialalias(p, sp, q, sq)))

#######################

#30
prove(Implies(
  And(gep(p, x, w),
      gep(q, y, z),
      mustalias(x, max_size(), y, max_size()),
      (w - z) < 0,
      sp != max_size(),
      sq != max_size(),
      UGE(-(w - z), sp)
    ),
  noalias(p, sp, q, sq)))

#######################

#31
prove(Implies(
  And(sp != 0,
      sq != 0,
      not_ub(p, sp),
      not_ub(q, sq),
      p == q
    ),
  mustalias(p, sp, q, sq)))

#######################

# 32: fixed version of 9
# fixed in https://reviews.llvm.org/rL317680
prove(Implies(
  And(gep(p, x, w),
      gep(q, x, z),
      x.is_logic(),
      sp == x.size(),
      sp != max_size(),
      sq != max_size(),
      not_ub(p, sp),
      not_ub(q, sq),
      sq != 0
    ),
  partialalias(p, sp, q, sq)))

#######################

# 33: another fixed version of 9
prove(Implies(
  And(gep(p, x, w),
      gep(q, x, z),
      w != z,
      x.is_logic(),
      sp == x.size(),
      sp != max_size(),
      sq != max_size(),
      q.offset() == q.size(),
      not_ub(p, sp),
      not_ub(q, sq)
    ),
  noalias(p, sp, q, sq)))

#######################

# 34: fixed version of 16
prove(Implies(
  And(gep_inbounds(p, x, w),
      w >= 0,
      noalias(x, max_size(), q, max_size())
    ),
  noalias(p, sp, q, sq)))

#######################

# 35: fixed version of 17
prove(Implies(
  And(gep_inbounds(p, x, w),
      gep_inbounds(q, y, z),
      w >= 0,
      z >= 0,
      noalias(x, max_size(), y, max_size())
    ),
  noalias(p, sp, q, sq)))

#######################

# 36: a different possible version of 18
prove(Implies(
  And(gep_inbounds(p, x, w),
      gep_inbounds(q, y, z),
      noalias(x, sp, y, sq),
      w >= 0,  # this is the fix
      sp == sq,
      w == z
    ),
  noalias(p, sp, q, sq)))

#######################
