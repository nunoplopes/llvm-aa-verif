Verification of LLVM's Alias Analysis Proof Rules
=================================================

This repo contains a Python script that verifies LLVM alias analysis (AA)
proof rules automatically. It uses Z3Py to discharge the proof obligations.
The script formalizes the AA results of LLVM (no alias, partial alias,
must alias, may alias).
The formalization of the LLVM memory is based on the OOPSLA'18 paper.

The script currently attempts to prove 2 things:
 - Relationships between AA's lattice values (e.g., no-alias implies
   not must-alias)
 - Most proof rules of BasicAA

Limitations:
 - Address spaces are not supported (assumed 0 always).
 - Const memory, arguments, locally allocated objects not supported.
 - Missing proofs that spec of AA results is meaningful (e.g., if
   p,q must-alias, then load p == load q if memories are equal).
