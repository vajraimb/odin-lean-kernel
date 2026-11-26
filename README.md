# odin-lean-kernel

Proof-of-concept Lean 4 kernel type checker written in Odin. Reads lean4export NDJSON (format 3.1.0).

Supports: dependent types, delta/iota/eta/proof irrelevance, Nat literal GMP shortcuts, Quot, inductive types (mutual, indexed, reflexive, nested) with recursor regeneration.

Build: `odin build kernel.odin -file -o:speed -out:kernel`
Run: `ulimit -s unlimited; ./kernel file.ndjson [-v]`

Results: Poc.lean 121/121, Init.Prelude 1840/1840, Init.Core 3480/3480.
Full Init (6,495,296-line export, 332 MB, Lean 4.36.0): 58547 accepted, 0 rejected, wall 103.979 s, user 102.500 s, peak RSS 1872428 KB.

Arena contract: exit 0 accepts, exit 1 rejects, exit 3 is a checker error. Exit 2 is reserved for an intentional decline; this checker does not decline.

Checked against the Lean Kernel Arena suite (Lean 4.36.0, lean4export 3.1.0): the small tarball is 138/138 accept and 92/92 reject. `Std` (`import Std`, 10,123,010 lines, 532 MB) is 96589 accepted and 38 rejected, wall 347.338 s, user 341.928 s, peak RSS 4531656 KB. The only root rejection is `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq._unary`, which hits the per-declaration expression cap; the other 37 are unknown-constant cascades. Mathlib has not been run.
