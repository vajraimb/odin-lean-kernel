# odin-lean-kernel

Proof-of-concept Lean 4 kernel type checker written in Odin. Reads lean4export NDJSON (format 3.1.0).

Supports: dependent types, delta/iota/eta/proof irrelevance, Nat literal GMP shortcuts, Quot, inductive types (mutual, indexed, reflexive, nested) with recursor regeneration.

Build: `odin build kernel.odin -file -o:speed -out:kernel`
Run: `ulimit -s unlimited; ./kernel file.ndjson [-v]`

Results: Poc.lean 121/121, Init.Prelude 1840/1840, Init.Core 3480/3480.

Limits: no string literal expansion, no Quot statement check, conservative level reasoning, not yet run against Lean Kernel Arena.
