# odin-lean-kernel

A Lean 4 kernel type checker written in Odin. It reads one [lean4export](https://github.com/leanprover/lean4export) NDJSON file (format 3.1.0) and checks every declaration. It does not elaborate, compile, or run Lean source.

## Build

Tested with Odin `dev-2026-11-nightly:9a69916` (2026-11-03).

```
odin build kernel.odin -file -o:speed -out:kernel
```

## Run

```
ulimit -s unlimited
./kernel file.ndjson
```

Exit status: `0` if every declaration is accepted, `1` if any is rejected, `2` if the file cannot be read or the arguments are wrong. A second argument prints each declaration name as it is checked.

The checker uses a deep call stack, so `ulimit -s unlimited` is required.

## What has been checked

Exports are Lean 4.36.0, lean4export 3.1.0. Each line is one run of this build on one core (`taskset -c 0`) of a 4-core machine with a 15 GB memory limit, not a repeated benchmark.

| Input | Result | Wall | User | Max RSS |
| --- | --- | --- | --- | --- |
| Init, 58547 declarations | 58547 accepted, 0 rejected | 88.620 s | 85.070 s | 1753068 KB |
| Std, 96627 declarations | 96627 accepted, 0 rejected | 494.964 s | 483.292 s | 4408236 KB |
| Mathlib, 721845 declarations, 6.3 GB | 721845 accepted, 0 rejected | 7050.530 s | 6904.301 s | 12774036 KB |
| Lean Kernel Arena, 138 good and 92 bad files | 138/138 good accepted, 92/92 bad rejected | | | |

Init ran with nothing else on the machine. Std ran next to the Arena run, which used the other cores and a 400 s cap per file. The Mathlib run is from the commit before the last one on this build (the last one only changes the layout of an expression node) and shared the machine with Init timing runs on another core.

Against the previous build, Init was timed three times each, alternating, while another job held a different core: user time 89.78 s before (sd 0.89) and 94.47 s now (sd 2.16). Init is about 5% slower. Std and Mathlib have no such comparison; their figures are single samples.

The previous build did not finish Mathlib: it was killed at about 14.9 GB after 48867 accepts, inside `CommRingCat.instCreatesLimitRingCatForget₂RingHomCarrierCarrier`. On an export of that declaration and its 2247 dependencies, the previous build had not finished after 150 s; this build checks all of them in 4.2 s.

## Tests

```
python3 tests/run.py ./kernel
```

`tests/accept` holds exports that must be accepted and `tests/reject` exports that must be rejected. Each reject file ends in a false theorem, such as `Eq' T.b T.a` for a type `T` with two constructors, that earlier builds accepted: an equality proved under one set of binders was reused under another. `tests/accept/quot-lift-held-in-field` is a Lean export that earlier builds rejected.

## Limits

- Universe levels are compared syntactically, except sorts, which use a conservative comparison. A term Lean's kernel accepts can be rejected here.
- The definitional-equality cache is lossy: an entry can be overwritten and the work done again.
- Every expression from the export stays in memory. The file itself is read a line at a time. Std peaked near 4.4 GB and Mathlib near 12.8 GB, so Mathlib needs a machine with more than that free.
- An export of a gigabyte or more gets its expression table reserved from the file size. `STORE_CAP=n` overrides the number of expressions reserved.
