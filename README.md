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

Exports are Lean 4.36.0, lean4export 3.1.0. Each line is one run on one machine (`taskset -c 0`), not a repeated benchmark.

| Input | Result | Wall | User | Max RSS |
| --- | --- | --- | --- | --- |
| Init, 58547 declarations | 58547 accepted, 0 rejected | 82.660 s | 81.064 s | 1851972 KB |
| Std, 96627 declarations | 96627 accepted, 0 rejected | 559.258 s | 555.292 s | 4629724 KB |
| Lean Kernel Arena, 138 good and 92 bad files | 138/138 good accepted, 92/92 bad rejected | | | |

The Arena run used a 400 s cap per file, and was repeated on this build: 138/138 good accepted, 92/92 bad rejected. Init was also repeated on this build: 58547 accepted, 0 rejected, wall 101.319 s, user 96.098 s, max RSS 1846836 KB. Both are single samples. The 82.660 s Init figure and the Std figure are from the build before the export was read as a stream. Init's 82.660 s is a single sample next to an earlier 103.979 s run of a previous build; that gap is not a measured speedup.

Mathlib (Lean 4.36.0, lean4export 3.1.0, 721845 declarations, 6.3 GB) was exported and started. The process was killed at about 14.9 GB resident after 48867 accepts and 0 rejects, while checking `CommRingCat.instCreatesLimitRingCatForget₂RingHomCarrierCarrier`. That run did not finish.

## Limits

- Universe levels are compared syntactically, except sorts, which use a conservative comparison. A term Lean's kernel accepts can be rejected here.
- The definitional-equality cache is lossy. Weak-head normal forms are not reused across different binder contexts.
- Every expression from the export stays in memory. The file itself is read a line at a time. Std peaked near 4.5 GB. Mathlib did not fit in a 15 GB limit.
