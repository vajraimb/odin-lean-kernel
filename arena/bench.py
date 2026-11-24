#!/usr/bin/env python3
"""User-CPU timings for a fixed set of Lean Kernel Arena files.

The ndjson files are not in this repo. Download lean-arena-tests.tar.gz from
https://arena.lean-lang.org/ and point DIR at the extracted tree (the directory
that contains good/ and bad/).

Measurement: each file is run REPEATS times (default 5), pinned to CPU 0, with
`ulimit -s unlimited`. The number reported is ru_utime of the child (user CPU,
not wall clock). mean / sample stdev / min / max are printed. A non-zero exit
status is recorded and the run still counts, so a crash is visible.

Usage: python3 bench.py KERNEL DIR [repeats]
"""
import glob, os, resource, statistics, subprocess, sys

FILES = [
    "good/perf/let-ladder.ndjson",
    "good/perf/beta-ladder.ndjson",
    "good/perf/app-lam.ndjson",
    "good/perf/magma-list-pair-n7.ndjson",
    "good/perf/magma-list-deep-n21.ndjson",
    "good/perf/shared-subterm.ndjson",
    "good/perf/discarded-argument.ndjson",
    "good/perf/church-numerals.ndjson",
]

def one(kernel, path):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    p = subprocess.run(
        f"ulimit -s unlimited; taskset -c 0 {kernel} {path}",
        shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    return after.ru_utime - before.ru_utime, p.returncode

def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(2)
    kernel, root = sys.argv[1], sys.argv[2]
    repeats = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    kernel = os.path.abspath(kernel)
    print(f"kernel {kernel}  repeats {repeats}  metric ru_utime  pin cpu 0")
    for rel in FILES:
        hits = glob.glob(os.path.join(root, rel))
        if not hits:
            print(f"{rel}  MISSING")
            continue
        path = hits[0]
        xs, rcs = [], []
        for _ in range(repeats):
            u, rc = one(kernel, path)
            xs.append(u)
            rcs.append(rc)
        mean = statistics.mean(xs)
        sd = statistics.stdev(xs) if len(xs) > 1 else 0.0
        print(f"{rel}  n={repeats}  mean {mean:.3f}  sd {sd:.3f}  min {min(xs):.3f}  max {max(xs):.3f}  rc {rcs}")

if __name__ == "__main__":
    main()
