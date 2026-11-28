#!/usr/bin/env python3
"""Regression exports for the kernel's own caches.

tests/accept/*.ndjson must exit 0, tests/reject/*.ndjson must exit 1.

Each reject file ends with a false theorem that a kernel accepts only if it
reuses an equality cached under other binders. The accept file of the same
name is the Lean export it was edited from.

An accept file without a reject twin is a Lean export this kernel once
rejected: quot-lift-held-in-field has `Quot.lift f h` stored in a structure
field and applied to a `Quot.mk` after projection.

usage: tests/run.py <kernel>
"""
import glob, os, subprocess, sys

kernel = sys.argv[1] if len(sys.argv) > 1 else "./kernel"
here = os.path.dirname(os.path.abspath(__file__))
bad = 0
for want, sub in ((0, "accept"), (1, "reject")):
    for f in sorted(glob.glob(os.path.join(here, sub, "*.ndjson"))):
        p = subprocess.run(f"ulimit -s unlimited; {kernel} {f}", shell=True, capture_output=True, text=True)
        ok = p.returncode == want
        bad += not ok
        print(("ok   " if ok else "WRONG"), sub, os.path.basename(f), "exit", p.returncode)
print("failures:", bad)
sys.exit(1 if bad else 0)
