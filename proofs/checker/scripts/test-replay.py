#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Replay the fixtures of `proofs/checker/tests/replay`.

Each directory holds a program, a stream the engine wrote for it (`ok.trace`)
and the same stream with one witness changed (`bad.trace`; `README` names the
line). The kernel must prove every `check-eq` of the program from `ok.trace`,
with no failed event and no merge without a kernel step, and fewer from
`bad.trace`: a wrong witness costs the goal that depends on it.

Usage: test-replay.py [--checker PATH]
"""

import argparse
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
TESTS = os.path.join(ROOT, "proofs", "checker", "tests", "replay")


def replay(checker, program, trace):
    p = subprocess.run([checker, "--replay", program, trace], capture_output=True, text=True,
                       timeout=60)
    k = re.search(r"kernel: \d+ steps, (\d+) of (\d+) check-eq proved", p.stdout)
    m = re.search(r"(\d+) events replayed, (\d+) failed", p.stdout)
    if not k or not m:
        return None
    return int(k.group(1)), int(k.group(2)), int(m.group(2)), "no kernel step" in p.stdout


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--checker", default=os.path.join(ROOT, "proofs", "checker", ".lake", "build",
                                                      "bin", "semper-check"))
    args = ap.parse_args()
    bad = []
    names = sorted(n for n in os.listdir(TESTS) if os.path.isdir(os.path.join(TESTS, n)))
    for name in names:
        d = os.path.join(TESTS, name)
        program = os.path.join(d, "program.egg")
        ok = replay(args.checker, program, os.path.join(d, "ok.trace"))
        wrong = replay(args.checker, program, os.path.join(d, "bad.trace"))
        if ok is None or wrong is None:
            bad.append(f"{name}: the replay did not report")
            continue
        proved, total, failed, nostep = ok
        if total == 0 or proved != total or failed or nostep:
            bad.append(f"{name}: ok.trace proves {proved} of {total}, {failed} failed events"
                       + (", a merge with no kernel step" if nostep else ""))
        if wrong[0] >= proved:
            bad.append(f"{name}: bad.trace still proves {wrong[0]} of {wrong[1]}")
        print(f"{name}: ok.trace {proved} of {total}, bad.trace {wrong[0]} of {wrong[1]}")
    if bad:
        print(f"{len(bad)} failures:")
        for b in bad:
            print(f"  {b}")
        sys.exit(1)
    print(f"{len(names)} fixtures pass")


if __name__ == "__main__":
    main()
