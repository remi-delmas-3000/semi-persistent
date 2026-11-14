#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Write an equality certificate for every regression program and check it.

For each `.egg` program the regression tests run and expect `ok` (the files
`egraph/tests/egg_tests.rs` registers, the CBMC and conformance corpora it and
`egraph/tests/conform.rs` walk, and the book examples, the cost-model ones with machine
types as `egraph/tests/cost_models.rs` runs them), the engine runs with
`--proofs --cert` under the program's `TYPES` and `UNION_BY` directives, and
`semper-check` checks the certificate against the program. The run fails when:

- the engine fails on a program that expects `ok`, or exceeds its time or memory limit
  where the baseline does not record that it does (proof mode is slower than the
  regression tests on some search benchmarks);
- a certificate does not parse, or the checker rejects it (an ill-sorted node, a child
  after its parent);
- a step of a certificate does not check, which is a bug in the writer
  (`egraph/src/egraph/cert.rs`) or in the reader the writer mirrors;
- a program proves fewer `check-eq` than `proofs/checker/coverage.tsv` records.

A `check-eq` the certificate does not prove is not a failure: the writer cannot yet
express every explanation (see `proofs/checker/README.md`). `--update` rewrites the
baseline after a change that proves more.

Usage: check-certificates.py [--engine PATH] [--checker PATH] [--out DIR] [--jobs N]
                             [--timeout SECONDS] [--memory MB] [--update] [FILE...]
"""

import argparse
import concurrent.futures
import os
import re
import resource
import subprocess
import sys
import tempfile
from collections import Counter

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
BASELINE = os.path.join(ROOT, "proofs", "checker", "coverage.tsv")
# The directories a test walks: every `.egg` file in them is a regression program.
WALKED = [
    "egraph/tests/egg/cbmc",
    "egraph/tests/egg/conform",
    "egraph/tests/egg/conform-cc",
    "egraph/tests/egg/conform-cc-cert",
    "egraph/tests/egg/conform-flatten",
    "egraph/tests/egg/conform-rounds",
    "doc/book/examples",
]
# Run with machine types from their own directory (`cost_models.rs`).
COST_MODELS = "doc/book/examples/cost-models"


def walk(d):
    full = os.path.join(ROOT, d)
    return [os.path.join(d, n) for n in sorted(os.listdir(full)) if n.endswith(".egg")]


def registered():
    """The files `egg_tests.rs` registers under `tests/egg/`."""
    with open(os.path.join(ROOT, "egraph", "tests", "egg_tests.rs"), encoding="utf-8") as f:
        names = sorted(set(re.findall(r'"([A-Za-z0-9_./-]+\.egg)"', f.read())))
    return [os.path.join("egraph/tests/egg", n) for n in names
            if os.path.exists(os.path.join(ROOT, "egraph/tests/egg", n))]


def installed(tool):
    return any(os.access(os.path.join(p, tool), os.X_OK)
               for p in os.environ.get("PATH", "").split(os.pathsep))


def programs():
    out = registered()
    for d in WALKED:
        out += walk(d)
    for p in walk(COST_MODELS):
        with open(os.path.join(ROOT, p), encoding="utf-8") as f:
            src = f.read()
        if ('(asp "clingo")' in src and not installed("clingo")) or \
                ('(minizinc "' in src and not installed("minizinc")):
            continue
        out.append(p)
    return out


def directives(path):
    """The directives of a program's first eight lines (`egg_tests.rs`)."""
    d = {"EXPECT": "ok", "TYPES": "bignum", "UNION_BY": None}
    with open(os.path.join(ROOT, path), encoding="utf-8") as f:
        for _, line in zip(range(8), f):
            m = re.match(r"\s*;; (EXPECT|TYPES|UNION_BY):\s*(\S+)", line)
            if m:
                d[m.group(1)] = m.group(2)
    return d


def limit(memory_mb):
    def apply():
        if memory_mb:
            nbytes = memory_mb * 1024 * 1024
            try:
                resource.setrlimit(resource.RLIMIT_AS, (nbytes, nbytes))
            except (ValueError, OSError):
                pass  # macOS does not enforce RLIMIT_AS; the timeout still holds.
    return apply


def run(cmd, timeout, memory_mb, cwd=None):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout,
                           preexec_fn=limit(memory_mb), cwd=cwd)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return None, ""


def check_one(path, args):
    d = directives(path)
    if d["EXPECT"] != "ok":
        return path, {"status": "skipped"}
    cert = os.path.join(args.out, path.replace("/", "__") + ".cert")
    cost = path.startswith(COST_MODELS + "/")
    types = "machine" if cost else d["TYPES"]
    cmd = [args.engine, "--proofs", "--cert", cert, "--types", types]
    if d["UNION_BY"]:
        cmd += ["--union-by", d["UNION_BY"]]
    cmd.append(os.path.join(ROOT, path))
    code, out = run(cmd, args.timeout, args.memory,
                    cwd=os.path.join(ROOT, COST_MODELS) if cost else None)
    if code is None:
        return path, {"status": "engine-timeout"}
    if code != 0:
        # Past the memory limit the engine aborts its allocation; that is a resource
        # outcome like a timeout, not an engine failure.
        if "memory allocation" in out or code < 0:
            return path, {"status": "engine-timeout", "detail": ["memory limit"]}
        return path, {"status": "engine-error", "detail": out.strip().splitlines()[-1:]}
    unsupported = Counter()
    for m in re.finditer(r"unsupported: (.+): (\d+)", out):
        unsupported[m.group(1)] += int(m.group(2))
    code, out = run([args.checker, os.path.join(ROOT, path), cert], args.timeout, args.memory)
    if not args.keep:
        try:
            os.remove(cert)
        except OSError:
            pass
    if code is None:
        return path, {"status": "checker-timeout"}
    r = {"unsupported": unsupported}
    if out.startswith("program:"):
        r.update(status="unread", detail=[out.strip()])
        return path, r
    if out.startswith("certificate:") or "certificate rejected" in out:
        r.update(status="rejected", detail=[out.strip()])
        return path, r
    m = re.search(r"(\d+) steps checked, (\d+) failed; (\d+) of (\d+) check-eq proved", out)
    if not m:
        r.update(status="checker-error", detail=out.strip().splitlines()[-2:])
        return path, r
    steps, failed, proved, total = map(int, m.groups())
    r.update(status="step-failed" if failed else "checked", steps=steps, failed=failed,
             proved=proved, total=total)
    if failed:
        r["detail"] = [l for l in out.splitlines() if "fails:" in l][:3]
    return path, r


def read_baseline():
    base = {}
    if os.path.exists(BASELINE):
        with open(BASELINE, encoding="utf-8") as f:
            for line in f:
                if line.startswith("#") or not line.strip():
                    continue
                path, proved, total, status = line.rstrip("\n").split("\t")
                base[path] = (int(proved), int(total), status)
    return base


def write_baseline(results):
    with open(BASELINE, "w", encoding="utf-8") as f:
        f.write("# Written by proofs/checker/scripts/check-certificates.py --update.\n")
        f.write("# program\tcheck-eq proved\tcheck-eq read\tstatus\n")
        for path in sorted(results):
            r = results[path]
            f.write(f"{path}\t{r.get('proved', 0)}\t{r.get('total', 0)}\t{r['status']}\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--engine", default=os.path.join(ROOT, "target", "release", "semi-persistent"))
    ap.add_argument("--checker",
                    default=os.path.join(ROOT, "proofs", "checker", ".lake", "build", "bin",
                                         "semper-check"))
    ap.add_argument("--out", default=None, help="directory for the certificates")
    ap.add_argument("--keep", action="store_true", help="keep the certificates")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--timeout", type=int, default=60, help="seconds per run")
    ap.add_argument("--memory", type=int, default=4000, help="MB per run (Linux)")
    ap.add_argument("--update", action="store_true", help="rewrite coverage.tsv")
    ap.add_argument("files", nargs="*", help="programs, relative to the repository root")
    args = ap.parse_args()
    args.out = args.out or tempfile.mkdtemp(prefix="semper-certs-")
    os.makedirs(args.out, exist_ok=True)

    files = args.files or programs()
    results = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for path, r in ex.map(lambda p: check_one(p, args), files):
            results[path] = r

    base = read_baseline()
    failures = []
    for path, r in sorted(results.items()):
        st = r["status"]
        known = path in base and base[path][2] == st
        if st in ("engine-timeout", "checker-timeout") and known:
            continue
        if st in ("engine-error", "engine-timeout", "checker-timeout", "checker-error",
                  "rejected", "step-failed"):
            failures.append(f"{path}: {st} {' | '.join(r.get('detail', []))}")
        elif path in base and r.get("proved", 0) < base[path][0]:
            failures.append(f"{path}: proves {r.get('proved', 0)} check-eq, baseline "
                            f"{base[path][0]}")

    statuses = Counter(r["status"] for r in results.values())
    proved = sum(r.get("proved", 0) for r in results.values())
    total = sum(r.get("total", 0) for r in results.values())
    steps = sum(r.get("steps", 0) for r in results.values())
    full = sum(1 for r in results.values() if r.get("total", 0) > 0 and r["proved"] == r["total"])
    some = sum(1 for r in results.values() if r.get("total", 0) > 0)
    unsupported = Counter()
    for r in results.values():
        unsupported.update(r.get("unsupported", {}))

    print(f"{len(results)} programs: " + ", ".join(f"{n} {s}" for s, n in sorted(statuses.items())))
    print(f"{steps} steps checked; {proved} of {total} check-eq proved; "
          f"{full} of {some} programs with a check-eq fully proved")
    if unsupported:
        print("edges the writer cannot express:")
        for why, n in unsupported.most_common():
            print(f"  {n:6d}  {why}")
    if args.update:
        write_baseline(results)
        print(f"wrote {os.path.relpath(BASELINE, ROOT)}")
    if failures:
        print(f"{len(failures)} failures:")
        for f in failures:
            print(f"  {f}")
        sys.exit(1)


if __name__ == "__main__":
    main()
