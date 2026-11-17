#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Write the replay stream of every regression program, replay it, and have
the kernel check the steps the replay emits.

For each `.egg` program the regression tests run and expect `ok` (the files
`egraph/tests/egg_tests.rs` registers, the CBMC and conformance corpora it and
`egraph/tests/conform.rs` walk, and the book examples, the cost-model ones with
machine types as `egraph/tests/cost_models.rs` runs them), the engine runs with
`--proofs --trace` under the program's `TYPES` and `UNION_BY` directives, and
`semper-check --replay` replays the stream (`proofs/checker/REPLAY.md`). The
replay emits kernel steps; the kernel checks them, and `replay_sound`
(`SemperCheck/ReplaySound.lean`) covers the `check-eq` it accepts. The run
fails when:

- the engine fails on a program that expects `ok`, or the engine or the replay
  exceeds its time limit where the baseline does not record that it does;
- the replay does not finish, or the kernel rejects the node table;
- a program proves fewer `check-eq` through the kernel than
  `proofs/checker/coverage.tsv` records.

An event whose check fails, a merge with no kernel step and a `check-eq` not
proved are counted and listed by cause; they are not failures: the replayer
cannot yet justify every merge (see `proofs/checker/README.md`). `--update`
rewrites the baseline after a change that proves more; a row's note, its fifth
column, is kept.

`--assume` sets `SEMPER_REPLAY_ASSUME`: the replayer joins the classes of the
merges it does not check, which separates a check that fails by itself from
one that fails because an earlier merge was not applied. The kernel count does
not change: such a merge has no kernel step.

Usage: check-replay.py [--engine PATH] [--checker PATH] [--out DIR] [--jobs N]
                       [--timeout SECONDS] [--memory MB] [--assume] [--update]
                       [--json FILE] [FILE...]
"""

import argparse
import collections
import concurrent.futures
import json
import os
import re
import resource
import subprocess
import sys
import tempfile
import time

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
    cost = path.startswith(COST_MODELS + "/")
    trace = os.path.join(args.out, path.replace("/", "__") + ".trace")
    cmd = [args.engine, "--proofs", "--trace", trace, "--types",
           "machine" if cost else d["TYPES"]]
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
    size = os.path.getsize(trace)
    start = time.time()
    try:
        # `time` reports the replay's peak memory, where it is installed.
        timed = ["/usr/bin/time", "-l" if sys.platform == "darwin" else "-v"] \
            if os.path.exists("/usr/bin/time") else []
        p = subprocess.run(timed + [args.checker, "--replay", os.path.join(ROOT, path), trace],
                           capture_output=True, text=True, timeout=args.timeout)
    except subprocess.TimeoutExpired:
        os.remove(trace)
        return path, {"status": "replay-timeout", "bytes": size}
    secs = time.time() - start
    os.remove(trace)
    if "program:" in p.stderr:
        return path, {"status": "unread", "bytes": size}
    if "node table is rejected" in p.stdout:
        return path, {"status": "rejected", "bytes": size}
    m = re.search(r"(\d+) events replayed, (\d+) failed, (\d+) unchecked; "
                  r"(\d+) of (\d+) check-eq proved", p.stdout)
    k = re.search(r"kernel: (\d+) steps, (\d+) of \d+ check-eq proved", p.stdout)
    if not m or not k:
        return path, {"status": "replay-error",
                      "detail": (p.stdout + p.stderr).strip().splitlines()[-2:]}
    events, failed, unchecked, joined, total = map(int, m.groups())
    rss = re.search(r"(\d+)\s+maximum resident set size", p.stderr)
    if rss:
        rss_mb = int(rss.group(1)) / 1e6
    else:
        rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", p.stderr)
        rss_mb = int(rss.group(1)) / 1e3 if rss else 0.0

    def by(label):
        return {c: int(n) for n, c in re.findall(label + r": (\d+) (.+)", p.stdout)}
    return path, {
        "status": "replayed", "events": events, "failed": failed, "unchecked": unchecked,
        "joined": joined, "total": total, "steps": int(k.group(1)), "proved": int(k.group(2)),
        "bytes": size, "secs": secs, "rss_mb": rss_mb,
        "failed_by": by("failed"), "unchecked_by": by("unchecked"),
        "nostep_by": by("no kernel step"),
    }


def read_baseline():
    base = {}
    if os.path.exists(BASELINE):
        with open(BASELINE, encoding="utf-8") as f:
            for line in f:
                if line.startswith("#") or not line.strip():
                    continue
                cols = line.rstrip("\n").split("\t")
                base[cols[0]] = (int(cols[1]), int(cols[2]), cols[3],
                                 cols[4] if len(cols) > 4 else "")
    return base


def write_baseline(results, base):
    with open(BASELINE, "w", encoding="utf-8") as f:
        f.write("# Written by proofs/checker/scripts/check-replay.py --update.\n")
        f.write("# program\tcheck-eq proved by the kernel\tcheck-eq read\tstatus\tnote\n")
        for path in sorted(results):
            r = results[path]
            note = base[path][3] if path in base else ""
            f.write(f"{path}\t{r.get('proved', 0)}\t{r.get('total', 0)}\t{r['status']}"
                    + (f"\t{note}" if note else "") + "\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--engine", default=os.path.join(ROOT, "target", "release",
                                                     "semi-persistent"))
    ap.add_argument("--checker", default=os.path.join(ROOT, "proofs", "checker", ".lake",
                                                      "build", "bin", "semper-check"))
    ap.add_argument("--out", default=None, help="directory for the streams")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--timeout", type=int, default=60, help="seconds per run")
    ap.add_argument("--memory", type=int, default=4000, help="MB per engine run (Linux)")
    ap.add_argument("--assume", action="store_true",
                    help="measurement: join the classes of the merges the replayer does not check")
    ap.add_argument("--update", action="store_true", help="rewrite coverage.tsv")
    ap.add_argument("--json", default=None, help="write the per-program results here")
    ap.add_argument("files", nargs="*", help="programs, relative to the repository root")
    args = ap.parse_args()
    args.out = args.out or tempfile.mkdtemp(prefix="semper-replay-")
    os.makedirs(args.out, exist_ok=True)
    if args.assume:
        os.environ["SEMPER_REPLAY_ASSUME"] = "1"

    results = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for path, r in ex.map(lambda p: check_one(p, args), args.files or programs()):
            results[path] = r
    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump(results, f)

    base = read_baseline()
    failures = []
    for path, r in sorted(results.items()):
        st = r["status"]
        known = path in base and base[path][2] == st
        if st in ("engine-timeout", "replay-timeout") and known:
            continue
        if st in ("engine-error", "engine-timeout", "replay-timeout", "replay-error", "rejected"):
            failures.append(f"{path}: {st} {' | '.join(r.get('detail', []))}")
        elif path in base and r.get("proved", 0) < base[path][0]:
            failures.append(f"{path}: proves {r.get('proved', 0)} check-eq, baseline "
                            f"{base[path][0]}")

    statuses = collections.Counter(r["status"] for r in results.values())
    done = [r for r in results.values() if r["status"] == "replayed"]
    with_goal = [r for r in done if r["total"]]
    total = sum(r["total"] for r in done)
    print(f"{len(results)} programs: " + ", ".join(f"{n} {s}" for s, n in sorted(statuses.items())))
    if args.assume:
        print("measurement mode: the classes of unchecked merges are joined")
    print(f"{sum(r['proved'] for r in done)} of {total} check-eq proved by the kernel "
          f"({sum(r['steps'] for r in done)} steps); "
          f"{sum(1 for r in with_goal if r['proved'] == r['total'])} of {len(with_goal)} programs "
          "with a check-eq fully proved")
    print(f"{sum(r['joined'] for r in done)} of {total} check-eq joined by the replay; "
          f"{sum(r['events'] for r in done)} events, {sum(r['failed'] for r in done)} failed, "
          f"{sum(r['unchecked'] for r in done)} unchecked")
    if done:
        print(f"streams: {sum(r['bytes'] for r in done)} bytes, largest "
              f"{max(r['bytes'] for r in done)}; slowest replay "
              f"{max(r['secs'] for r in done):.2f} s; largest replay "
              f"{max(r['rss_mb'] for r in done):.0f} MB")
    for title, key in (("failed events by cause:", "failed_by"),
                       ("unchecked merges by kind:", "unchecked_by"),
                       ("merges with no kernel step, by line kind:", "nostep_by")):
        count = collections.Counter()
        for r in done:
            count.update(r[key])
        if count:
            print(title)
            for what, n in count.most_common():
                print(f"  {n:8d}  {what}")
    if args.update:
        write_baseline(results, base)
        print(f"wrote {os.path.relpath(BASELINE, ROOT)}")
    if failures:
        print(f"{len(failures)} failures:")
        for f in failures:
            print(f"  {f}")
        sys.exit(1)


if __name__ == "__main__":
    main()
