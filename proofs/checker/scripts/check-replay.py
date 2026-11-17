#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Write the replay stream of every regression program and replay it.

For each program `check-certificates.py` covers, the engine runs with
`--proofs --trace` and `semper-check --replay` replays the stream against the
program (`proofs/checker/REPLAY.md`). The script reports, over all programs, the
`check-eq` proved, the events that failed by cause, the merges the replayer does
not check yet by kind, the stream sizes, and the replay time and memory.

The replayer has no soundness theorem yet: the counts measure the design.

`--assume` sets `SEMPER_REPLAY_ASSUME`: the replayer applies the merges it does
not check. That separates a check that fails by itself from one that fails
because an earlier merge was not applied; a goal it reports is not proved.

Usage: check-replay.py [--engine PATH] [--checker PATH] [--out DIR] [--jobs N]
                       [--timeout SECONDS] [--assume] [--json FILE] [FILE...]
"""

import argparse
import collections
import concurrent.futures
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "check_certificates", os.path.join(HERE, "check-certificates.py"))
cc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cc)


def check_one(path, args):
    d = cc.directives(path)
    if d["EXPECT"] != "ok":
        return path, {"status": "skipped"}
    cost = path.startswith(cc.COST_MODELS + "/")
    trace = os.path.join(args.out, path.replace("/", "__") + ".trace")
    cmd = [args.engine, "--proofs", "--trace", trace, "--types",
           "machine" if cost else d["TYPES"]]
    if d["UNION_BY"]:
        cmd += ["--union-by", d["UNION_BY"]]
    cmd.append(os.path.join(cc.ROOT, path))
    code, out = cc.run(cmd, args.timeout, args.memory,
                       cwd=os.path.join(cc.ROOT, cc.COST_MODELS) if cost else None)
    if code is None:
        return path, {"status": "engine-timeout"}
    if code != 0:
        return path, {"status": "engine-error", "detail": out.strip().splitlines()[-1:]}
    size = os.path.getsize(trace)
    start = time.time()
    try:
        p = subprocess.run(["/usr/bin/time", "-l" if sys.platform == "darwin" else "-v",
                            args.checker, "--replay", os.path.join(cc.ROOT, path), trace],
                           capture_output=True, text=True, timeout=args.timeout)
    except subprocess.TimeoutExpired:
        os.remove(trace)
        return path, {"status": "replay-timeout", "bytes": size}
    secs = time.time() - start
    os.remove(trace)
    if "program:" in p.stderr:
        return path, {"status": "unread", "bytes": size}
    m = re.search(r"(\d+) events replayed, (\d+) failed, (\d+) unchecked; "
                  r"(\d+) of (\d+) check-eq proved", p.stdout)
    if not m:
        return path, {"status": "replay-error",
                      "detail": (p.stdout + p.stderr).strip().splitlines()[-2:]}
    events, failed, unchecked, proved, total = map(int, m.groups())
    k = re.search(r"kernel: (\d+) steps, (\d+) of \d+ check-eq proved", p.stdout)
    steps, kernel = (int(k.group(1)), int(k.group(2))) if k else (0, 0)
    rss = re.search(r"(\d+)\s+maximum resident set size", p.stderr)
    if rss:
        rss_mb = int(rss.group(1)) / 1e6
    else:
        rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", p.stderr)
        rss_mb = int(rss.group(1)) / 1e3 if rss else 0.0
    return path, {
        "status": "replayed", "events": events, "failed": failed, "unchecked": unchecked,
        "proved": proved, "total": total, "kernel": kernel, "steps": steps,
        "rejected": "node table is rejected" in p.stdout, "bytes": size, "secs": secs, "rss_mb": rss_mb,
        "failed_by": {c: int(n) for n, c in re.findall(r"failed: (\d+) (.+)", p.stdout)},
        "unchecked_by": {c: int(n) for n, c in re.findall(r"unchecked: (\d+) (.+)", p.stdout)},
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--engine", default=os.path.join(cc.ROOT, "target", "release",
                                                     "semi-persistent"))
    ap.add_argument("--checker", default=os.path.join(cc.ROOT, "proofs", "checker", ".lake",
                                                      "build", "bin", "semper-check"))
    ap.add_argument("--out", default=None, help="directory for the streams")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--timeout", type=int, default=60, help="seconds per run")
    ap.add_argument("--memory", type=int, default=4000, help="MB per engine run (Linux)")
    ap.add_argument("--assume", action="store_true",
                    help="measurement: apply the merges the replayer does not check")
    ap.add_argument("--json", default=None, help="write the per-program results here")
    ap.add_argument("files", nargs="*", help="programs, relative to the repository root")
    args = ap.parse_args()
    args.out = args.out or tempfile.mkdtemp(prefix="semper-replay-")
    os.makedirs(args.out, exist_ok=True)
    if args.assume:
        os.environ["SEMPER_REPLAY_ASSUME"] = "1"

    results = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for path, r in ex.map(lambda p: check_one(p, args), args.files or cc.programs()):
            results[path] = r
    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump(results, f)

    statuses = collections.Counter(r["status"] for r in results.values())
    done = [r for r in results.values() if r["status"] == "replayed"]
    print(f"{len(results)} programs: " + ", ".join(f"{n} {s}" for s, n in sorted(statuses.items())))
    if args.assume:
        print("measurement mode: unchecked merges applied; the counts below are not proofs")
    with_goal = [r for r in done if r["total"]]
    print(f"kernel (covered by goal_sound): {sum(r['kernel'] for r in done)} of "
          f"{sum(r['total'] for r in done)} check-eq proved, "
          f"{sum(1 for r in with_goal if r['kernel'] == r['total'])} of {len(with_goal)} programs "
          f"fully, {sum(r['steps'] for r in done)} steps, "
          f"{sum(1 for r in done if r['rejected'])} node tables rejected")
    print(f"replay (unproved): {sum(r['proved'] for r in done)} of {sum(r['total'] for r in done)} check-eq; "
          f"{sum(1 for r in with_goal if r['proved'] == r['total'])} of {len(with_goal)} programs "
          "with a check-eq fully proved")
    print(f"{sum(r['events'] for r in done)} events, {sum(r['failed'] for r in done)} failed, "
          f"{sum(r['unchecked'] for r in done)} unchecked")
    if done:
        print(f"streams: {sum(r['bytes'] for r in done)} bytes, largest "
              f"{max(r['bytes'] for r in done)}; slowest replay "
              f"{max(r['secs'] for r in done):.2f} s; largest replay "
              f"{max(r['rss_mb'] for r in done):.0f} MB")
    failed_by, unchecked_by = collections.Counter(), collections.Counter()
    for r in done:
        failed_by.update(r["failed_by"])
        unchecked_by.update(r["unchecked_by"])
    if failed_by:
        print("failed events by cause:")
        for cause, n in failed_by.most_common():
            print(f"  {n:8d}  {cause}")
    if unchecked_by:
        print("unchecked merges by kind:")
        for kind, n in unchecked_by.most_common():
            print(f"  {n:8d}  {kind}")
    bad = [(p, r) for p, r in sorted(results.items())
           if r["status"] in ("engine-error", "engine-timeout", "replay-error", "replay-timeout")]
    for p, r in bad:
        print(f"{r['status']}: {p} {' | '.join(r.get('detail', []))}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
