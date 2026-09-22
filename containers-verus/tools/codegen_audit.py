#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Codegen audit of Criterion bench closures in a bench binary (macOS arm64).

For every `Bencher::iter` instantiation, disassemble it and report:
  instr           total instructions in the closure
  calls_cv        out-of-line calls into semi_persistent_containers_verus (inlining failures)
  carried         loops whose body stores to and reloads the same stack slot
                  (a loop variable kept in memory across iterations)
  dup_loads       stack slots loaded more than once inside one loop body without an
                  intervening store (redundant reloads, alias-analysis failures)
  panics          refuse / unwrap_failed / panic / expect call sites reachable in the closure
  inner           size of the innermost (smallest) loop with >= 8 instructions
Usage: codegen_audit.py <bench-binary> [name-filter]
"""
import re, subprocess, sys, collections

binary = sys.argv[1]
flt = sys.argv[2] if len(sys.argv) > 2 else ""

def v0_idents(sym):
    """Scan a v0-mangled symbol: every <len><ident> pair yields ident (exact length)."""
    sym = re.sub(r'Cs[A-Za-z0-9]{8,14}_', 'C', sym)   # drop crate disambiguator hashes
    out = []; i = 0; n = len(sym)
    while i < n:
        if sym[i].isdigit() and sym[i] != '0':
            j = i
            while j < n and sym[j].isdigit(): j += 1
            ln = int(sym[i:j]); k = j
            if k < n and sym[k] == '_': k += 1
            if k + ln <= n and re.fullmatch(r'[A-Za-z0-9_]+', sym[k:k+ln] or ' '):
                out.append(sym[k:k+ln]); i = k + ln; continue
        i += 1
    return out

nm = subprocess.run(['nm', binary], capture_output=True, text=True).stdout.split('\n')
closures = []
for line in nm:
    parts = line.split()
    if len(parts) < 3: continue
    sym = parts[2]
    ids = v0_idents(sym) if ('Bencher4iter' in sym or 'probe_' in sym) else []
    probe = next((i for i in ids if i.startswith('probe_')), None)
    if probe:
        k = ids.index(probe)
        mod = ids[k-1] if k > 0 else ''
        closures.append((f"{mod}::{probe}", 0, sym)); continue
    if 'Bencher4iter' in sym and 'bench' in sym:
        # bench function name: identifier starting with 'bench_'
        fn = next((i for i in ids if i.startswith('bench_')), None)
        if not fn: continue
        # closure ordinal: pattern like 'bench_xxx00' (first) / 'bench_xxxs_00' (second) / 's0_00' ...
        m = re.search(re.escape(fn) + r'(s[0-9a-z]*_)?00', sym)
        ordinal = 0
        if m and m.group(1):
            o = m.group(1)[1:-1]
            ordinal = 1 if o == '' else int(o, 36) + 2
        closures.append((fn, ordinal, sym))
closures.sort()

def disasm(sym):
    out = subprocess.run(['objdump', '-d', f'--disassemble-symbols={sym}', binary], capture_output=True, text=True).stdout
    ins = []
    for l in out.split('\n'):
        m = re.match(r'\s*([0-9a-f]+):\s+[0-9a-f ]+\s+(\S+)\s*(.*)', l)
        if m:
            ins.append((int(m.group(1), 16), m.group(2), m.group(3).split(';')[0].strip()))
    return ins

def analyze(ins):
    addr = [a for a, _, _ in ins]
    idx = {a: i for i, a in enumerate(addr)}
    calls_cv = collections.Counter()
    panics = 0
    for a, op, arg in ins:
        if op == 'bl':
            tgt = arg
            if 'containers_verus' in tgt and 'drop_glue' not in tgt and 'refuse' not in tgt:
                ids = [i for i in v0_idents(tgt) if len(i) > 2 and not re.match(r'^(Cs|B\d|E|R)', i)
                       and i not in ('semi_persistent_containers_verus', 'retained_containers_bench', 'core', 'alloc')]
                name = '::'.join([i for i in ids if not re.match(r'^[A-Z]$', i)][-5:])
                cold = re.search(r'grow_one|grow_to|push_fresh|env_compress_default|reserve|shrink|restore_frame|push_frame|mark|new\b|drop|realloc', name)
                calls_cv[('cold ' if cold else 'HOT  ') + name] += 1
            if re.search(r'refuse|unwrap_failed|panic|expect_failed|handle_error|slice_index|len_mismatch|option', tgt):
                panics += 1
    loops = []
    for i, (a, op, arg) in enumerate(ins):
        if op.startswith('b') and op not in ('bl', 'blr', 'br', 'brk'):
            m = re.match(r'(?:\S+,\s*)?0x([0-9a-f]+)', arg)
            if m:
                t = int(m.group(1), 16)
                if t <= a and t in idx:
                    loops.append((idx[t], i))
    carried = set(); dup = set(); inner = None
    # innermost loops only: a loop that contains no other loop
    loops = [(s, e) for (s, e) in loops if not any(s < s2 and e2 < e for (s2, e2) in loops)]
    for s, e in loops:
        n = e - s + 1
        if n < 8: continue
        if inner is None or n < inner: inner = n
        stores = collections.defaultdict(list); loads = collections.defaultdict(list)
        for j in range(s, e + 1):
            op, arg = ins[j][1], ins[j][2]
            for mm in re.finditer(r'\[sp, #(0x[0-9a-f]+)\]|\[(x29), #-?(0x[0-9a-f]+)\]', arg):
                key = mm.group(0)
                if op.startswith(('str', 'stp', 'stur')): stores[key].append(j)
                elif op.startswith(('ldr', 'ldp', 'ldur')): loads[key].append(j)
        for k in stores:
            if k in loads: carried.add(k)
        for k, ls in loads.items():
            if len(ls) > 1 and k not in stores: dup.add(k)
    return dict(instr=len(ins), calls_cv=calls_cv, panics=panics, carried=sorted(carried), dup=sorted(dup), inner=inner)

rows = []
for fn, ordinal, sym in closures:
    if flt and flt not in fn: continue
    r = analyze(disasm(sym))
    rows.append((fn, ordinal, r))

print(f"{'function':58s} {'arm':>3s} {'instr':>6s} {'inner':>6s} {'cv-calls':>8s} {'panic':>5s} {'carried':>8s} {'dup':>4s}")
for fn, o, r in rows:
    print(f"{fn:58s} {o:3d} {r['instr']:6d} {str(r['inner']):>6s} {sum(r['calls_cv'].values()):8d} {r['panics']:5d} {len(r['carried']):8d} {len(r['dup']):4d}")
    for name, c in r['calls_cv'].most_common():
        print(f"      call x{c}: {name[:100]}")
    if r['carried']: print(f"      carried through stack: {r['carried'][:6]}")
