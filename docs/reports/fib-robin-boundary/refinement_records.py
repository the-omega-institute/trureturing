#!/usr/bin/env python3
"""Enumerate conditional records for operation-summary refinement.

Run with --out PATH. Integer-only, standard library, no project/scratch imports.
Small raw affine-behavior models are checked independently of eta labels.
"""
from __future__ import annotations

import sys

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit("Run without -O: exact checks require assertions.")

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import json
from math import gcd, prod
from pathlib import Path


@lru_cache(maxsize=None)
def factor(n):
    result = []
    p = 2
    while p*p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            result.append((p, e))
        p = 3 if p == 2 else p + 2
    if n > 1:
        result.append((n, 1))
    return tuple(result)


@lru_cache(maxsize=None)
def divisors(n):
    out = [1]
    for p, h in factor(n):
        out = [d*p**e for d in out for e in range(h+1)]
    return tuple(sorted(out))


def phi(n):
    return prod((p-1)*p**(h-1) for p, h in factor(n))


def valuation(n, p, cap):
    if n == 0:
        return cap
    e = 0
    while e < cap and n % p == 0:
        n //= p
        e += 1
    return e


def local_eta(x, p, h, e):
    x %= p**h
    r = valuation(x, p, h)
    m = p**(h-e)
    return (0, r, (x//p**r) % m) if r < e else (1, (x//p**e) % m, 0)


@lru_cache(maxsize=None)
def eta_list(H, d):
    assert H >= 2 and H % d == 0
    fd = dict(factor(d))
    return tuple(tuple(local_eta(x, p, h, fd.get(p, 0)) for p, h in factor(H))
                 for x in range(H))


def predicted_max(H, old, new):
    assert old % new == 0 and H % old == 0
    eo, en = dict(factor(old)), dict(factor(new))
    local = [p**(eo.get(p, 0)-en.get(p, 0)) if eo.get(p, 0) < h
             else phi(p**(h-en.get(p, 0))) for p, h in factor(H)]
    answer = prod(local)
    numerator, denominator = phi(H//new), phi(H//old)
    assert numerator % denominator == 0
    assert answer == numerator // denominator
    return answer


def audit_partition(H, old, new, coarse, fine, counts):
    fibers = defaultdict(set)
    fine_to_coarse = {}
    for x in range(H):
        fibers[coarse[x]].add(fine[x])
        assert fine[x] not in fine_to_coarse or fine_to_coarse[fine[x]] == coarse[x]
        fine_to_coarse[fine[x]] = coarse[x]
    actual = max(map(len, fibers.values()))
    expected = predicted_max(H, old, new)
    assert actual == expected
    for x in range(H):
        if gcd(x, H) == 1:
            assert len(fibers[coarse[x]]) == actual
            counts['unit_source_maximum_checks'] += 1
    dec = {c: tuple(sorted(f)) for c, f in fibers.items()}
    enc = {c: {f: i for i, f in enumerate(fs)} for c, fs in dec.items()}
    record = tuple(enc[coarse[x]][fine[x]] for x in range(H))
    assert len(set(record)) == expected
    for x in range(H):
        assert dec[coarse[x]][record[x]] == fine[x]
        counts['encode_decode_checks'] += 1
    # R=1 iff all exponents are unchanged, except a possible full 2-axis
    # dropping exactly one level; state-label renaming is still permitted.
    exceptional = H % 2 == 0 and valuation(old, 2, 1000) == valuation(H, 2, 1000) and new*2 == old
    assert (expected == 1) == (new == old or exceptional)
    counts['refinement_pairs'] += 1
    return actual, sorted(Counter(map(len, fibers.values())).items())


def raw_affine_partition(H, d, counts):
    # Actual gcd responses for every affine action ax+db; no eta formula.
    classes, labels = {}, []
    for x in range(H):
        response = tuple(gcd(a*x+d*b, H) for a in range(H) for b in range(H//d))
        counts['raw_affine_gcd_evaluations'] += H*(H//d)
        labels.append(classes.setdefault(response, len(classes)))
    eta = eta_list(H, d)
    forward, backward = {}, {}
    for x in range(H):
        assert eta[x] not in forward or forward[eta[x]] == labels[x]
        assert labels[x] not in backward or backward[labels[x]] == eta[x]
        forward[eta[x]] = labels[x]
        backward[labels[x]] = eta[x]
    counts['raw_affine_models'] += 1
    return tuple(labels)


def run():
    counts = Counter()
    for H in range(2, 25):
        raw = {d: raw_affine_partition(H, d, counts) for d in divisors(H)}
        for old in divisors(H):
            for new in divisors(old):
                audit_partition(H, old, new, raw[old], raw[new], counts)
                counts['raw_behavior_refinement_pairs'] += 1
    for H in range(2, 129):
        for old in divisors(H):
            for new in divisors(old):
                audit_partition(H, old, new, eta_list(H, old), eta_list(H, new), counts)
                counts['eta_refinement_pairs'] += 1
        eta_list.cache_clear()

    H = 5040
    selected = ((5040, 2520), (5040, 1), (5040, 7), (5040, 10),
                (5040, 2), (5040, 3), (5040, 5), (2520, 1),
                (2520, 1260), (7, 1), (10, 1), (2, 1),
                (3, 1), (5, 1), (1, 1), (16, 8), (8, 4))
    examples = []
    for old, new in selected:
        coarse, fine = eta_list(H, old), eta_list(H, new)
        maximum, histogram = audit_partition(H, old, new, coarse, fine, counts)
        examples.append({'old': old, 'new': new,
                         'old_states': len(set(coarse)), 'new_states': len(set(fine)),
                         'record_values': maximum,
                         'coarse_fiber_size_histogram': {str(k):v for k,v in histogram}})
    # Adding H/2 to any old library leaves the partition unchanged for even H.
    for old in divisors(H):
        new = gcd(old, H//2)
        assert predicted_max(H, old, new) == 1
        coarse, fine = eta_list(H, old), eta_list(H, new)
        c2f = {}
        for x in range(H):
            assert coarse[x] not in c2f or c2f[coarse[x]] == fine[x]
            c2f[coarse[x]] = fine[x]
            counts['half_modulus_no_refinement_sources'] += 1
        counts['half_modulus_no_refinement_libraries'] += 1

    # Incomparable requested libraries: joint image equals gcd refinement.
    incomparable = []
    for old, requested in ((7, 10), (10, 7), (16, 9), (9, 16)):
        new = gcd(old, requested)
        coarse = eta_list(H, old)
        joint = tuple(zip(coarse, eta_list(H, requested)))
        maximum, histogram = audit_partition(H, old, new, coarse, joint, counts)
        expected_fine = eta_list(H, new)
        for x, y in ((x, (x+H//2) % H) for x in range(H)):
            assert (joint[x] == joint[y]) == (expected_fine[x] == expected_fine[y])
        # Strong complete partition comparison, not just sampled pairs.
        jf, fj = {}, {}
        for j, f in zip(joint, expected_fine):
            assert j not in jf or jf[j] == f
            assert f not in fj or fj[f] == j
            jf[j] = f
            fj[f] = j
        incomparable.append({'old':old, 'requested':requested, 'union':new, 'record_values':maximum})

    return {'scope':'Finite integer diagnostics for a direct corollary of section 100; no new Lean or novelty claim.',
            'domains': {'raw_affine_H':[2,24], 'eta_enumeration_H':[2,128],
                        'large_H':H, 'large_refinements':len(selected)},
            'counts': dict(sorted(counts.items())), 'examples':examples,
            'incomparable_libraries':incomparable,
            'formula':'min |R| = phi(H/d_new) / phi(H/d_old), when d_new divides d_old divides H',
            'fixed_record_contract':'A finite record value is decoded together with the old summary; labels may be reused across coarse fibers.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', required=True, type=Path)
    args = ap.parse_args()
    result = run()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True)+'\n',encoding='utf-8')
    print(json.dumps(result['counts'],sort_keys=True))


if __name__ == '__main__':
    main()
