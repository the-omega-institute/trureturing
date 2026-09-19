#!/usr/bin/env python3
"""Check original top fans and ancestor cuts on a supplied whole AP cover.

Python 3.9+, standard library only. Input is JSON with an aps field containing
[residue, modulus] pairs; extra fields, such as those in the 369 checker output,
are allowed. All hypotheses and necessary conditions are checked on the full
original period. This is an exact finite verifier for subsequent cover searches,
not a proof of the general theorems, a solver, or a Lean certification. Checks
remain active under -O. The optional period limit rejects before enumeration.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
import json
from math import isqrt, lcm, prod
from pathlib import Path


COUNTS = Counter()
H1_BOUNDARY = ((0, 2), (0, 3), (1, 4), (5, 6), (7, 12))


class VerificationFailure(Exception):
    def __init__(self, stage, message):
        super().__init__(message)
        self.stage = stage


def check(condition, message, stage='necessary-condition'):
    COUNTS[stage + '_checks'] += 1
    if not condition:
        raise VerificationFailure(stage, message)


def factors(n):
    result, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = 1
    return result


def height(n, q):
    e = 0
    while n % q == 0:
        e += 1
        n //= q
    return e


def ratio(value):
    return dict(numerator=value.numerator, denominator=value.denominator)


def original_family(data, max_period):
    aps = data.get('aps') if isinstance(data, dict) else None
    check(isinstance(aps, (list, tuple)) and bool(aps), 'input requires a nonempty aps list', 'input')
    A = {}
    for row in aps:
        check(isinstance(row, (list, tuple)) and len(row) == 2,
              'each AP must be [residue, modulus]', 'input')
        a, d = row
        check(type(a) is int and type(d) is int and d > 1 and 0 <= a < d,
              'AP entries must be canonical integer residues and moduli greater than one', 'input')
        check(d not in A, 'original numerical moduli must be distinct', 'input')
        A[d] = a
    A = dict(sorted(A.items()))
    Q = lcm(*A)
    check(max_period is None or Q <= max_period, 'period exceeds the requested enumeration limit', 'input')
    for d in A:
        for e in range(1, isqrt(d) + 1):
            if d % e == 0:
                check((e == 1 or e in A) and d // e in A,
                      'missing original divisor of modulus ' + str(d), 'hypothesis')
    for d, e in combinations(A, 2):
        if e % d == 0:
            check((A[d] - A[e]) % d != 0, 'comparable original classes intersect', 'hypothesis')
    hits = tuple(frozenset(d for d, a in A.items() if z % d == a) for z in range(Q))
    check(all(hits), 'original classes do not cover the full period', 'hypothesis')
    private = {d: [] for d in A}
    for z, labels in enumerate(hits):
        if len(labels) == 1:
            private[next(iter(labels))].append(z)
    for d, points in private.items():
        check(bool(points), 'original modulus has no private point: ' + str(d), 'hypothesis')
    COUNTS['period_points'] = Q
    return A, Q, hits, private


def prime_geometry(q, H, A, Q, hits, private):
    power, B, r0 = q ** H, Q // q ** H, A[q]
    R = frozenset(x for x in range(B) if all(x % d != a for d, a in A.items() if d % q))
    crt = lambda x, v: v + power * (((x-v) * pow(power, -1, B)) % B)
    originals = {d: (height(d, q), d // q ** height(d, q)) for d in A if d % q == 0}
    palette = sorted(m for d, (e, m) in originals.items() if e == H and m > 1)
    traces = {(e, m): frozenset(x for x in R if x % m == A[d] % m)
              for d, (e, m) in originals.items() if m > 1}
    E = {m: traces[1, m] for m in palette}
    F = {m: traces[H, m] for m in palette}
    actual = {(z % B, (z % power) // q) for z in private[q]}
    expected = set(product(R, range(q ** (H-1))))
    check(bool(R) and actual == expected and len(private[q]) == len(expected),
          'prime-private set differs from the full original cofactor/tail product')
    check(all(z % q == r0 for z in private[q]), 'prime-private first root changed')
    roots = defaultdict(list)
    for d in originals:
        roots[A[d] % q].append(d)
        if d != q:
            check(all(z % B in R for z in private[d]), 'a q-bearing private cofactor is outside R_q')
    universal = {m: A[q*m] % q for (e, m), trace in traces.items() if e == 1 and trace == R}
    for m, root in universal.items():
        check(roots[root] == [q*m], 'a universal first ancestor is not a global singleton root')
    check(len(set(universal.values())) == len(universal), 'universal first ancestors share a root')
    check(len(universal) <= q-1, 'too many nonprime universal first roots')

    cutoffs, active_top = {}, {}
    for x in sorted(R):
        columns = defaultdict(list)
        for (e, m), trace in traces.items():
            if x in trace:
                columns[m].append(e)
        check(len(columns) >= q-1, 'too few actual compatible nonpure columns')
        ell = sorted(map(max, columns.values()), reverse=True)[q-2]
        cutoffs[x] = ell
        active_top[x] = [m for m in palette if x in F[m]]
        check((ell == H) == (len(active_top[x]) >= q-1), 'top count and actual cutoff disagree')
        for tail in range(q ** (H-1)):
            for root in range(q):
                if root == r0:
                    continue
                z = crt(x, q*tail + root)
                check(all(d % q == 0 for d in hits[z]), 'an original root lift meets a q-free class')
                check(any(originals[d][0] <= ell for d in hits[z]), 'actual shallow truncation loses coverage')
                COUNTS['full_tail_root_lifts'] += 1
    for d, (e, _) in originals.items():
        if d != q:
            check(all(cutoffs[z % B] >= e for z in private[d]), 'private support violates the actual cutoff')
    low = sorted(x for x in R if cutoffs[x] < H)
    gain = sum(q ** (H-cutoffs[x]) - 1 for x in R)
    baseline = (q-2)*len(private[q]) + len(R)
    strengthened = sum((q-2)*q ** (H-1) + q ** (H-cutoffs[x]) for x in R)
    check(strengthened-baseline == gain, 'full-period source normalization does not balance')
    result = dict(q=q, H=H, cofactor_period=B, prime_root=r0, cofactor_region=sorted(R),
                  full_tails_per_cofactor=q ** (H-1), prime_private_count=len(private[q]),
                  prime_private_mass=ratio(Fraction(len(R), q*B)), top_palette=palette,
                  universal_first_cofactors=sorted(universal),
                  cutoff_histogram=dict(sorted(Counter(cutoffs.values()).items())),
                  cofactor_cutoffs=[[x, cutoffs[x]] for x in sorted(R)], low_cofactors=low,
                  all_high=not low, baseline_source_count=baseline, strengthened_source_count=strengthened,
                  source_gain_count=gain, source_gain_mass=ratio(Fraction(gain, Q)))
    return result, dict(R=R, E=E, F=F, U=universal, crt=crt, roots=roots, active=active_top)


def top_fan(result, g, A, Q, hits, private):
    q, H, B = result['q'], result['H'], result['cofactor_period']
    R, E, F, U, crt = (g[k] for k in ('R', 'E', 'F', 'U', 'crt'))
    top, witness = q ** H, private[q ** H][0]
    x, prefix = witness % B, witness % (q ** (H-1))
    fan, siblings = [], []
    for digit in range(q):
        v = prefix + digit * q ** (H-1)
        z = crt(x, v)
        check(all(height(d, q) == H for d in hits[z]), 'a pure-top private sibling meets a lower original')
        if z != witness:
            candidates = sorted(d for d in hits[z] if d != top)
            check(bool(candidates), 'a pure-top sibling has no nonpure top original')
            chosen = candidates[0]
            fan.append(chosen // top)
            siblings.append(dict(point=z, original_modulus=chosen))
    check(len(fan) == len(set(fan)) == q-1, 'private sibling fan repeats a numerical top color')
    check(len(U) <= q-2, 'a high original leaves no root outside the universal first roots')
    proper = [m for m in fan if E[m] and E[m] != R]
    check(bool(proper), 'private top fan has no nonempty proper first-ancestor trace')
    for m in proper:
        residues = {y % m for y in R}
        check(len(residues) >= 2 and A[m] not in residues and m >= 3,
              'proper ancestor trace does not separate two original cofactor residues from its parent')
    check(len(R) >= 2, 'high pure fan has fewer than two actual cofactors')
    if result['all_high']:
        palette = result['top_palette']
        check(len(palette) >= q, 'all-high has fewer than q global nonpure top colors')
        inventory = {q ** e for e in range(1, H+1)}
        inventory.update(q ** e*m for m in palette[:q] for e in range(H+1))
        check(inventory.issubset(A) and len(inventory) == (q+1)*H+q,
              'conditional original divisor inventory failed')
    else:
        check(result['source_gain_count'] >= q-1, 'a low cofactor has less than one finite gain quantum')
    result['high_height'] = dict(applicable=True, pure_top_private_point=witness,
                                fan_cofactor=x, sibling_fan=siblings, fan_colors=fan,
                                proper_first_ancestor_colors=proper,
                                proper_ancestor_traces={m: sorted(E[m]) for m in proper},
                                all_high_class_count_bound=(q+1)*H+q)


def ancestor_cuts(result, g, A, private):
    q, H, B = result['q'], result['H'], result['cofactor_period']
    R, E, F, U, active = (g[k] for k in ('R', 'E', 'F', 'U', 'active'))
    palette = result['top_palette']
    if len(U) != q-2:
        result['ancestor_cuts'] = dict(applicable=False, reason='first roots are not saturated by q-2 universal mixed originals')
        return
    free_roots = set(range(q)) - {A[q]} - set(U.values())
    check(len(free_roots) == 1, 'saturated roots do not leave exactly one first root')
    root = next(iter(free_roots))
    excluded = {q} | {q*m for m in U}
    check(all(A[d] % q == root for d in A if d % q == 0 and d not in excluded),
          'a remaining q-bearing original is outside the saturated free root')
    cuts = []
    for m in palette:
        if m in U:
            continue
        upper = [n for n in palette if n % m == 0]
        outside = [n for n in palette if n % m != 0]
        check(bool(E[m]), 'an actual first ancestor has empty cofactor trace')
        for n in upper:
            check(not E[m].intersection(F[n]), 'first ancestor intersects a top trace in its divisibility upper cone')
        counts = [sum(n in active[x] for n in outside) for x in sorted(E[m])]
        check(all(set(active[x]).issubset(outside) for x in E[m]), 'active top palette escapes the original upper-cone exclusion')
        if result['all_high']:
            check(min(counts) >= q-1, 'all-high fails the actual ancestor trace cut')
        if len(outside) <= q-2:
            check(E[m].issubset(result['low_cofactors']), 'small upper-cone complement retains a high cofactor')
            check(result['source_gain_count'] >= (q-1)*len(E[m]), 'ancestor-trace finite gain lost its original period factor')
        cuts.append(dict(cofactor=m, first_ancestor_private_point=private[q*m][0],
                         ancestor_trace=sorted(E[m]), upper_cone=upper, outside_upper_cone=outside,
                         minimum_active_outside_on_trace=min(counts),
                         count_cut_slack=sum(counts)-(q-1)*len(E[m]),
                         small_complement_forces_low=len(outside) <= q-2))
    chain = all(n % m == 0 or m % n == 0 for m, n in combinations(palette, 2))
    if chain:
        outside_U = sorted(set(palette) - set(U))
        check(bool(outside_U), 'private fan leaves no color outside the saturated universal set')
        first = outside_U[0]
        check(all(n in U for n in palette if n % first != 0), 'chain minimum outside U has a nonuniversal predecessor')
        check(bool(result['low_cofactors']), 'a saturated chain palette remains all-high')
    result['ancestor_cuts'] = dict(applicable=True, free_root=root, top_palette_is_chain=chain,
                                   all_height_chain_low_verified=chain, cuts=cuts)
    if H == 2 and result['all_high']:
        m = min(set(palette) - set(U))
        y = private[q*m][0]
        leaves = defaultdict(list)
        for n in active[y % B]:
            leaves[A[q*q*n] % (q*q)].append(n)
        collision = next((ns for ns in leaves.values() if len(ns) >= 2), None)
        check(collision is not None, 'height-two private ancestor has no coactive top collision')
        check(all(n % m != 0 and m % n != 0 for m, n in combinations(collision, 2)),
              'coactive same-leaf top colors fail to form an antichain')
        result['ancestor_cuts']['height_two_antichain'] = dict(private_point=y, colors=collision)


def binary_conditions(result, g, A, Q):
    q, H, B = result['q'], result['H'], result['cofactor_period']
    if q == 2 or Q % 2:
        result['binary'] = dict(applicable=False, reason='requires an odd q and an even original period')
        return
    survivors = {}
    for k in range(1, height(Q, 2)+1):
        leftover = [b for b in range(2 ** k) if all(b % (2 ** j) != A[2 ** j] for j in range(1, k+1))]
        check(len(leftover) == 1 and all(x % (2 ** k) == leftover[0] for x in g['R']),
              'actual binary ladder has no common unique survivor')
        survivors[k] = leftover[0]
    for d in A:
        if d % q == 0:
            k = height(d, 2)
            check(k <= q-2, 'an original q-bearing cofactor exceeds the binary exponent bound')
            check(all(2 ** j in g['U'] for j in range(1, k+1)), 'binary divisors do not supply actual universal first ancestors')
    if result['all_high']:
        check(all(height(m, 2) <= q-3 for m in result['top_palette']), 'all-high top palette violates the strict binary bound')
    skeleton_top = q ** H * 2 ** (q-2)
    if skeleton_top in A:
        check(bool(result['low_cofactors']), 'saturated binary skeleton has no low cofactor')
    small, profile = [], []
    odd_factors = {p: e for p, e in factors(B).items() if p != 2}
    if q == 3:
        if len(odd_factors) <= 1 and sum(odd_factors.values()) <= 2:
            small.append('odd part has at most two nonunit prime-power divisors')
        if 6 in A and len(odd_factors) <= 1:
            small.append('original 6 and one odd cofactor prime give an all-height chain cut')
        if 6 in A and len(odd_factors) == 2 and min(odd_factors.values()) <= 1:
            small.append('original 6 and two odd cofactor primes, one of height one, give an upper-cone cut')
        if 6 in A:
            top_heights = Counter()
            for m in result['top_palette']:
                for p, e in factors(m).items():
                    if p != 2:
                        top_heights[p] = max(top_heights[p], e)
            for p in sorted(top_heights):
                other_divisors = prod(e+1 for s, e in top_heights.items() if s != p)
                if result['all_high']:
                    check(p in result['top_palette'] and other_divisors >= 3,
                          'all-high ternary top support violates the prime upper-cone divisor bound')
                profile.append(dict(top_prime=p, top_height=top_heights[p],
                                    other_prime_divisor_count=other_divisors,
                                    necessary_if_all_high=3))
        if small:
            check(bool(result['low_cofactors']) and result['source_gain_count'] >= 2,
                  'declared ternary small-palette hypotheses have no finite low-cofactor gain')
    result['binary'] = dict(applicable=True, survivor_residues=survivors,
                            saturated_binary_top_original=skeleton_top if skeleton_top in A else None,
                            odd_cofactor_factorization=odd_factors, original_6_present=6 in A,
                            ternary_top_prime_profile=profile,
                            verified_small_palette_conditions=small)


def verify(data, max_period=None):
    A, Q, hits, private = original_family(data, max_period)
    reports = []
    for q, H in factors(Q).items():
        result, geometry = prime_geometry(q, H, A, Q, hits, private)
        if H >= 2:
            top_fan(result, geometry, A, Q, hits, private)
            ancestor_cuts(result, geometry, A, private)
            binary_conditions(result, geometry, A, Q)
        else:
            result['high_height'] = dict(applicable=False, reason='H=1: the pure top equals the prime and a first ancestor can equal its top class')
        reports.append(result)
    return dict(status='verified finite original cover', scope=__doc__.strip(), period=Q,
                aps=[[a, d] for d, a in A.items()], aps_order='[residue, modulus]',
                original_class_count=len(A), private_counts={d: len(zs) for d, zs in private.items()},
                private_witnesses={d: zs[0] for d, zs in private.items()},
                primes=reports, counts=dict(sorted(COUNTS.items())))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument('--input', type=Path, help='JSON containing aps=[residue, modulus] pairs')
    source.add_argument('--fixture', choices=['h1-boundary'], help='the explicit five-class whole cover of period 12')
    parser.add_argument('--max-period', type=int, help='reject larger periods before full enumeration')
    args = parser.parse_args()
    try:
        check(args.max_period is None or args.max_period > 0, 'max-period must be positive', 'input')
        data = dict(aps=H1_BOUNDARY) if args.fixture else json.loads(args.input.read_text(encoding='utf-8'))
        output = verify(data, args.max_period)
        if args.fixture:
            ternary = next(r for r in output['primes'] if r['q'] == 3)
            check(ternary['H'] == 1 and ternary['all_high'] and ternary['top_palette'] == [2, 4],
                  'period-12 boundary fixture does not exhibit the stated H=1 exception')
            output['fixture_boundary'] = dict(q=3, H=1, all_high=True, top_colors=[2, 4],
                                              high_height_theorems_applied=False,
                                              failed_if_unrestricted=['at least q top colors', 'binary exponent at most q-2'])
            output['counts'] = dict(sorted(COUNTS.items()))
        print(json.dumps(output, indent=2, sort_keys=True))
    except (VerificationFailure, OSError, ValueError) as error:
        print(json.dumps(dict(status='verification rejected', stage=getattr(error, 'stage', 'input'),
                              error=str(error), counts=dict(sorted(COUNTS.items()))), sort_keys=True))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
