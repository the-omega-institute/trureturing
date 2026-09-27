#!/usr/bin/env python3
"""Exact controls for joint prime-parent support and minimum-height ties.

Python 3.9+, standard library only; no files, repository imports or solvers.
Both literal AP fixtures are whole even covers. The checks establish finite
support bounds and a colliding height minimum, not unrestricted Erdos #7,
an odd-cover counterexample, a general exchange theorem or a Lean proof.
All checks remain active with python -O. Output is deterministic JSON.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, lcm, prod
import json


COUNTS = Counter()
FIXTURES = {
    'Q450': ((0, 2), (0, 3), (0, 5), (5, 6), (4, 9), (9, 10),
             (7, 15), (11, 25), (13, 30), (1, 45), (31, 50),
             (46, 75), (1, 150), (16, 225)),
    'Q3150b': ((0, 2), (0, 3), (0, 5), (5, 6), (0, 7), (4, 9),
               (7, 10), (3, 14), (4, 15), (19, 21), (6, 25),
               (8, 35), (25, 42), (16, 45), (21, 50), (55, 63),
               (23, 70), (1, 75), (1, 105), (16, 175),
               (223, 315), (436, 525)),
}


def check(condition, message):
    COUNTS['checks'] += 1
    if not condition:
        raise ArithmeticError(message)


def height(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def prime_support(n):
    result, p = [], 2
    while p * p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.append(n)
    return tuple(result)


def crt(a, power, x, cofactor):
    if cofactor == 1:
        return a % power
    return (a + power * ((x - a) * pow(power, -1, cofactor) % cofactor)) % (power * cofactor)


def reset(z, q, root, period):
    power = q ** height(period, q)
    return crt(z % power - z % q + root, power, z % (period // power), period // power)


def prepare(name):
    aps = FIXTURES[name]
    A = dict(sorted((d, a) for a, d in aps))
    check(len(A) == len(aps), 'original moduli must be distinct')
    check(all(d > 1 and 0 <= a < d for d, a in A.items()), 'invalid literal AP')
    Q = lcm(*A)
    primes = frozenset(prime_support(Q))
    check(primes <= A.keys(), 'an original prime label is missing')
    for d in A:
        check(all(e in A for e in range(2, d + 1) if d % e == 0), 'divisor closure fails')
    for d, m in combinations(A, 2):
        if d % m == 0 or m % d == 0:
            check((A[d] - A[m]) % gcd(d, m) != 0, 'comparable original classes intersect')
    hits = tuple(frozenset(d for d, a in A.items() if z % d == a) for z in range(Q))
    check(all(hits), 'whole-cover membership fails')
    private = {d: frozenset(z for z, E in enumerate(hits) if E == {d}) for d in A}
    check(all(private.values()), 'a class has no private witness')
    residual = {z: E for z, E in enumerate(hits) if not E & primes and len(E) >= 2}
    for E in residual.values():
        check(all(d % m and m % d for d, m in combinations(E, 2)), 'active antichain fails')
    COUNTS['literal_period_points'] += Q
    return dict(name=name, A=A, Q=Q, primes=primes, hits=hits, private=private,
                pi={d: F(len(points), Q) for d, points in private.items()}, residual=residual)


def matching_menu(q, rows, forced):
    """Enumerate the entire forced menu; check maximum rank by all Hall cuts.

    Each row is one nonprime root, each edge an original numerical modulus.
    The empty choice is necessary because a maximum matching can be partial.
    """
    color = lambda d: d // q ** height(d, q)
    neighbors = tuple(frozenset(color(d) for d in row) for row in rows)
    deficiency = 0
    for mask in range(1 << len(rows)):
        selected = [i for i in range(len(rows)) if mask >> i & 1]
        union = set().union(*(neighbors[i] for i in selected))
        deficiency = max(deficiency, len(selected) - len(union))
        COUNTS['hall_subsets'] += 1
    rank = len(rows) - deficiency
    menus = []
    for choice in product(*((None,) + row for row in rows)):
        edges = tuple(d for d in choice if d is not None)
        if len(edges) != rank or not forced <= set(edges):
            continue
        if len({color(d) for d in edges}) == rank:
            menus.append(edges)
    check(bool(menus), 'forced edges prevent Hall maximum rank')
    check(len(set(menus)) == len(menus), 'a local matching was enumerated twice')
    costs = tuple(sum(height(d, q) for d in edges) for edges in menus)
    minimum = min(costs)
    minima = tuple(edges for edges, cost in zip(menus, costs) if cost == minimum)
    check(minimum >= rank, 'selected exponent below one')
    COUNTS['local_maximum_matchings'] += len(menus)
    COUNTS['local_minimum_matchings'] += len(minima)
    return rank, tuple(menus), minimum, minima


def sources(model):
    A, Q, primes = (model[k] for k in ('A', 'Q', 'primes'))
    all_sources, summaries = {}, {}
    for q in sorted(primes):
        H = height(Q, q)
        power, tails, B = q ** H, q ** (H - 1), Q // q ** H
        roots = tuple(r for r in range(q) if r != A[q])
        forced = set()
        for root in roots:
            ds = [d for d in A if d % q == 0 and A[d] % q == root]
            if len(ds) == 1:
                d = ds[0]
                check(height(d, q) == 1 and d > q, 'forced edge is not mixed height one')
                forced.add(d)
        R = tuple(x for x in range(B) if all(x % d != a for d, a in A.items() if d % q))
        check(bool(R), 'empty actual cofactor region')
        histogram, seen, records = Counter(), set(), []
        for x in R:
            compatible = []
            column_heights = {}
            for d, a in A.items():
                e = height(d, q)
                if e and d != q:
                    m = d // q ** e
                    if x % m == a % m:
                        compatible.append(d)
                        if m > 1:
                            column_heights[m] = max(e, column_heights.get(m, 0))
            check(len(column_heights) >= q - 1, 'too few compatible nonpure columns')
            cutoff = sorted(column_heights.values(), reverse=True)[q - 2]
            histogram[cutoff] += 1
            local_rank_sum = 0
            for t in range(tails):
                y = crt(A[q] + q * t, power, x, B)
                check(y not in seen and model['hits'][y] == {q}, 'source product loses private provenance')
                seen.add(y)
                rows = []
                for root in roots:
                    z = reset(y, q, root, Q)
                    check(z == crt(root + q * t, power, x, B), 'root reset changes original tail')
                    full = {d for d in compatible if A[d] % q == root
                            and t % q ** (height(d, q) - 1) == (A[d] % q ** height(d, q)) // q}
                    check(full == model['hits'][z], 'prefix graph disagrees with literal AP hits')
                    low = {d for d in full if height(d, q) <= cutoff}
                    check(bool(low), 'truncation loses complete root coverage')
                    rows.append(tuple(sorted(d for d in low if d // q ** height(d, q) > 1)))
                    COUNTS['literal_root_checks'] += 1
                rank, menu, minimum, minima = matching_menu(q, tuple(rows), forced)
                local_rank_sum += rank
                record = dict(q=q, y=y, H=H, cutoff=cutoff, roots=roots, rows=tuple(rows),
                              forced=frozenset(forced), rank=rank, menu=menu,
                              minimum=minimum, minima=minima, chosen=minima[0])
                all_sources[q, y] = record
                records.append(record)
                COUNTS['source_points'] += 1
            check(F(local_rank_sum, tails) >= q - 2 + F(1, q ** (cutoff - 1)),
                  'same-cofactor full-tail rank bound fails')
        check(seen == model['private'][q] and len(seen) == len(R) * tails,
              'cofactor-tail product differs from complete original private source')
        summaries[q] = dict(q=q, H=H, cofactor_states=len(R), cutoff_counts=dict(sorted(histogram.items())),
                            source_points=len(seen), forced=sorted(forced),
                            rbar=sum((n * (q - 2 + F(1, q ** (ell - 1)))
                                      for ell, n in histogram.items()), F()) / len(R),
                            minimum_height=sum(s['minimum'] for s in records),
                            rank_histogram=dict(sorted(Counter(s['rank'] for s in records).items())),
                            minimum_height_histogram=dict(sorted(Counter(s['minimum'] for s in records).items())))
    return all_sources, summaries


def support_bound(model, all_sources, summaries):
    A, Q, primes, pi = (model[k] for k in ('A', 'Q', 'primes', 'pi'))
    Fq = {q: frozenset(d for d in A if d % q == 0 and d // q ** height(d, q) in primes) for q in primes}
    K = {z: frozenset(q for q in primes if all(d % q == 0 for d in E))
         for z, E in model['residual'].items()}
    for z, E in model['residual'].items():
        eligible = {q: E & Fq[q] for q in K[z] if E & Fq[q]}
        check(len(eligible) <= 2 and len(eligible) <= len(E), 'prime-parent direction capacity fails')
        for q, r in combinations(eligible, 2):
            check(not eligible[q] & eligible[r], 'distinct prime directions share an eligible original label')
        COUNTS['residual_support_points'] += 1
    rows, strengthened = [], F()
    for q, summary in summaries.items():
        alpha = F(q, q - 1) * (1 - F(1, q ** summary['H']))
        u = sum((pi[d] for d in Fq[q]), F())
        epsilon = F(sum(q in K[z] for z in K), Q)
        delta = F(sum(len(E & Fq[q]) for E in model['residual'].values()), Q)
        gamma = F(sum(q in K[z] and bool(E & Fq[q]) for z, E in model['residual'].items()), Q)
        check(epsilon == (q - 1) * pi[q] - sum((pi[d] for d in A if d != q and d % q == 0), F()),
              'residual reset support disagrees with epsilon formula')
        P0 = prod((F(p - 1, p) for p in primes), start=F(1))
        phi = lambda d: prod(p ** (height(d, p) - 1) * (p - 1) for p in prime_support(d))
        check(delta == sum((P0 / phi(d) - pi[d] for d in Fq[q]), F()),
              'literal containing multiplicity disagrees with Delta formula')
        U = min((len(primes) - 1) * pi[q], u + min(epsilon, delta))
        Ugamma = min((len(primes) - 1) * pi[q], u + gamma)
        check(0 <= gamma <= min(epsilon, delta) and Ugamma <= U, 'joint support does not refine allowance')
        f = sum(d // q not in primes for d in summary['forced'])
        lower = lambda allowance: f * pi[q] + max(F(), (summary['rbar'] - f) * pi[q] - allowance) / alpha
        lifted, prime_points, composite_count = set(), set(), 0
        for (p, y), source in all_sources.items():
            if p != q:
                continue
            for d in source['chosen']:
                z = reset(y, q, A[d] % q, Q)
                check(z not in lifted and d in model['hits'][z], 'fixed-q lift is not injective or original')
                lifted.add(z)
                if d in Fq[q]:
                    prime_points.add(z)
                    if z in model['residual']:
                        check(q in K[z] and bool(model['hits'][z] & Fq[q]), 'selected residual lift leaves joint support')
                    else:
                        check(model['hits'][z] == {d}, 'selected nonresidual lift is not private')
                else:
                    composite_count += 1
        P, C = F(len(prime_points), Q), F(composite_count, Q)
        bound = C / alpha + (1 - 1 / alpha) * f * pi[q]
        check(P <= Ugamma and P + C >= summary['rbar'] * pi[q], 'selected source violates refined bound')
        check(lower(U) <= lower(Ugamma) <= bound, 'refined lower bound exceeds actual forced source charge')
        strengthened += bound
        cells = Counter(tuple(sorted(E)) for z, E in model['residual'].items() if q in K[z])
        rows.append(dict(q=q, pi=str(pi[q]), rbar=str(summary['rbar']), f=f, alpha=str(alpha),
                         u=str(u), epsilon=str(epsilon), Delta=str(delta), Gamma=str(gamma),
                         U=str(U), U_Gamma=str(Ugamma), ST5=str(lower(U)), refined=str(lower(Ugamma)),
                         selected_prime_mass=str(P), selected_composite_mass=str(C),
                         cells=[dict(E=list(E), points=n, eligible=bool(set(E) & Fq[q])) for E, n in sorted(cells.items())]))
    M = sum((F(1, d) * (1 - prod((F(p - 1, p) for p in primes if d % p), start=F(1)))
             for d in A if d not in primes), F())
    literal_M = F(sum(len(E - primes) for E in model['hits'] if E & primes), Q)
    old, refined = (sum((F(row[key]) for row in rows), F()) for key in ('ST5', 'refined'))
    check(M == literal_M and old <= refined <= strengthened <= M, 'complete original target-budget control fails')
    return dict(rows=rows, ST5=str(old), refined=str(refined), gain=str(refined-old),
                actual_forced_source_charge=str(strengthened), M_comp=str(M))


def height_collision(model, all_sources, summaries):
    A, Q = model['A'], model['Q']
    check(model['hits'][1] == {75, 105}, 'collision target has the wrong active family')
    check({q for q in model['primes'] if all(d % q == 0 for d in model['hits'][1])} == {3, 5},
          'collision target has the wrong common-prime directions')
    a, b = all_sources[3, 351], all_sources[5, 3025]
    check(reset(1, 3, A[3], Q) == 351 and reset(1, 5, A[5], Q) == 3025, 'wrong original source reset')
    check(a['rows'] == ((75, 105), (6,)) and b['rows'] == ((105,), (10,), (35,), (15,)),
          'literal truncated collision menus changed')
    check(a['cutoff'] == b['cutoff'] == 1 and a['H'] == b['H'] == 2, 'wrong original or truncated height')
    check(a['forced'] == {6} and b['forced'] == {10, 15}, 'wrong forced original edges')
    check(set(a['menu']) == {(75, 6), (105, 6)} and b['menu'] == ((105, 10, 35, 15),),
          'collision witness omits an actual maximum matching')
    check(a['minimum'] == a['rank'] == 2 and b['minimum'] == b['rank'] == 4,
          'specified sources do not attain the absolute height lower bound')
    a['chosen'] = (105, 6)
    check(all(s['chosen'] in s['minima'] for s in all_sources.values()), 'joint witness is not a product of minima')
    total = sum(sum(height(d, q) for d in s['chosen']) for (q, _), s in all_sources.items())
    check(total == sum(s['minimum'] for s in all_sources.values()), 'separable minimum is not attained')

    def loads():
        result = Counter()
        for (q, y), source in all_sources.items():
            for d in source['chosen']:
                z = reset(y, q, A[d] % q, Q)
                check(d in model['hits'][z], 'selected lift misses its original AP')
                if z in model['residual']:
                    result[z, d] += 1
        return result

    before = loads()
    check(before[1, 105] == 2 and before[1, 75] == 0, 'specified global minimum does not have the claimed collision')
    check(height(75, 5) > b['cutoff'], 'competing q=5 source can use the proposed replacement')
    a['chosen'] = (75, 6)
    check(a['chosen'] in a['minima'], 'equal-height exchange leaves the maximum forced menu')
    after = loads()
    check(after[1, 105] == after[1, 75] == 1, 'specified residual collision was not repaired')
    check({slot for slot in before.keys() | after.keys() if before[slot] != after[slot]} == {(1, 105), (1, 75)},
          'the single-source exchange changed an additional slot')
    check(sum(sum(height(d, q) for d in s['chosen']) for (q, _), s in all_sources.items()) == total,
          'exchange changed total height')
    return dict(source_points=len(all_sources), minimum_total_height=total,
                sources=[dict(q=s['q'], y=s['y'], H=s['H'], cutoff=s['cutoff'],
                              forced=sorted(s['forced']), rows=s['rows'], maximum_menu=s['menu'],
                              rank=s['rank'], minimum_height=s['minimum']) for s in (a, b)],
                collision=dict(z=1, d=105, before=before[1, 105], after=after[1, 105]),
                replacement=dict(z=1, d=75, before=before[1, 75], after=after[1, 75]),
                per_prime=[{k: v for k, v in row.items() if k != 'rbar'} for row in summaries.values()],
                scope='One specified collision is repaired at equal height; other global slots are unchanged, not certified collision-free.')


def main():
    small = prepare('Q450')
    small_sources, small_rows = sources(small)
    support = support_bound(small, small_sources, small_rows)
    check(support['ST5'] == '2/25' and support['refined'] == '11/120'
          and support['gain'] == '7/600' and support['M_comp'] == '11/50', 'Q450 exact full-source values changed')
    check([(r['q'], r['Gamma'], r['U_Gamma'], r['refined']) for r in support['rows']]
          == [(2, '1/25', '67/450', '2/75'), (3, '7/450', '19/150', '19/600'),
              (5, '1/225', '2/45', '1/30')], 'Q450 per-prime support values changed')
    large = prepare('Q3150b')
    large_sources, large_rows = sources(large)
    collision = height_collision(large, large_sources, large_rows)
    check(collision['source_points'] == 605 and collision['minimum_total_height'] == 908,
          'Q3150b complete source minimum changed')
    print(json.dumps(dict(scope=__doc__.strip(), counts=dict(sorted(COUNTS.items())),
                          Q450=support, Q3150b=collision), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
