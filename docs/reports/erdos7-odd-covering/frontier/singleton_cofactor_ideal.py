#!/usr/bin/env python3
"""Exact singleton-cofactor and forced-selection checks on original APs.

Whole even covers, complete prime-power coordinates, original uniform Haar.
Only divisor-closed fixtures support the complete composite-target chain.
The affine refinement tests a strict source improvement, not that chain.
Standard library only; checks survive -O and require no repository imports.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, lcm, prod
import json


CHECKS = 0


def check(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ArithmeticError(message)


def support(n):
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.append(n)
    return tuple(result)


def val(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def phi(n):
    return prod(p ** (val(n, p) - 1) * (p - 1) for p in support(n))


def reset(x, q, root, Q):
    power = q ** val(Q, q)
    other = Q // power
    target = x % power - x % q + root
    return (x + other * ((target - x) * pow(other, -1, power) % power)) % Q


def prepare(aps, require=True):
    A = {d: a for a, d in aps}
    check(len(A) == len(aps), 'distinct original numerical labels')
    check(all(d > 1 and 0 <= a < d for d, a in A.items()), 'valid AP')
    Q = lcm(*A)
    primes = support(Q)
    check(all(p in A for p in primes), 'original support primes present')
    hits = tuple(frozenset(d for d, a in A.items() if x % d == a)
                 for x in range(Q))
    private = {d: tuple(x for x, hs in enumerate(hits) if hs == {d}) for d in A}
    covering = all(hits)
    irredundant = covering and all(private.values())
    comparable = all((A[d] - A[m]) % gcd(d, m) != 0
                     for d, m in combinations(A, 2) if d % m == 0 or m % d == 0)
    if require:
        check(irredundant, 'whole irredundant cover')
        check(comparable, 'comparable original classes disjoint')
    missing = sorted({j for d in A for j in range(2, d + 1)
                      if d % j == 0 and j not in A})
    return dict(A=A, Q=Q, primes=primes, hits=hits, private=private,
                pi={d: F(len(xs), Q) for d, xs in private.items()},
                covering=covering, irredundant=irredundant,
                comparable=comparable, missing=missing)


def graph(A, q, y, Q):
    rows = []
    for root in range(q):
        if root == A[q] % q:
            continue
        x = reset(y, q, root, Q)
        edges = []
        for d, a in sorted(A.items()):
            if d % q == 0 and x % d == a:
                m = d // q ** val(d, q)
                if m > 1:
                    edges.append((root, d, m))
        rows.append(tuple(edges))
    return tuple(rows)


def max_matchings(rows):
    best = []
    rank = -1
    for choices in product(*((None,) + row for row in rows)):
        chosen = tuple(edge for edge in choices if edge is not None)
        if len({m for _, _, m in chosen}) != len(chosen):
            continue
        if len(chosen) > rank:
            rank, best = len(chosen), [chosen]
        elif len(chosen) == rank:
            best.append(chosen)
    return best


def force_edges(matches, forced, A, q):
    normalized = []
    for matching in matches:
        colors = {m for _, _, m in matching}
        check(set(forced) <= colors, 'every maximum matching contains forced colors')
        new = [edge for edge in matching if edge[2] not in forced]
        new += [(A[q * m] % q, q * m, m) for m in sorted(forced)]
        check(len(new) == len(matching) and len({e[0] for e in new}) == len(new),
              'simultaneous forced-root relocation preserves rank')
        check({e[2] for e in new} == colors, 'relocation preserves exact color set')
        check(all(val(d, q) == 1 for _, d, m in new if m in forced),
              'forced columns use only actual height one')
        normalized.append(tuple(sorted(new)))
    return min(normalized)


def singleton_data(model, q):
    A, Q, private = model['A'], model['Q'], model['private']
    power = q ** val(Q, q)
    other = Q // power
    R = {x for x in range(other) if all(x % d != a for d, a in A.items() if d % q)}
    check(bool(R), 'nonempty cofactor source')
    expected = {x for x in range(Q) if x % q == A[q] % q and x % other in R}
    check(set(private[q]) == expected, 'exact prime-private product with all tails')
    check(F(len(R), other) == q * model['pi'][q], 'cofactor Haar normalization')
    forced = set()
    for root in range(q):
        if root == A[q] % q:
            continue
        ds = [d for d in A if d % q == 0 and A[d] % q == root]
        if len(ds) == 1:
            d = ds[0]
            check(val(d, q) == 1 and d > q, 'singleton has exact q-height one')
            forced.add(d // q)
    universal = {d // q for d, a in A.items() if val(d, q) == 1 and d > q
                 and all(x % (d // q) == a % (d // q) for x in R)}
    check(forced == universal, 'singleton iff universal actual child cofactor')
    L = lcm(*forced) if forced else 1
    c = min(R) % L
    check(all(x % L == c for x in R), 'one coherent actual cofactor class')
    relative = {d // q for d in A if d > q and d % q == 0 and L % (d // q) == 0}
    check(forced == relative, 'relative ideal uses only actual qn labels')
    for d in A:
        if d != q and d % q == 0:
            for x in private[d]:
                y = reset(x, q, A[q] % q, Q)
                check(y in expected and y % other == x % other,
                      'every actual child-private witness resets into same source')
        if d % q == 0 and d > q:
            m = d // q ** val(d, q)
            if m in support(L):
                check(A[d] % m == c % m, 'prime-color residue cannot mismatch forced ideal')
    for m in forced:
        child_private = {reset(x, q, A[q * m] % q, Q) for x in private[q]}
        check(set(private[q * m]) == child_private, 'full singleton-private cylinder')
        check(model['pi'][q * m] == model['pi'][q], 'singleton private masses equal')
    check(len(forced) <= q - 1, 'distinct nonprime singleton roots')
    if val(Q, q) >= 2:
        check(len(forced) <= q - 2, 'actual higher-q label reserves a nonsingleton root')
    if not model['missing']:
        for m in forced:
            check(all(j in forced for j in range(2, m + 1) if m % j == 0),
                  'divisor closure makes forced cofactors a divisor ideal')
            check(sum(m % j == 0 for j in range(1, m + 1)) <=
                  q - int(q * q in A), 'general cofactor divisor-count bound')
        check(set(support(L)) == forced.intersection(model['primes']),
              'prime members equal support of L only with divisor closure')
    cap = F(1, q * L) * prod(F(p - 1, p) for p in model['primes'] if (q * L) % p)
    P0 = prod(F(p - 1, p) for p in model['primes'])
    check(cap == P0 / ((q - 1) * phi(L)), 'same coherent CRT cap')
    check(model['pi'][q] <= cap, 'whole-source coherent cap')
    return dict(F=forced, L=L, c=c, cap=cap, R=R)


def source_row(model, q, data):
    A, Q, primes, pi = (model[k] for k in ('A', 'Q', 'primes', 'pi'))
    P0 = prod(F(p - 1, p) for p in primes)
    eligible = [d for d in A if d % q == 0 and d // q ** val(d, q) in primes]
    eps = (q - 1) * pi[q] - sum((pi[d] for d in A if d > q and d % q == 0), F())
    u = sum((pi[d] for d in eligible), F())
    delta = sum((P0 / phi(d) - pi[d] for d in eligible), F())
    U = min((len(primes) - 1) * pi[q], u + min(eps, delta))
    alpha = F(q, q - 1) * (1 - F(1, q ** val(Q, q)))
    rank_lower = q - 2 + F(1, q ** (val(Q, q) - 1))
    forced = data['F']
    f = sum(m not in primes for m in forced)
    selected = {}
    prime_count = composite_count = 0
    cache = {}
    for y in model['private'][q]:
        rows = graph(A, q, y, Q)
        if rows not in cache:
            cache[rows] = force_edges(max_matchings(rows), forced, A, q)
        chosen = cache[rows]
        for _, d, m in chosen:
            e = val(d, q)
            counts, heights = selected.setdefault(m, [0, set()])
            selected[m] = [counts + 1, heights | {e}]
            prime_count += m in primes
            composite_count += m not in primes
    P, C = F(prime_count, Q), F(composite_count, Q)
    check(P <= U and P + C >= rank_lower * pi[q], 'same 363 upper and full-tail mean rank')
    check(C >= f * pi[q] and P <= (q - 1 - f) * pi[q], 'forced composite mass and root slots')
    lower = f * pi[q] + max(F(), (rank_lower - f) * pi[q] - U) / alpha
    old = max(F(), rank_lower * pi[q] - U) / alpha
    strengthened = C / alpha + (1 - 1 / alpha) * f * pi[q]
    check(old <= lower <= strengthened, 'forced source lower dominates scalar 363')
    Uslot = min(U, (q - 1 - f) * pi[q])
    check(lower == f * pi[q] + max(F(), (rank_lower - f) * pi[q] - Uslot) / alpha,
          'root-slot cut leaves combined formula unchanged')
    for m, (count, heights) in selected.items():
        rho = prod(F(p - 1, p) for p in primes if p != q and m % p)
        used = sum((F(q, q ** e) for e in heights), F())
        check(F(count, Q) <= used * rho / (q * m), 'actual used-height source cylinder')
        if m in forced:
            check(count == len(model['private'][q]) and heights == {1} and used == 1,
                  'forced column has complete source and coefficient one')
    if not model['missing']:
        check(P >= len(support(data['L'])) * pi[q] and U >= len(support(data['L'])) * pi[q],
              'divisor-closed forced prime count')
        check(f == len(forced) - len(support(data['L'])), 'divisor-closed composite count')
    return dict(q=q, F=sorted(forced), L=data['L'], f=f, pi=str(pi[q]),
                coherent_cap=str(data['cap']), alpha=str(alpha), r=str(rank_lower),
                epsilon=str(eps), U=str(U), P=str(P), C=str(C),
                old_lower=str(old), forced_lower=str(lower),
                strengthened_source=str(strengthened), graph_patterns=len(cache)), selected


def beta_rho(primes, q, m):
    free = [p for p in primes if p != q and m % p]
    rho = prod(F(p - 1, p) for p in free)
    beta = F()
    for present in product((False, True), repeat=len(free)):
        probability = prod((F(1, p) if yes else F(p - 1, p)
                            for p, yes in zip(free, present)), start=F(1))
        beta += probability / (1 + int(m in primes) + sum(present))
    return beta, rho


def full_target_check(model, selections, rows):
    A, Q, primes = (model[k] for k in ('A', 'Q', 'primes'))
    source = target = F()
    for q, columns in selections.items():
        for m, (count, heights) in columns.items():
            if m in primes:
                continue
            check(m in A, 'complete target chain needs actual parent')
            beta, rho = beta_rho(primes, q, m)
            used = sum((F(q, q ** e) for e in heights), F())
            capacity = sum((F(1, Q * len(hs.intersection(primes)))
                            for hs in model['hits'] if q in hs and m in hs), F())
            check(capacity == beta / (q * m), 'literal original 1/k target allocation')
            charge = beta / (used * rho) * F(count, Q)
            check(charge <= capacity and beta >= rho, 'used-height source-to-target charge')
            source += charge
            target += capacity
    M = sum((F(1, m) * (1 - prod(F(p - 1, p) for p in primes if m % p))
             for m in A if m not in primes), F())
    strengthened = sum((F(row['strengthened_source']) for row in rows), F())
    lower = sum((F(row['forced_lower']) for row in rows), F())
    check(lower <= strengthened <= source <= target <= M, 'complete combined 363 forced target chain')
    return dict(combined_lower=str(lower), source_charge=str(source),
                target_charge=str(target), Mcomp=str(M))


def swap_checks(model, data):
    A, Q = model['A'], model['Q']
    candidates = legal_count = transports = 0
    for q in model['primes']:
        for d in A:
            if d <= q or val(d, q) != 1:
                continue
            m = d // q
            if len(support(m)) != 1:
                continue
            candidates += 1
            b, c = A[q], A[d] % q
            changed = dict(A)
            changed[q] = c
            changed[d] = next(x for x in range(A[d] % m, d, m) if x % q == b)
            new = prepare([(a, j) for j, a in changed.items()], False)
            legal = all(x % m == A[d] % m for x in model['private'][q])
            check(new['covering'] == legal, 'actual prime-parent no-escape condition')
            if legal:
                legal_count += 1
            if legal and new['irredundant']:
                check(m in data[q]['F'], 'legal plus resulting irredundancy forces singleton')
            if m not in data[q]['F']:
                continue
            check(legal and new['irredundant'], 'singleton implies legal rigid exchange')
            if not model['missing']:
                e = val(m, support(m)[0])
                check(e <= q - 1 - int(q * q in A), 'closed legal prime-power height bound')
            transports += 1
            permutation = [reset(x, q, c if x % q == b else b, Q)
                           if x % q in (b, c) else x for x in range(Q)]
            check(len(set(permutation)) == Q, 'whole first-root permutation')
            for x, y in enumerate(permutation):
                check(model['hits'][x] == new['hits'][y], 'every original label transported')
            for p in model['primes']:
                for x in model['private'][p]:
                    old_graph = graph(A, p, x, Q)
                    new_graph = graph(changed, p, permutation[x], Q)
                    transformed = sorted((c if root == b else b if root == c else root, d0, m0)
                                         if p == q else (root, d0, m0)
                                         for row in old_graph for root, d0, m0 in row)
                    check(transformed == sorted(e0 for row in new_graph for e0 in row),
                          'color-preserving graph isomorphism for every observing prime')
    return dict(candidates=candidates, legal=legal_count, singleton_transports=transports)


FIXTURES = (
    ('period12', ((0,2),(0,3),(1,4),(5,6),(7,12))),
    ('period144', ((0,2),(0,3),(1,4),(5,6),(7,24),(7,36),(19,48),(67,72),(91,144))),
    ('period960', ((0,2),(0,3),(3,4),(0,5),(1,8),(1,10),(13,16),(17,20),
                   (13,40),(69,160),(149,320),(469,480),(629,960))),
    ('period120', ((0,2),(0,3),(0,5),(1,6),(1,8),(1,10),(2,15),(3,20),
                   (11,24),(13,40),(29,60),(119,120))),
    ('period180', ((0,2),(0,3),(0,5),(1,4),(1,9),(1,10),(2,15),(3,20),
                   (5,18),(7,30),(7,36),(29,45),(49,90),(179,180))),
)


def affine_refinement(base):
    A, Q, pi = (base[k] for k in ('A', 'Q', 'pi'))
    check(Q == 960 and base['private'][960] == (629,), 'replacement AP entirely private')
    refined = {d: a for d, a in A.items() if d != Q}
    refined.update({Q * d: 629 + Q * a for d, a in A.items()})
    check(len(refined) == 25 and lcm(*refined) == Q * Q, 'distinct affine refined labels and full period')
    check(all(d % m and m % d or (refined[d] - refined[m]) % gcd(d, m) != 0
              for d, m in combinations(refined, 2)), 'refined comparable classes disjoint')
    # Each complete x=r+Q*t has exactly the following original membership.
    # For r!=629 it is the unchanged base row; for r=629 it is Q times
    # the base row at t. This factorization checks all Q^2 points without
    # building Q^2 large rows or assuming independent private witnesses.
    for r, hs in enumerate(base['hits']):
        if r != 629:
            check(Q not in hs and bool(hs), 'unchanged exterior whole-cover row')
        else:
            for t, inner in enumerate(base['hits']):
                x = r + Q * t
                actual = frozenset(d for d, a in refined.items() if x % d == a)
                check(actual == {Q * d for d in inner}, 'complete affine interior original labels')
    new_pi = {d: mass for d, mass in pi.items() if d != Q}
    new_pi.update({Q * d: mass / Q for d, mass in pi.items()})
    check(all(mass > 0 for mass in new_pi.values()), 'affine whole cover irredundant')
    check(sum(pi.values(), F()) == F(9, 20), 'base total private mass')
    source = tuple(r + Q * t for r in base['private'][5] for t in range(Q))
    check(len(source) == 7680, 'complete refined original prime-private source')
    model = dict(A=refined, Q=Q * Q, primes=base['primes'], pi=new_pi,
                 private={5: source}, missing=[6])
    forced = {d // 5 for d in refined if val(d, 5) == 1 and d > 5
              and sum(j % 5 == 0 and refined[j] % 5 == refined[d] % 5 for j in refined) == 1}
    check(forced == {2, 4, 8}, 'actual refined forced roots and full heights')
    data = dict(F=forced, L=8, cap=F(1, 60))
    row, selections = source_row(model, 5, data)
    check(row['alpha'] == '6/5' and row['epsilon'] == '31/19200' and row['U'] == '191/19200',
          'exact refined 363 parameters')
    check(row['old_lower'] == '107/7680' and row['forced_lower'] == '77/4608',
          'strict actual source comparison')
    check(F(row['forced_lower']) - F(row['old_lower']) == F(1, 360), 'strict forced-source gain')
    for m in (4, 8):
        count, heights = selections[m]
        beta, rho = beta_rho(base['primes'], 5, m)
        check(m in refined and heights == {1} and beta / rho * F(count, Q * Q) <= beta / (5 * m),
              'forced composite column has actual parent and valid height-one target')
    row.update(period=Q * Q, AP_count=25, full_source_points=7680,
               gain='1/360', scope='Source and two actual forced targets only; missing parents forbid full Mcomp chain.')
    return row


def main():
    output, models, data_all = [], {}, {}
    for name, aps in FIXTURES:
        model = prepare(aps)
        models[name] = model
        data = {q: singleton_data(model, q) for q in model['primes']}
        data_all[name] = data
        rows, selections = [], {}
        for q in model['primes']:
            row, selections[q] = source_row(model, q, data[q])
            rows.append(row)
        target = full_target_check(model, selections, rows) if not model['missing'] else None
        output.append(dict(name=name, period=model['Q'], AP_count=len(aps),
                           missing_divisors=model['missing'], sources=rows,
                           full_target_chain=target, swaps=swap_checks(model, data)))
    low = models['period12']
    x, y = 1, 7
    check(x % 2 == y % 2 and x % 3 == y % 3 and x % 3 in data_all['period12'][2]['R'],
          'high-digit control shares first root and full cofactor source')
    check(x % 4 == 1 and y % 4 != 1, 'first-digit shadow falsely erases q-tail distinction')
    check(data_all['period12'][3]['L'] == 4 and low['pi'][3] == F(1, 12),
          'cofactor ideal keeps modulus four rather than radical two')
    high = data_all['period960'][3]
    check(high['F'] == {160, 320} and 2 not in high['F'] and 6 not in models['period960']['A'],
          'non-divisor-closed relative ideal never invents original qn')
    check(sum(m not in models['period960']['primes'] for m in high['F']) == 2
          and len(high['F']) - len(support(high['L'])) == 0,
          'closed-palette forced-composite formula fails on nonclosed fixture')
    refinement = affine_refinement(models['period960'])
    print(json.dumps(dict(checks=CHECKS, fixtures=output, affine_refinement=refinement,
                          negative_controls=['complete q-tail', 'full cofactor exponent',
                                             'missing numerical parents', 'closure-dependent composite count'],
                          scope='Finite exact checks on whole even covers; no odd-cover contradiction or Lean verification.'),
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
