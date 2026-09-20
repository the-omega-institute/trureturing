#!/usr/bin/env python3
"""Exact shallow-tail truncation and same-source matching-budget checks.

Local sharp prefix models are not whole integer covers. Actual AP fixtures
are whole even covers, with literal original labels and complete CRT tails.
Only divisor-closed fixtures test the complete composite-target chain; the
affine fixture tests its q=5 source estimates only. A separate actual control
refutes a pointwise-alpha substitution in an individual column capacity.
Standard library only, no repository imports, and checks remain active -O.
No Lean verification, odd-cover counterexample or general resolution claimed.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import gcd, lcm, prod
import json


COUNTS = Counter()


def check(condition, message):
    COUNTS['checks'] += 1
    if not condition:
        raise ArithmeticError(message)


@lru_cache(None)
def factor(n):
    answer = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            answer.append((p, e))
        p += 1
    if n > 1:
        answer.append((n, 1))
    return tuple(answer)


def height(n, q):
    return dict(factor(n)).get(q, 0)


def phi(n):
    return prod(p ** (e - 1) * (p - 1) for p, e in factor(n))


def divisors(n):
    answer = [1]
    for p, e in factor(n):
        answer = [d * p ** j for d in answer for j in range(e + 1)]
    return answer


def crt(a, u, b, v):
    return (a + u * ((b - a) * pow(u, -1, v) % v)) % (u * v) if v > 1 else a % u


def set_root(x, q, root, Q):
    power = q ** height(Q, q)
    return crt(x % power - x % q + root, power, x % (Q // power), Q // power)


def literal_hits(A, x):
    return frozenset(d for d, a in A.items() if x % d == a)


def inventory(A):
    check(all(d > 1 and 0 <= a < d for d, a in A.items()), 'invalid original AP')
    Q = lcm(*A)
    primes = tuple(p for p, _ in factor(Q))
    check(all(p in A for p in primes), 'original prime label missing')
    for d, m in combinations(A, 2):
        if d % m == 0 or m % d == 0:
            check((A[d] - A[m]) % gcd(d, m) != 0, 'comparable original APs intersect')
            COUNTS['comparable_pairs'] += 1
    missing = sorted({e for d in A for e in divisors(d) if e > 1 and e not in A})
    return Q, primes, missing


def prepare(name, aps):
    A = dict(sorted((d, a) for a, d in aps))
    check(len(A) == len(aps), 'original moduli repeated')
    Q, primes, missing = inventory(A)
    hits = tuple(literal_hits(A, x) for x in range(Q))
    COUNTS['literal_full_period_points'] += Q
    check(all(hits), 'actual AP fixture is not a whole cover')
    private = {d: tuple(x for x, labels in enumerate(hits) if labels == {d}) for d in A}
    check(all(private.values()), 'original AP has no private point')
    return dict(name=name, A=A, Q=Q, primes=primes, missing=missing, hits=hits,
                hit=lambda x: hits[x % Q], private=private,
                pi={d: F(len(xs), Q) for d, xs in private.items()})


# Labels are (root, actual cofactor/color, exponent e, tail prefix, original id).
# Color 1 is pure. The id is a literal modulus in an actual AP fixture.
def compatible_labels(A, q, x):
    labels = []
    for d, a in A.items():
        e = height(d, q)
        if not e or d == q:
            continue
        m = d // q ** e
        if x % m == a % m:
            labels.append((a % q, m, e, (a % q ** e) // q, d))
    return tuple(sorted(labels))


def local_cut(q, H, roots, labels):
    check(len(roots) == q - 1, 'wrong nonprime root count')
    check(len({(m, e) for _, m, e, _, _ in labels}) == len(labels),
          'a numerical column repeats at one exponent')
    check(all(r in roots and 1 <= e <= H and 0 <= a < q ** (e - 1)
              for r, _, e, a, _ in labels), 'invalid original prefix')
    check(not any(m == 1 and e == 1 for _, m, e, _, _ in labels),
          'pure color occurs on a nonprime depth-zero root')
    heights = {}
    for _, m, e, _, _ in labels:
        if m != 1:
            heights[m] = max(heights.get(m, 0), e)
    check(len(heights) >= q - 1, 'not enough compatible nonpure colors')
    L = sorted(heights.values(), reverse=True)[q - 2]
    check(1 <= L <= H and sum(e > L for e in heights.values()) <= q - 2,
          'height order statistic or late color budget changed')
    late_weight = (q - 1) * sum((F(1, q ** (e - L)) for e in range(L + 1, H + 1)), F())
    check(late_weight == 1 - F(1, q ** (H - L)) < 1, 'strict late-prefix mass bound')
    return L


def active_rows(q, roots, labels, t, cutoff):
    return tuple(tuple(label for label in labels
                       if label[0] == root and label[2] <= cutoff
                       and t % q ** (label[2] - 1) == label[3]) for root in roots)


@lru_cache(None)
def choose_matching(roots, rows, forced):
    """Maximum rank by augmentation, independently checked by every Hall cut."""
    COUNTS['distinct_matching_graphs'] += 1
    graph = {root: tuple(sorted({a[1] for a in row if a[1] != 1}))
             for root, row in zip(roots, rows)}
    owner = {}

    def augment(root, seen):
        for color in graph[root]:
            if color in seen:
                continue
            seen.add(color)
            if color not in owner or augment(owner[color], seen):
                owner[color] = root
                return True
        return False

    for root in roots:
        augment(root, set())
    selected = []
    for color, root in owner.items():
        row = rows[roots.index(root)]
        selected.append(min((a for a in row if a[1] == color), key=lambda a: (a[2], a[4])))
    rank = len(selected)
    deficiency = 0
    for size in range(len(roots) + 1):
        for subset in combinations(roots, size):
            neighbors = set().union(*(set(graph[root]) for root in subset))
            deficiency = max(deficiency, size - len(neighbors))
            COUNTS['hall_subsets'] += 1
    check(rank == len(roots) - deficiency, 'augmenting rank disagrees with Hall cuts')
    colors = {a[1] for a in selected}
    check(set(forced) <= colors, 'maximum matching omits a forced color')
    selected = [a for a in selected if a[1] not in forced]
    for color in forced:
        candidates = [a for row in rows for a in row if a[1] == color and a[2] == 1]
        check(len(candidates) == 1, 'forced color lacks its unique original height-one edge')
        selected.extend(candidates)
    check(len(selected) == rank and len({a[0] for a in selected}) == rank,
          'forced relocation changes rank or repeats a root')
    check({a[1] for a in selected} == colors, 'forced relocation changes the color set')
    return tuple(sorted(selected))


def sharp_model(q, L, H):
    roots = tuple(range(q - 1))
    last = q - 2
    labels = []

    def add(root, color, e, prefix):
        labels.append((root, color, e, prefix, len(labels) + 1))

    for root in range(q - 2):
        add(root, root + 2, 1, 0)
    for depth in range(1, L):
        for branch, color in enumerate(tuple(range(2, q)) + (1,)):
            add(last, color, depth + 1, q ** (depth - 1) - 1 + branch * q ** (depth - 1))
    add(last, q, L, q ** (L - 1) - 1)
    if H > L:
        add(last, 1, H, 0)
        if q >= 3:
            add(roots[0], 2, H, 0)
    labels = tuple(labels)
    check(local_cut(q, H, roots, labels) == L, 'added high columns changed the cut')
    low_total = full_total = 0
    for t in range(q ** (H - 1)):
        full = active_rows(q, roots, labels, t, H)
        low = active_rows(q, roots, labels, t, L)
        check(all(full) and all(low), 'full-node truncation failed in local model')
        full_match = choose_matching(roots, full, ())
        low_match = choose_matching(roots, low, ())
        check(all(a in labels and a[2] <= L for a in low_match), 'invented shallow matching edge')
        low_total += len(low_match)
        full_total += len(full_match)
        COUNTS['local_full_tail_points'] += 1
        COUNTS['local_truncated_root_checks'] += len(roots)
    mean = F(low_total, q ** (H - 1))
    old = q - 2 + F(1, q ** (H - 1))
    new = q - 2 + F(1, q ** (L - 1))
    check(mean == F(full_total, q ** (H - 1)) == new >= old, 'local sharp mean mismatch')
    witness = q ** (L - 1) - 1
    too_shallow = active_rows(q, roots, labels, witness, L - 1)
    check(not too_shallow[-1], 'cut L-1 must leave the terminal root uncovered')
    COUNTS['local_sharp_models'] += 1
    return dict(q=q, L=L, H=H, labels=len(labels), tail_points=q ** (H - 1),
                old_lower=str(old), new_lower=str(new), mean_rank=str(mean),
                high_pure_added=H > L, high_nonpure_added=H > L and q >= 3,
                cutoff_L_minus_one_failure=dict(root=last, tail=witness))


def beta_rho(primes, q, m):
    free = tuple(p for p in primes if p != q and m % p)
    rho = prod((F(p - 1, p) for p in free), start=F(1))
    beta = F()
    for mask in product((False, True), repeat=len(free)):
        probability = prod((F(1, p) if present else F(p - 1, p)
                            for p, present in zip(free, mask)), start=F(1))
        beta += probability / (1 + int(m in primes) + sum(mask))
    return beta, rho


def analyze_source(model, q):
    A, Q, primes, pi = (model[k] for k in ('A', 'Q', 'primes', 'pi'))
    H = height(Q, q)
    power, tails = q ** H, q ** (H - 1)
    B = Q // power
    roots = tuple(r for r in range(q) if r != A[q] % q)
    R = tuple(x for x in range(B) if all(x % d != a for d, a in A.items() if d % q))
    check(bool(R) and F(len(R) * tails, Q) == pi[q], 'complete original private-source product')
    forced = []
    for root in roots:
        ds = [d for d in A if d % q == 0 and A[d] % q == root]
        if len(ds) == 1:
            d = ds[0]
            check(height(d, q) == 1 and d > q, 'singleton root is not a height-one mixed child')
            forced.append(d // q)
    forced = tuple(sorted(forced))
    f = sum(m not in primes for m in forced)
    global_heights = {}
    for d in A:
        e = height(d, q)
        if e and d > q ** e:
            m = d // q ** e
            global_heights[m] = max(global_heights.get(m, 0), e)
    Lstar = sorted(global_heights.values(), reverse=True)[q - 2]
    check(Lstar == H, 'whole irredundant inventory fails the known top-height cut')
    cuts, histogram = {}, Counter()
    selected = defaultdict(lambda: [0, set()])
    low_rank_total = full_rank_total = prime_count = composite_count = 0
    new_lower_sum = F()
    source_points = set()
    for x in R:
        labels = compatible_labels(A, q, x)
        L = local_cut(q, H, roots, labels)
        cuts[x] = L
        histogram[L] += 1
        local_low = local_full = 0
        for t in range(tails):
            y = crt(A[q] % q + q * t, power, x, B)
            check(model['hit'](y) == {q}, 'enumerated cofactor-tail is not actual prime-private')
            source_points.add(y)
            full = active_rows(q, roots, labels, t, H)
            low = active_rows(q, roots, labels, t, L)
            for root, complete, truncated in zip(roots, full, low):
                z = crt(root + q * t, power, x, B)
                actual = literal_hits(A, z)
                check({a[4] for a in complete} == actual == model['hit'](z),
                      'prefix label graph differs from literal original AP membership')
                check(bool(complete) and bool(truncated), 'a full original root loses coverage after truncation')
                if len(actual) == 1:
                    d = next(iter(actual))
                    check(height(d, q) <= L, 'original private point below its necessary cofactor cut')
                COUNTS['actual_truncated_root_checks'] += 1
            complete_match = choose_matching(roots, full, ())
            shallow_match = choose_matching(roots, low, forced)
            check(all(a in labels and a[2] <= L for a in shallow_match), 'selected edge lost original provenance')
            check(len(shallow_match) <= len(complete_match), 'truncation increased maximum rank')
            local_full += len(complete_match)
            local_low += len(shallow_match)
            for _, m, e, _, d in shallow_match:
                check(d == q ** e * m and m > 1, 'selected cofactor or exponent is not original')
                selected[m][0] += 1
                selected[m][1].add(e)
                prime_count += m in primes
                composite_count += m not in primes
            COUNTS['actual_source_tail_points'] += 1
        old = q - 2 + F(1, q ** (H - 1))
        new = q - 2 + F(1, q ** (L - 1))
        check(F(local_low, tails) >= new >= old and F(local_full, tails) >= old,
              'complete uniform-tail mean bound failed')
        low_rank_total += local_low
        full_rank_total += local_full
        new_lower_sum += new
        COUNTS['actual_cofactor_models'] += 1
    check(len(source_points) == len(R) * tails and source_points == set(model['private'][q]),
          'actual source enumeration omitted or duplicated a full-tail point')
    old_r = q - 2 + F(1, q ** (H - 1))
    new_r = new_lower_sum / len(R)
    delta = new_r - (q - 2)
    gain_identity = (q - 1) * sum((F(sum(n for L, n in histogram.items() if L <= h), len(R) * q ** h)
                                  for h in range(1, H)), F())
    check(new_r - old_r == gain_identity >= 0, 'adaptive cofactor-threshold gain identity')
    alpha = F(q, q - 1) * (1 - F(1, q ** H))
    P0 = prod((F(p - 1, p) for p in primes), start=F(1))
    eligible = [d for d in A if height(d, q) and d // q ** height(d, q) in primes]
    u = sum((pi[d] for d in eligible), F())
    epsilon = (q - 1) * pi[q] - sum((pi[d] for d in A if d != q and d % q == 0), F())
    deltaF = sum((P0 / phi(d) - pi[d] for d in eligible), F())
    U = min((len(primes) - 1) * pi[q], u + min(epsilon, deltaF))
    P, C = F(prime_count, Q), F(composite_count, Q)
    check(epsilon >= 0 and deltaF >= 0 and P <= U, 'same-source 363 prime-parent upper bound')
    check(P + C == F(low_rank_total, Q) >= new_r * pi[q], 'adaptive source-rank integral')
    check(C >= f * pi[q], 'forced composite edges did not cover the whole source')
    old_lower = max(F(), old_r * pi[q] - U) / alpha
    new_lower = max(F(), new_r * pi[q] - U) / alpha
    old_forced = f * pi[q] + max(F(), (old_r - f) * pi[q] - U) / alpha
    new_forced = f * pi[q] + max(F(), (new_r - f) * pi[q] - U) / alpha
    strengthened = C / alpha + (1 - 1 / alpha) * f * pi[q]
    check(old_lower <= new_lower <= new_forced <= strengthened and old_forced <= new_forced,
          'adaptive 363/364 lower bound changed source or denominator')
    for m, (count, used) in selected.items():
        beta, rho = beta_rho(primes, q, m)
        used_alpha = sum((F(q, q ** e) for e in used), F())
        check(F(count, Q) <= used_alpha * rho / (q * m), 'actual selected-column containing bound')
        if m in forced:
            check(count == len(source_points) and used == {1} and used_alpha == 1,
                  'forced relocation lost complete source or height one')
        COUNTS['selected_original_columns'] += 1
    COUNTS['actual_prime_sources'] += 1
    row = dict(q=q, H=H, Lstar=Lstar, cofactor_states=len(R), full_tail_points=tails,
               private_source_points=len(source_points), pi=str(pi[q]),
               L_distribution=dict(sorted(histogram.items())), adaptive_delta=str(delta),
               old_r=str(old_r), adaptive_rbar=str(new_r), rbar_gain=str(new_r - old_r),
               full_mean_rank=str(F(full_rank_total, len(source_points))),
               truncated_mean_rank=str(F(low_rank_total, len(source_points))),
               full_H_rank_integral=str(F(full_rank_total, Q)),
               truncated_H_rank_integral=str(P + C), old_H_lower=str(old_r * pi[q]),
               adaptive_H_lower=str(new_r * pi[q]), alpha_original_height=str(alpha),
               forced_cofactors=list(forced), forced_composite_count=f,
               epsilon=str(epsilon), u=str(u), Delta_F=str(deltaF), U=str(U), P=str(P), C=str(C),
               old_363_lower=str(old_lower), adaptive_363_lower=str(new_lower),
               old_364_lower=str(old_forced), adaptive_364_lower=str(new_forced),
               adaptive_364_gain=str(new_forced - old_forced),
               strengthened_selected_source=str(strengthened),
               selected_missing_parents=sorted(m for m in selected if m not in A))
    return row, selected, cuts


def complete_target_chain(model, rows, selections):
    A, Q, primes = (model[k] for k in ('A', 'Q', 'primes'))
    check(not model['missing'], 'full target chain requested without divisor closure')
    source_charge = target_charge = F()
    allocation = [F() for _ in range(Q)]
    for q, columns in selections.items():
        for m, (count, used) in columns.items():
            if m in primes:
                continue
            check(m in A, 'selected composite parent is not an original AP')
            beta, rho = beta_rho(primes, q, m)
            used_alpha = sum((F(q, q ** e) for e in used), F())
            capacity = F()
            for z, hits in enumerate(model['hits']):
                if q in hits and m in hits:
                    weight = F(1, len(hits.intersection(primes)))
                    allocation[z] += weight
                    capacity += weight / Q
            check(capacity == beta / (q * m), 'actual 1/k target capacity differs from CRT formula')
            charge = beta * F(count, Q) / (used_alpha * rho)
            check(charge <= capacity and beta >= rho, 'source-to-original-composite-target charge')
            source_charge += charge
            target_charge += capacity
    for amount, hits in zip(allocation, model['hits']):
        check(amount <= sum(d not in primes for d in hits) * bool(hits.intersection(primes)),
              'composite target allocation reuses an original capacity')
    M = sum((F(1, d) * (1 - prod((F(p - 1, p) for p in primes if d % p), start=F(1)))
             for d in A if d not in primes), F())
    actual_M = F(sum(sum(d not in primes for d in hits) * bool(hits.intersection(primes))
                     for hits in model['hits']), Q)
    lower = sum((F(row['adaptive_364_lower']) for row in rows), F())
    strengthened = sum((F(row['strengthened_selected_source']) for row in rows), F())
    check(M == actual_M and lower <= strengthened <= source_charge <= target_charge <= M,
          'complete adaptive source/target/Mcomp chain')
    COUNTS['complete_target_fixtures'] += 1
    return dict(adaptive_combined_lower=str(lower), strengthened_selected_source=str(strengthened),
                used_height_source_charge=str(source_charge), allocated_target_charge=str(target_charge),
                Mcomp=str(M))


FIXTURES = (
    ('period12', ((0, 2), (0, 3), (1, 4), (5, 6), (7, 12))),
    ('period144', ((0, 2), (0, 3), (1, 4), (5, 6), (7, 24), (7, 36), (19, 48), (67, 72), (91, 144))),
    ('period960', ((0, 2), (0, 3), (3, 4), (0, 5), (1, 8), (1, 10), (13, 16), (17, 20),
                   (13, 40), (69, 160), (149, 320), (469, 480), (629, 960))),
    ('period120', ((0, 2), (0, 3), (0, 5), (1, 6), (1, 8), (1, 10), (2, 15), (3, 20),
                   (11, 24), (13, 40), (29, 60), (119, 120))),
    ('period180', ((0, 2), (0, 3), (0, 5), (1, 4), (1, 9), (1, 10), (2, 15), (3, 20),
                   (5, 18), (7, 30), (7, 36), (29, 45), (49, 90), (179, 180))),
    ('period60', ((0, 2), (0, 3), (3, 4), (0, 5), (5, 6), (7, 10), (13, 15), (9, 20), (1, 30))),
    ('period450', ((0, 2), (0, 3), (0, 5), (5, 6), (4, 9), (9, 10), (7, 15),
                   (11, 25), (13, 30), (1, 45), (31, 50), (46, 75), (1, 150), (16, 225))),
)


def pointwise_alpha_control(model, cuts):
    A, Q = model['A'], model['Q']
    check(Q == 60 and not model['missing'], 'wrong pointwise-alpha control fixture')
    q, m, B = 2, 5, 15
    check(set(cuts) == {1, 2, 4, 7, 8, 11, 14}, 'actual R2 control changed')
    check({x for x, L in cuts.items() if L == 2} == {4, 14}, 'actual adaptive cuts changed')
    sources = {}
    weighted = F()
    for e in (1, 2):
        d = q ** e * m
        points = {y for y in model['private'][q]
                  if set_root(y, q, A[d] % q, Q) % d == A[d]}
        expected = {2, 22, 32, 52} if e == 1 else {4, 44}
        check(points == expected, 'literal selected child source changed')
        for y in points:
            L = cuts[y % B]
            check(e <= L and L == e, 'control selected edge exceeds its actual adaptive cut')
            labels = compatible_labels(A, q, y % B)
            rows = active_rows(q, (1,), labels, (y % 4) // 2, L)
            check(len(choose_matching((1,), rows, ())) == 1, 'control choice is not a maximum-rank edge')
            alphaL = F(q, q - 1) * (1 - F(1, q ** L))
            weighted += F(1, Q) / alphaL
        sources[e] = sorted(points)
    check(set(sources[1]).isdisjoint(sources[2]), 'control reuses a source point')
    _, rho = beta_rho(model['primes'], q, m)
    capacity = rho / (q * m)
    mass = F(sum(map(len, sources.values())), Q)
    alphaH = F(3, 2)
    check(weighted == F(4, 45) > capacity == F(1, 15), 'pointwise-alpha control does not refute the column inequality')
    check(weighted - capacity == F(1, 45) and mass / alphaH == capacity,
          'original-height denominator must retain the valid column capacity')
    return dict(period=Q, q=q, parent=m, child_source_sets=sources,
                pointwise_alpha_weighted_mass=str(weighted), column_capacity=str(capacity),
                excess=str(weighted - capacity), original_H_alpha=str(alphaH),
                valid_original_H_weighted_mass=str(mass / alphaH),
                scope='Refutes the pointwise-alpha substitution for one actual column only; no all-prime aggregate or odd-cover claim.')


def affine_model(base):
    A, Q = base['A'], base['Q']
    check(Q == 960 and base['private'][Q] == (629,), 'affine replaced class is not entirely private')
    refined = dict((d, a) for d, a in A.items() if d != Q)
    refined.update((Q * d, 629 + Q * a) for d, a in A.items())
    newQ, primes, missing = inventory(refined)
    check(len(refined) == 25 and newQ == Q * Q, 'wrong affine modulus inventory')
    check(all(Q % d == 0 for d in A), 'exterior labels do not divide the base period')
    check(all(d % Q == 0 and a % Q == 629 for d, a in refined.items() if d >= 2 * Q),
          'affine labels can escape the replaced base class')
    for r, old in enumerate(base['hits']):
        if r != 629:
            check(Q not in old and old == literal_hits(refined, r) and bool(old),
                  'factorized exterior membership changed')
            COUNTS['affine_exterior_rows'] += 1
        else:
            for t, inner in enumerate(base['hits']):
                check(literal_hits(refined, r + Q * t) == {Q * d for d in inner} and bool(inner),
                      'factorized affine interior membership changed')
                COUNTS['affine_interior_rows'] += 1

    def hits(x):
        r, t = x % Q, (x // Q) % Q
        return base['hits'][r] if r != 629 else frozenset(Q * d for d in base['hits'][t])

    pi = {d: mass for d, mass in base['pi'].items() if d != Q}
    pi.update({Q * d: mass / Q for d, mass in base['pi'].items()})
    for d in refined:
        witness = base['private'][d][0] if d < Q else 629 + Q * base['private'][d // Q][0]
        check(pi[d] > 0 and hits(witness) == literal_hits(refined, witness) == {d},
              'affine original lacks its literal private witness')
    source = tuple(r + Q * t for r in base['private'][5] for t in range(Q))
    check(len(source) == 7680 and bool(missing), 'affine source or missing-parent scope changed')
    return dict(name='affine921600', A=refined, Q=newQ, primes=primes, missing=missing,
                hit=hits, private={5: source}, pi=pi)


def main():
    local = [sharp_model(q, L, H) for q in (2, 3, 5, 7)
             for L in (1, 2, 3) for H in (L, L + 1)]
    actual, models, all_cuts = [], {}, {}
    for name, aps in FIXTURES:
        model = prepare(name, aps)
        models[name] = model
        rows, selections, cuts = [], {}, {}
        for q in model['primes']:
            row, selections[q], cuts[q] = analyze_source(model, q)
            rows.append(row)
        all_cuts[name] = cuts
        target = complete_target_chain(model, rows, selections) if not model['missing'] else None
        if name == 'period450':
            old = sum((F(row['old_364_lower']) for row in rows), F())
            new = sum((F(row['adaptive_364_lower']) for row in rows), F())
            check(old == F(71, 1350) and new == F(2, 25) and new - old == F(37, 1350),
                  'period450 strict complete-budget gain changed')
            check(target is not None and target['Mcomp'] == '11/50',
                  'period450 needs its complete original target chain')
        actual.append(dict(name=name, period=model['Q'], AP_count=len(aps),
                           missing_divisors=model['missing'], sources=rows, complete_target_chain=target))
    negative = pointwise_alpha_control(models['period60'], all_cuts['period60'][2])
    refined = affine_model(models['period960'])
    affine_row, _, _ = analyze_source(refined, 5)
    check(affine_row['alpha_original_height'] == '6/5' and affine_row['U'] == '191/19200',
          'affine original-height alpha or original 363 upper changed')
    check(F(affine_row['rbar_gain']) > 0 and F(affine_row['adaptive_364_gain']) > 0,
          'affine source must exhibit strict adaptive improvement')
    affine_row.update(period=refined['Q'], AP_count=len(refined['A']),
                      missing_divisors=refined['missing'], complete_target_chain=None,
                      scope='Actual complete q=5 cofactor/tail source only; missing parents forbid a full Mcomp chain.')
    output = dict(
        scope='Exact finite prefix and original-AP checks. Local sharp models are not whole covers; actual covers are even. No Lean verification or unrestricted odd-cover conclusion.',
        counters=dict(sorted(COUNTS.items())), local_sharp_models=local,
        actual_cover_fixtures=actual, affine_q5_source=affine_row,
        pointwise_alpha_negative_control=negative)
    print(json.dumps(output, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
