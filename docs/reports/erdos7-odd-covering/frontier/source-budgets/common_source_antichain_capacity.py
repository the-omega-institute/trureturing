#!/usr/bin/env python3
"""Exact common-source antichains and selected-cofactor capacity checks.

All AP fixtures are even covers. Their source matchings use actual children
and distinct numerical cofactors; missing original parents are reported,
and no full target-budget claim is made for those fixtures. The additional
rational profile separates only the enumerated scalar inequalities and has
no asserted AP realization. Standard library only; checks survive -O.
"""
from collections import Counter
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
    answer = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            answer.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        answer.append(n)
    return tuple(answer)


def valuation(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def phi(n):
    return prod((p - 1) * p ** (valuation(n, p) - 1) for p in support(n))


def subsets(items, minimum=0):
    return (part for size in range(minimum, len(items) + 1)
            for part in combinations(items, size))


def changed_root(z, q, root, period):
    power = q ** valuation(period, q)
    other = period // power
    target = z % power - z % q + root
    result = (z + other * ((target - z) * pow(other, -1, power) % power)) % period
    check(result % q == root, 'new first root')
    check((result % power) // q == (z % power) // q, 'complete tail preserved')
    check(result % other == z % other, 'other prime coordinates preserved')
    return result


def common_core(labels):
    check(bool(labels), 'whole cover needed for nonempty active family')
    return set.intersection(*(set(support(d)) for d in labels))


def maximum_selection(options):
    best = ()
    for choices in product(*options):
        chosen = tuple(item for item in choices if item is not None)
        if len({m for _, m in chosen}) == len(chosen) and len(chosen) > len(best):
            best = chosen
    return best


def fixture(name, aps):
    residues = {d: a for a, d in aps}
    check(len(residues) == len(aps), 'distinct original moduli')
    check(all(d > 1 and 0 <= a < d for a, d in aps), 'proper original APs')
    period = lcm(*residues)
    primes = support(period)
    composites = tuple(d for d in residues if d not in primes)
    check(all(q in residues for q in primes), 'all original primes present')
    for (a, d), (b, m) in combinations(aps, 2):
        if d % m == 0 or m % d == 0:
            check((a - b) % gcd(d, m) != 0, 'comparable original classes disjoint')
    memberships = [frozenset(d for a, d in aps if (z - a) % d == 0)
                   for z in range(period)]
    check(all(memberships), 'whole-period coverage')
    base = tuple(z for z, labels in enumerate(memberships) if labels.isdisjoint(primes))
    P0 = prod(F(q - 1, q) for q in primes)
    check(F(len(base), period) == P0, 'original no-prime Haar mass')
    antichains = Counter(memberships[z] for z in base)
    core = {z: common_core(memberships[z]) for z in base}
    private = {d: F(sum(labels == {d} for labels in memberships), period) for d in residues}
    capacity = {d: P0 / phi(d) for d in composites}
    delta = {d: capacity[d] - private[d] for d in composites}
    rho = P0 - sum((private[d] for d in composites), F())
    v = sum(capacity.values(), F()) - P0
    residual_points = tuple(z for z in base if len(memberships[z]) >= 2)
    check(rho == F(len(residual_points), period), 'same nonprivate carrier')
    check(v - rho == sum((F(max(len(memberships[z]) - 2, 0), period) for z in base), F()),
          'multiplicity gap identity')
    check(sum(delta.values(), F()) == rho + v, 'residual degree sum')
    for labels in antichains:
        check(all(d % e and e % d for d, e in combinations(labels, 2)), 'actual active antichain')
    for d in composites:
        check(capacity[d] == F(sum(d in memberships[z] for z in base), period), 'literal cap_d')
        check(delta[d] == F(sum(d in memberships[z] for z in residual_points), period),
              'common residual label incidence')
    epsilon = {}
    for q in primes:
        epsilon[q] = (q - 1) * private[q] - sum((private[d] for d in composites if d % q == 0), F())
        check((q - 1) * private[q] == F(sum(q in core[z] for z in base), period),
              'prime-private reset fibre multiplicity')
        check(epsilon[q] == F(sum(q in core[z] for z in residual_points), period),
              'same residual common-support incidence')
        delta_q = sum((delta[d] for d in composites if d % q == 0), F())
        check(0 <= epsilon[q] <= rho and 2 * epsilon[q] <= delta_q,
              'joint residual budgets')
    reset_count = 0
    for ss in subsets(primes):
        ss_set = set(ss)
        fibres = Counter()
        zero_composites = 0
        composite_incidence = 0
        for z in base:
            y = z
            for q in ss:
                y = changed_root(y, q, residues[q] % q, period)
            expected = {d for d in memberships[z] if all(d % q for q in ss)}
            actual = set(memberships[y]).difference(primes)
            check(actual == expected, 'same active labels under every reset pattern')
            check(set(memberships[y]).intersection(primes) == ss_set, 'exact prime pattern')
            zero_composites += not actual
            composite_incidence += len(actual)
            fibres[y] += 1
            reset_count += 1
        multiplier = prod(q - 1 for q in ss)
        pattern = {z for z, labels in enumerate(memberships) if labels.intersection(primes) == ss_set}
        check(set(fibres) == pattern and all(n == multiplier for n in fibres.values()),
              'uniform complete reset fibre size')
        exact_prime_only = sum(labels == ss_set for labels in memberships)
        check(zero_composites == multiplier * exact_prime_only, 'hitting event equals V_S pullback')
        check(composite_incidence == multiplier * sum(len(memberships[z].difference(primes)) for z in pattern),
              'same pattern composite incidence')
    pair_rows = []
    if rho == v:
        check(all(len(labels) <= 2 for labels in antichains), 'saturation leaves only singleton/pair patterns')
        for labels, count in antichains.items():
            if len(labels) != 2:
                continue
            d, e = sorted(labels)
            weight = F(count, period)
            check(d % e and e % d, 'actual pair is incomparable')
            check((residues[d] - residues[e]) % gcd(d, e) == 0, 'actual pair is CRT compatible')
            check(weight == P0 / phi(lcm(d, e)), 'pair-only residual retains exact CRT mass')
            pair_rows.append(dict(labels=[d, e], mass=str(weight)))
        check(sum((F(row['mass']) for row in pair_rows), F()) == v, 'one shared pair budget')
    rows = []
    for q in primes:
        height = valuation(period, q)
        r_q = q - 2 + F(1, q ** (height - 1))
        family = tuple(d for d in composites if d % q == 0 and d // q ** valuation(d, q) in primes)
        u_q = sum((private[d] for d in family), F())
        delta_F = sum((delta[d] for d in family), F())
        old_cap = sum((capacity[d] for d in family), F())
        old_size = (len(primes) - 1) * private[q]
        refined = u_q + min(epsilon[q], delta_F)
        upper = min(old_size, refined)
        source_prime = 0
        source_composite = 0
        lifted_prime = {}
        lifted_composite = {}
        for y, labels in enumerate(memberships):
            if labels != {q}:
                continue
            options = []
            for root in range(q):
                if root == residues[q] % q:
                    continue
                x = changed_root(y, q, root, period)
                choices = [None]
                for d in sorted(memberships[x]):
                    e = valuation(d, q)
                    m = d // q ** e
                    if e and m > 1:
                        choices.append((d, m))
                options.append(choices)
            chosen = maximum_selection(options)
            for d, m in chosen:
                x = changed_root(y, q, residues[d] % q, period)
                check(x in core and q in core[x] and d in memberships[x], 'selected edge on its actual base fibre')
                check(x not in lifted_prime and x not in lifted_composite, 'one selected child per q-root')
                if m in primes:
                    source_prime += 1
                    lifted_prime[x] = d
                    check(d in family, 'prime-parent lift has eligible original child')
                else:
                    source_composite += 1
                    lifted_composite[x] = d
        P = F(source_prime, period)
        C = F(source_composite, period)
        check(P == F(len(lifted_prime), period) and C == F(len(lifted_composite), period),
              'selection lift preserves original Haar mass')
        single_prime_lifts = sum(len(memberships[x]) == 1 for x in lifted_prime)
        residual_prime_lifts = len(lifted_prime) - single_prime_lifts
        check(F(single_prime_lifts, period) <= u_q, 'singleton prime-parent budget')
        check(F(residual_prime_lifts, period) <= min(epsilon[q], delta_F), 'same residual selection budget')
        check(P <= upper <= min(old_size, old_cap), 'strictly refined prime-parent estimate')
        check(P + C >= r_q * private[q], 'whole-private full-tail mean rank')
        old_lower = max(F(), r_q - len(primes) + 1) * private[q]
        lower = max(F(), r_q * private[q] - upper)
        check(old_lower <= lower <= C, 'new composite-cofactor lower bound')
        rows.append(dict(q=q, height=height, pi=str(private[q]), eligible_children=family,
                         epsilon=str(epsilon[q]), u=str(u_q), delta_F=str(delta_F),
                         size_upper=str(old_size), label_capacity_upper=str(old_cap),
                         refined_upper=str(upper), prime_selection=str(P), composite_selection=str(C),
                         old_composite_lower=str(old_lower), new_composite_lower=str(lower)))
    missing = sorted({d // q ** valuation(d, q) for d in residues for q in primes
                      if valuation(d, q) and d // q ** valuation(d, q) > 1
                      and d // q ** valuation(d, q) not in residues})
    if period == 960:
        row = next(row for row in rows if row['q'] == 5)
        check(F(row['refined_upper']) == F(3, 320) < min(F(row['size_upper']), F(row['label_capacity_upper'])),
              'strict source refinement at q=5')
        check(F(row['new_composite_lower']) == F(23, 960) and F(row['composite_selection']) == F(1, 40),
              'literal improved lower bound and actual selection')
        fake_P = fake_C = F(1, 60)
        check(fake_P <= min(F(row['size_upper']), F(row['label_capacity_upper']))
              and fake_P + fake_C == 4 * F(row['pi']) and fake_P > F(row['refined_upper']),
              'residual marginals alone do not constrain a newly introduced selection variable')
    return dict(name=name, period=period, AP_count=len(aps), no_prime_points=len(base),
                reset_point_patterns=reset_count, distinct_active_antichains=len(antichains),
                P0=str(P0), rho=str(rho), v=str(v), higher_multiplicity_gap=str(v - rho),
                saturated_pairs=pair_rows, missing_original_parents=missing,
                source_rows=rows, scope='Actual-child source checks; no full target-budget assertion.')


def scalar_separator():
    """The listed scalar family is feasible; the common-source residual is not."""
    primes = (3, 5, 7, 11, 13, 17)
    D = sorted(prod(p ** e for p, e in zip(primes, es))
               for es in product(range(3), repeat=len(primes)) if any(es))
    composites = tuple(d for d in D if d not in primes)
    check(len(D) == len(set(D)) == 728 and all(d % 2 for d in D), 'distinct odd divisor palette')
    for d in D:
        for p in primes:
            if d % p == 0 and d != p:
                check(d // p in D, 'palette divisor closure')
    check(all(max(valuation(d, p) for d in D) == 2 for p in primes), 'full height two')
    P0 = prod(F(p - 1, p) for p in primes)
    h = sum((F(1, d) for d in D), F()) - 1
    J = sum((F(1, p) for p in primes), F()) - 1 + P0
    cap = {d: P0 / phi(d) for d in composites}
    v = sum(cap.values(), F()) - P0
    Mcomp = sum((F(1, d) * (1 - prod((F(p - 1, p) for p in primes if d % p), start=F(1)))
                 for d in composites), F())
    check(Mcomp == h - J - v and v >= 0 and h >= J, 'same palette budgets')
    group5 = {d for d in composites if d % 5 == 0 and d % 7}
    group7 = {d for d in composites if d % 7 == 0 and d % 5}
    A5 = sum((cap[d] for d in group5), F())
    A7 = sum((cap[d] for d in group7), F())
    check(group5.isdisjoint(group7) and min(A5, A7) >= v, 'same two admissible removal groups')
    pi_comp = {d: cap[d] * (1 - (v / A5 if d in group5 else v / A7 if d in group7 else 0))
               for d in composites}
    mu = {p: P0 / (p - 1) for p in primes}
    lower = {p: mu[p] * max(F(), 1 - sum((F(1, phi(d)) for d in composites if d % p), F())) for p in primes}
    upper = {p: mu[p] * (1 - max(F(1, phi(d)) for d in composites if d % p)) for p in primes}
    pi = {p: lower[p] for p in primes}
    pi[11] = sum((pi_comp[d] for d in composites if d % 11 == 0), F()) / 10
    pi[13] = sum((pi_comp[d] for d in composites if d % 13 == 0), F()) / 12
    pi[17] = F(1, 100)
    for d in composites:
        check(max(F(), cap[d] - v) <= pi_comp[d] <= cap[d] <= F(1, d), 'old per-label regional bounds')
    comp_total = sum(pi_comp.values(), F())
    check(comp_total == P0 - v <= P0, 'old total composite-private regional bound')
    check(sum(pi.values(), F()) <= sum(mu.values(), F()), 'old exact-one-prime regional bound')
    check(1 - h <= comp_total + sum(pi.values(), F()) <= 1, 'old total private bounds')
    for p in primes:
        check(0 <= lower[p] <= pi[p] <= upper[p] <= mu[p], 'old prime-private regional bounds')
        check(sum((pi_comp[d] for d in composites if d % p == 0), F()) <= (p - 1) * pi[p], 'all PT6')
    rank = {p: F(p - 2) + F(1, p) for p in primes}
    alpha = {p: F(p + 1, p) for p in primes}
    R = sum((rank[p] * pi[p] / alpha[p] for p in primes), F())
    gamma = sum((max(F(), rank[p] - 5) * pi[p] / alpha[p] for p in primes), F())
    eta = sum((max(rank[p] / 2, rank[p] - F(5, 2)) * pi[p] / alpha[p] for p in primes), F())
    check(R <= 2 * J + Mcomp and gamma <= Mcomp and eta <= J + Mcomp, 'exact PR8 PR9 PR10 all hold')
    check(R / 2 <= J + Mcomp <= h, 'MP7 also holds')
    PT12 = F()
    stages = {p: F() for p in primes}
    for ss in subsets(primes, 2):
        U = sum((pi_comp[d] for d in composites if any(d % p == 0 for p in ss)), F())
        coefficient = prod(p - 1 for p in ss)
        PT12 += (len(ss) - 1) * U / coefficient
        stages[max(ss)] += U / coefficient
    check(PT12 <= J, 'PT12 inside prime-overlap budget')
    for p in primes:
        baseline = F(1, p) * (1 - prod((F(q - 1, q) for q in primes if q < p), start=F(1)))
        check(stages[p] <= baseline, 'PT13 below prime-label overlap baseline')
    q = 17
    epsilon = (q - 1) * pi[q] - sum((pi_comp[d] for d in composites if d % q == 0), F())
    residual_degree = sum((cap[d] - pi_comp[d] for d in composites if d % q == 0), F())
    gap = epsilon - residual_degree / 2
    check(gap == F(48194175100436, 422451039735725) > 0, 'common-source residual excludes scalar profile')
    triple = P0 / (phi(9) * phi(25) * phi(49))
    check(triple == F(128, 1786785) > 0, 'same palette cannot have pair-only actual residual')
    return dict(scope='Abstract rational scalar relaxation only; no residues, common antichains or selected sets. '
                      'Not a prime-support exclusion or an odd-cover candidate.',
                primes=primes, modulus_count=len(D), h=str(h), J=str(J), Mcomp=str(Mcomp),
                prime_private={p: str(pi[p]) for p in primes}, R=str(R), gamma=str(gamma), eta=str(eta),
                rho=str(P0 - comp_total), v=str(v), q17_epsilon=str(epsilon),
                q17_residual_degree=str(residual_degree), q17_reverse_bound_violation=str(gap),
                forced_9_25_49_intersection=str(triple))


def local_triple_boundary():
    """A literal CRT intersection on a higher carrier, not a whole cover."""
    period = 27 * 25 * 49
    primes = (3, 5, 7)
    aps = ((0, 3), (0, 5), (0, 7), (1, 9), (2, 27), (1, 25), (1, 49))
    check(lcm(*(d for _, d in aps)) == period, 'local boundary retains full original height')
    base = [z for z in range(period) if all(z % q for q in primes)]
    triple = [z for z in base if all((z - 1) % d == 0 for d in (9, 25, 49))]
    P0 = prod(F(q - 1, q) for q in primes)
    check(F(len(triple), period) == P0 / (phi(9) * phi(25) * phi(49)) == F(1, 11025),
          'positive full-height triple intersection')
    check(any(all((z - a) % d for a, d in aps) for z in range(period)), 'local boundary is not mislabeled a cover')
    return dict(scope='Local CRT intersection only; not a whole cover.', period=period,
                triple_points=len(triple), triple_mass=str(F(len(triple), period)))


def main():
    fixtures = [
        fixture('period12', ((0, 2), (0, 3), (1, 4), (5, 6), (7, 12))),
        fixture('period144', ((0, 2), (0, 3), (1, 4), (5, 6), (7, 24),
                              (7, 36), (19, 48), (67, 72), (91, 144))),
        fixture('period960', ((0, 2), (0, 3), (3, 4), (0, 5), (1, 8), (1, 10),
                              (13, 16), (17, 20), (13, 40), (69, 160),
                              (149, 320), (469, 480), (629, 960))),
    ]
    separator = scalar_separator()
    triple = local_triple_boundary()
    print(json.dumps(dict(exact_arithmetic=True, checks=CHECKS, even_cover_fixtures=fixtures,
                          scalar_separator=separator, local_triple_boundary=triple), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
