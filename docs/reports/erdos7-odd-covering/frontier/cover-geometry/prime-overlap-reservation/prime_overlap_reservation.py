#!/usr/bin/env python3
"""Exact prime/composite parent budgets and a scalar-relaxation separator.

The AP fixtures have even moduli. The six-prime rational private-mass
profile has no residues and is not asserted to be realizable. It separates
only the explicitly checked scalar constraints; in particular it fails the
independent known nine-prime requirement for an odd cover. Standard library
only, with checks active under Python -O. No Lean verification is claimed.
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


def beta_rho(q, m, primes):
    polynomial = [F(1)]
    free = [p for p in primes if p != q and m % p]
    for p in free:
        updated = [F()] * (len(polynomial) + 1)
        for j, value in enumerate(polynomial):
            updated[j] += value * F(p - 1, p)
            updated[j + 1] += value / p
        polynomial = updated
    base = 2 if m in primes else 1
    beta = sum((value / (j + base) for j, value in enumerate(polynomial)), F())
    rho = prod((F(p - 1, p) for p in free), start=F(1))
    check(beta / rho >= F(1, base), 'CA11 parent-type factor')
    return beta, rho


def changed_root(z, q, root, period):
    power = q ** valuation(period, q)
    other = period // power
    target = z % power - z % q + root
    result = (z + other * ((target - z) * pow(other, -1, power) % power)) % period
    check(result % q == root, 'reset first digit')
    check((result % power) // q == (z % power) // q, 'reset preserves full tail')
    check(result % other == z % other, 'reset preserves other coordinates')
    return result


def selected_budget(aps, memberships, primes, period, h, J, Mcomp):
    """Literal maximum partial selections; used only when all parents exist."""
    residues = {d: a for a, d in aps}
    selected = {}
    rank_sum = {q: 0 for q in primes}
    private = {q: sum(labels == {q} for labels in memberships) for q in primes}
    xprime = F()
    xcomp = F()
    lower_r = F()
    lower_gamma = F()
    for q in primes:
        height = valuation(period, q)
        alpha_q = F(q, q - 1) * (1 - F(1, q ** height))
        r_q = q - 2 + F(1, q ** (height - 1))
        lower_r += r_q * private[q] / (period * alpha_q)
        lower_gamma += max(F(), r_q - len(primes) + 1) * private[q] / (period * alpha_q)
        for z, labels in enumerate(memberships):
            if labels != {q}:
                continue
            roots = [root for root in range(q) if root != residues[q] % q]
            options = []
            for root in roots:
                at_root = memberships[changed_root(z, q, root, period)]
                candidates = [None]
                for d in sorted(at_root):
                    e = valuation(d, q)
                    m = d // q ** e
                    if e and m > 1:
                        check(m in residues, 'whole-private test needs actual parent')
                        candidates.append((d, m))
                options.append(candidates)
            best = ()
            for choices in product(*options):
                present = tuple(item for item in choices if item is not None)
                if len({m for _, m in present}) == len(present) and len(present) > len(best):
                    best = present
            rank_sum[q] += len(best)
            for d, m in best:
                selected.setdefault((q, m), {}).setdefault(d, set()).add(z)
                if m in primes:
                    xprime += 1 / (period * alpha_q)
                else:
                    xcomp += 1 / (period * alpha_q)
        check(F(rank_sum[q], period) >= r_q * private[q] / period,
              'whole-private mean partial-rank bound')
    charges = {True: F(), False: F()}
    columns = []
    for (q, m), by_child in sorted(selected.items()):
        children = [d for d in residues if valuation(d, q) > 0
                    and d // q ** valuation(d, q) == m]
        alpha = sum((F(q, q ** valuation(d, q)) for d in children), F())
        beta, rho = beta_rho(q, m, primes)
        points = set()
        for d, selected_points in by_child.items():
            e = valuation(d, q)
            a = residues[d]
            containing = {z for z in range(period)
                          if z % q == residues[q] % q
                          and z % (q ** e) // q == a % (q ** e) // q
                          and (z - a) % m == 0
                          and all(z % p != residues[p] % p for p in primes if p != q)}
            check(F(len(containing), period) == rho / d, 'exact containing cylinder')
            check(selected_points <= containing, 'actual selection lies in cylinder')
            check(points.isdisjoint(selected_points), 'cofactor used at two heights')
            points.update(selected_points)
        mass = F(len(points), period)
        check(mass <= alpha * rho / (q * m), 'selected source capacity')
        targets = [z for z, labels in enumerate(memberships) if q in labels and m in labels]
        capacity = sum((F(1, len(memberships[z].intersection(primes))) for z in targets), F()) / period
        check(capacity == beta / (q * m), 'CRT target capacity')
        charge = beta * mass / (alpha * rho)
        check(charge <= capacity, 'source charge bounded by actual target')
        charges[m in primes] += charge
        columns.append(dict(q=q, parent=m, selected_mass=str(mass), charge=str(charge)))
    check(xprime / 2 <= charges[True] <= J, 'prime-parent reserved budget')
    check(xcomp <= charges[False] <= Mcomp <= h - J, 'composite-parent reserved budget')
    check(lower_r <= xprime + xcomp <= 2 * J + Mcomp <= h + J, 'total rank budget')
    check(lower_gamma <= xcomp <= h - J, 'composite rank budget')
    return dict(Bprime=str(charges[True]), Bcomp=str(charges[False]),
                Xprime=str(xprime), Xcomp=str(xcomp), R=str(lower_r),
                gamma_source=str(lower_gamma), columns=columns)


def fixture(name, aps, test_selections=False):
    residues = {d: a for a, d in aps}
    check(len(residues) == len(aps), 'distinct fixture moduli')
    check(all(d > 1 and 0 <= a < d for a, d in aps), 'proper AP labels')
    period = lcm(*residues)
    primes = support(period)
    composites = [d for d in residues if d not in primes]
    check(all(p in residues for p in primes), 'all original prime labels present')
    for (a, d), (b, m) in combinations(aps, 2):
        if d % m == 0 or m % d == 0:
            check((a - b) % gcd(d, m) != 0, 'comparable classes must be disjoint')
    memberships = [frozenset(d for a, d in aps if (z - a) % d == 0) for z in range(period)]
    check(all(memberships), 'fixture covers whole period')
    P0 = prod(F(p - 1, p) for p in primes)
    J = sum((F(1, p) for p in primes), F()) - 1 + P0
    h = sum((F(1, d) for d in residues), F()) - 1
    Mcomp = sum((F(1, d) * (1 - prod((F(p - 1, p) for p in primes if d % p), start=F(1)))
                 for d in composites), F())
    zero_total = P0 * sum((F(1, phi(d)) for d in composites), F())
    literal_J = F()
    literal_Mcomp = F()
    literal_zero = F()
    for labels in memberships:
        k = len(labels.intersection(primes))
        t = len(labels) - k
        prime_edges = sum(q in labels and m in labels for q in primes for m in primes if q != m)
        comp_edges = sum(q in labels and m in labels for q in primes for m in composites if m % q)
        prime_load = F(prime_edges, k) if k else F()
        comp_load = F(comp_edges, k) if k else F()
        check(prime_load == max(k - 1, 0), 'pointwise full prime-pair load')
        check(comp_load == (t if k else 0), 'pointwise full composite-pair load')
        check(prime_load + comp_load <= k + t - 1, 'reserved loads fit same surplus')
        literal_J += prime_load / period
        literal_Mcomp += comp_load / period
        literal_zero += F(t if k == 0 else 0, period)
    check(literal_J == J, 'literal prime overlap equals CRT J')
    check(literal_Mcomp == Mcomp, 'literal composite target equals CRT formula')
    check(literal_zero == zero_total, 'literal no-prime composite incidence')
    check(h - J - Mcomp == zero_total - P0 >= 0, 'zero-prime excess identity')
    reset_charge = F()
    for ss in subsets(primes, 2):
        targets = {z for z, labels in enumerate(memberships) if labels == set(ss)}
        sources = {z for z, labels in enumerate(memberships)
                   if len(labels) == 1 and next(iter(labels)) in composites
                   and any(next(iter(labels)) % q == 0 for q in ss)}
        for z in sources:
            moved = z
            for q in ss:
                moved = changed_root(moved, q, residues[q] % q, period)
            check(moved in targets, 'multi-reset reaches exact-prime-only target')
        congestion = prod(q - 1 for q in ss)
        check(len(sources) <= congestion * len(targets), 'multi-reset congestion')
        reset_charge += F((len(ss) - 1) * len(sources), congestion * period)
    check(reset_charge <= J, 'PT12 is already inside reserved prime overlap')
    check(Mcomp + reset_charge <= h, 'no prime-only/composite double charge')
    missing = sorted({d // q ** valuation(d, q) for d in residues for q in primes
                      if valuation(d, q) and d // q ** valuation(d, q) > 1
                      and d // q ** valuation(d, q) not in residues})
    result = dict(name=name, period=period, AP_count=len(aps), h=str(h), J=str(J),
                  Mcomp=str(Mcomp), zero_prime_excess=str(zero_total - P0),
                  PT12=str(reset_charge), missing_original_parents=missing)
    if test_selections:
        check(not missing, 'selected whole-private fixture has all parents')
        result['actual_partial_selections'] = selected_budget(
            aps, memberships, primes, period, h, J, Mcomp)
    return result


def scalar_profile():
    primes = (3, 5, 7, 11, 13, 17)
    D = sorted(prod(p ** e for p, e in zip(primes, es))
               for es in product(range(3), repeat=len(primes)) if any(es))
    Q = prod(p ** 2 for p in primes)
    check(len(D) == len(set(D)) == 728, 'full distinct nonunit H=2 palette')
    check(all(d > 1 and d % 2 and Q % d == 0 for d in D), 'odd divisors')
    for d in D:
        for p in primes:
            if d % p == 0 and d != p:
                check(d // p in D, 'divisor closure above one')
    check(all(max(valuation(d, p) for d in D) == 2 for p in primes), 'original heights')
    composites = [d for d in D if d not in primes]
    P0 = prod(F(p - 1, p) for p in primes)
    h = sum((F(1, d) for d in D), F()) - 1
    check(h == prod(1 + F(1, p) + F(1, p * p) for p in primes) - 2,
          'actual reciprocal palette excess')
    J = sum((F(1, p) for p in primes), F()) - 1 + P0
    capacity = {d: P0 / phi(d) for d in composites}
    C = sum(capacity.values(), F())
    v = C - P0
    Mcomp = sum((F(1, d) * (1 - prod((F(p - 1, p) for p in primes if d % p), start=F(1)))
                 for d in composites), F())
    check(Mcomp == h - J - v, 'exact composite target formula')
    check(h >= J and v >= 0, 'prime overlap and conditional coverage baselines')
    check(sum((F(1, phi(d)) for d in composites), F()) >= 1, 'conditional union bound')
    mu = {p: P0 / (p - 1) for p in primes}
    lower = {p: mu[p] * max(F(), 1 - sum((F(1, phi(d)) for d in composites if d % p), F()))
             for p in primes}
    upper = {p: mu[p] * (1 - max(F(1, phi(d)) for d in composites if d % p)) for p in primes}
    r = {p: F(p - 2) + F(1, p) for p in primes}
    alpha = {p: F(p + 1, p) for p in primes}
    eta = {p: max(r[p] / 2, r[p] - F(len(primes) - 1, 2)) / alpha[p] for p in primes}
    gamma = {p: max(F(), r[p] - len(primes) + 1) / alpha[p] for p in primes}
    pi_prime = dict(lower)
    pi_prime[17] = upper[17]
    group5 = {d for d in composites if d % 5 == 0 and d % 7}
    group7 = {d for d in composites if d % 7 == 0 and d % 5}
    A5 = sum((capacity[d] for d in group5), F())
    A7 = sum((capacity[d] for d in group7), F())
    check(group5.isdisjoint(group7) and A5 >= v and A7 >= v, 'two admissible removal groups')
    pi_comp = {d: capacity[d] * (1 - (v / A5 if d in group5 else v / A7 if d in group7 else 0))
               for d in composites}
    pi_prime[11] = sum((pi_comp[d] for d in composites if d % 11 == 0), F()) / 10
    pi_prime[13] = (J + Mcomp - sum((eta[p] * pi_prime[p] for p in primes if p != 13), F())) / eta[13]
    for d in composites:
        check(max(F(), capacity[d] - v) <= pi_comp[d] <= capacity[d] <= F(1, d),
              'composite per-label regional lower and upper bounds')
    comp_total = sum(pi_comp.values(), F())
    prime_total = sum(pi_prime.values(), F())
    check(comp_total == P0 - v <= P0, 'composite private regional mass')
    check(prime_total <= sum(mu.values(), F()), 'prime private exact-one-prime capacity')
    check(1 - h <= comp_total + prime_total <= 1, 'total private mass interval')
    prime_rows = []
    for p in primes:
        check(0 <= lower[p] <= pi_prime[p] <= upper[p] <= mu[p] <= F(1, p),
              'prime private regional interval')
        reset_source = sum((pi_comp[d] for d in composites if d % p == 0), F())
        slack = (p - 1) * pi_prime[p] - reset_source
        check(slack >= 0, 'PT6 reset constraint')
        prime_rows.append(dict(q=p, lower=str(lower[p]), private=str(pi_prime[p]),
                               upper=str(upper[p]), PT6_slack=str(slack)))
    MP7 = sum((r[p] * pi_prime[p] / (2 * alpha[p]) for p in primes), F())
    old_type = sum((eta[p] * pi_prime[p] for p in primes), F())
    R = 2 * MP7
    gamma_source = sum((gamma[p] * pi_prime[p] for p in primes), F())
    check(MP7 <= J + Mcomp <= h, 'MP7 with the fixed-palette total capacity')
    check(old_type == J + Mcomp, 'old fixed-palette parent-type scalar saturated')
    check(R <= 2 * J + Mcomp <= h + J, 'new exact total-rank scalar also satisfied')
    PT12 = F()
    stage = {p: F() for p in primes}
    for ss in subsets(primes, 2):
        U = sum((pi_comp[d] for d in composites if any(d % p == 0 for p in ss)), F())
        denominator = prod(p - 1 for p in ss)
        PT12 += (len(ss) - 1) * U / denominator
        stage[max(ss)] += U / denominator
    kappa = lambda ss: 1 + prod((F(p, p - 1) for p in ss), start=F(1)) * (sum((F(1, p) for p in ss), F()) - 1)
    alternate_PT12 = sum(((kappa(primes) - kappa([p for p in primes if d % p])) * pi_comp[d]
                          for d in composites), F())
    check(PT12 == alternate_PT12 <= J, 'PT12 coefficient identity and prime-overlap budget')
    stage_rows = []
    for p in primes:
        baseline = F(1, p) * (1 - prod((F(q - 1, q) for q in primes if q < p), start=F(1)))
        check(stage[p] <= baseline, 'PT13 below known prime-label overlap lower bound on u_P')
        stage_rows.append(dict(q=p, charge=str(stage[p]), prime_baseline=str(baseline)))
    gap = gamma_source - Mcomp
    check(gap == F(26728255069959585256, 1236687482722966669395) > 0,
          'strict fixed-palette composite-rank separation')
    check(2 * J + Mcomp - R == gap, 'equal slack in exact total-rank scalar')
    check(gamma_source <= h - J, 'coarse composite-rank scalar also satisfied')
    return dict(scope='Abstract rational scalar profile, not AP residues or joint selected sets. '
                      'Also excluded by the independent known nine-prime condition.',
                primes=primes, full_heights=[2] * len(primes), modulus_count=len(D),
                composite_count=len(composites), full_period=Q,
                h=str(h), J=str(J), P0=str(P0), C=str(C), v=str(v),
                A5=str(A5), A7=str(A7), composite_private_total=str(comp_total),
                total_private_mass=str(comp_total + prime_total), prime_rows=prime_rows,
                MP7=str(MP7), old_type_scalar=str(old_type), old_type_budget=str(J + Mcomp),
                R=str(R), total_rank_budget=str(2 * J + Mcomp),
                total_rank_slack=str(2 * J + Mcomp - R), PT12=str(PT12), PT13=stage_rows,
                gamma_source=str(gamma_source), composite_budget=str(Mcomp),
                gamma_violation=str(gap), exact_composite_target=str(Mcomp),
                coarse_gamma_slack=str(h - J - gamma_source))


def main():
    fixtures = [
        fixture('period12', ((0, 2), (0, 3), (1, 4), (5, 6), (7, 12)), True),
        fixture('period144', ((0, 2), (0, 3), (1, 4), (5, 6), (7, 24),
                              (7, 36), (19, 48), (67, 72), (91, 144))),
        fixture('period960', ((0, 2), (0, 3), (3, 4), (0, 5), (1, 8), (1, 10),
                              (13, 16), (17, 20), (13, 40), (69, 160),
                              (149, 320), (469, 480), (629, 960))),
    ]
    profile = scalar_profile()
    print(json.dumps(dict(exact_arithmetic=True, checks=CHECKS,
                          even_cover_fixtures=fixtures, scalar_profile=profile),
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
