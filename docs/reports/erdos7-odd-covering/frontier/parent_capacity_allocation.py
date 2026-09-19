#!/usr/bin/env python3
"""Exact checks of synchronized-parent capacities and global surplus allocation.

The three fixtures are complete covers with even moduli, not odd covers.
Missing original parents are reported and excluded from the matching options.
All calculations use the standard library and rational arithmetic. Checks
remain active under optimized Python; no Lean verification is asserted.
"""
from fractions import Fraction
from itertools import combinations, product
from math import gcd, lcm, prod
import json


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def factors(n):
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


def split_prime(d, q):
    e = 0
    while d % q == 0:
        d //= q
        e += 1
    return e, d


def prepare(name, aps):
    residues = {d: a for a, d in aps}
    check(len(residues) == len(aps), name + ': repeated modulus')
    check(all(d > 1 and 0 <= a < d for a, d in aps), name + ': bad AP')
    period = lcm(*residues)
    primes = factors(period)
    check(all(q in residues for q in primes), name + ': missing prime label')
    for i, (a, d) in enumerate(aps):
        for b, m in aps[i + 1:]:
            if d % m == 0 or m % d == 0:
                check((a - b) % gcd(d, m) != 0,
                      name + ': intersecting comparable original labels')
    covers = [frozenset(d for a, d in aps if (z - a) % d == 0)
              for z in range(period)]
    check(all(covers), name + ': not a whole cover')
    prime_counts = [len(labels.intersection(primes)) for labels in covers]
    surplus = Fraction(sum(len(labels) - 1 for labels in covers), period)
    check(surplus == sum((Fraction(1, d) for d in residues), Fraction()) - 1,
          name + ': wrong surplus identity')
    return dict(name=name, residues=residues, period=period, primes=primes,
                covers=covers, prime_counts=prime_counts, surplus=surplus)


def beta_and_rho(q, m, primes):
    """Integrate the exact independent prime-root polynomial."""
    free = tuple(p for p in primes if p != q and m % p != 0)
    polynomial = [Fraction(1)]
    for p in free:
        updated = [Fraction()] * (len(polynomial) + 1)
        for j, value in enumerate(polynomial):
            updated[j] += value * Fraction(p - 1, p)
            updated[j + 1] += value / p
        polynomial = updated
    base = 2 if m in primes else 1
    beta = sum((value / (j + base)
                for j, value in enumerate(polynomial)), Fraction())
    rho = prod((Fraction(p - 1, p) for p in free), start=Fraction(1))
    check(beta / rho >= Fraction(1, base), 'prime-exclusion cancellation')
    return beta, rho, base, free


def changed_root(model, z, q, root):
    """Replace just the first q digit, preserving every other digit."""
    height, _ = split_prime(model['period'], q)
    power = q ** height
    other = model['period'] // power
    target = z % power - z % q + root
    result = (z + other * ((target - z) * pow(other, -1, power) % power))
    result %= model['period']
    check(result % q == root, 'wrong substituted first root')
    check((result % power) // q == (z % power) // q, 'q tail changed')
    check(result % other == z % other, 'non-q coordinate changed')
    return result


def selected_sources(model, q):
    """Enumerate matchings, choose the first, and independently check Hall."""
    residues = model['residues']
    roots = tuple(r for r in range(q) if r != residues[q] % q)
    by_label = {}
    by_parent = {}
    good = set()
    tuples = set()
    missing = set()
    matching_count = 0
    hall_checks = 0
    private_count = 0
    for z, labels in enumerate(model['covers']):
        if labels != {q}:
            continue
        private_count += 1
        options = []
        for root in roots:
            lifted = changed_root(model, z, q, root)
            available = []
            for d in sorted(model['covers'][lifted]):
                e, m = split_prime(d, q)
                if e == 0 or m == 1:
                    continue
                if m not in residues:
                    missing.add(m)
                    continue
                available.append((d, m))
            options.append(tuple(available))
        matchings = [choice for choice in product(*options)
                     if len({m for _, m in choice}) == q - 1]
        hall = True
        for size in range(1, len(roots) + 1):
            for subset in combinations(range(len(roots)), size):
                colors = {m for i in subset for _, m in options[i]}
                hall = hall and len(colors) >= size
                hall_checks += 1
        check(bool(matchings) == hall, 'matching enumeration disagrees with Hall')
        if not matchings:
            continue
        good.add(z)
        matching_count += len(matchings)
        chosen = matchings[0]
        tuples.add(tuple(d for d, _ in chosen))
        for root, (d, m) in zip(roots, chosen):
            check(d in residues and m in residues, 'invented original label')
            check(d in model['covers'][changed_root(model, z, q, root)],
                  'selected original misses the shared source coordinates')
            by_label.setdefault(d, set()).add(z)
            by_parent.setdefault(m, set()).add(z)
    check(sum(len(points) for points in by_parent.values()) == (q - 1) * len(good),
          'wrong number of distinct parent selections per source')
    return dict(good=good, by_label=by_label, by_parent=by_parent,
                missing=sorted(missing), tuples=tuples, matching_count=matching_count,
                hall_checks=hall_checks, private_count=private_count)


def examine(model):
    period = model['period']
    residues = model['residues']
    primes = model['primes']
    edges = {}
    sources = {}
    source_rows = []
    label_rows = []
    global_source = Fraction()
    global_variable_source = Fraction()
    coarse_source = Fraction()
    distinct_parent_source = Fraction()
    composite_sensitive_source = Fraction()
    for q in primes:
        selected = selected_sources(model, q)
        sources[q] = selected
        height, _ = split_prime(period, q)
        alpha_q = Fraction(q, q - 1) * (1 - Fraction(1, q ** height))
        fixed_prime_source = Fraction()
        fixed_prime_targets = Fraction()
        for m in sorted(residues):
            if m % q == 0:
                continue
            children = sorted(d for d in residues
                              if split_prime(d, q)[0] > 0
                              and split_prime(d, q)[1] == m)
            if not children:
                continue
            alpha = sum((Fraction(q, q ** split_prime(d, q)[0])
                         for d in children), Fraction())
            check(0 < alpha <= alpha_q, 'invalid finite-height capacity')
            beta, rho, base, free = beta_and_rho(q, m, primes)
            target = {z for z, labels in enumerate(model['covers'])
                      if q in labels and m in labels}
            check(Fraction(len(target), period) == Fraction(1, q * m),
                  'wrong coprime target cylinder mass')
            exact_capacity = sum((Fraction(1, model['prime_counts'][z])
                                  for z in target), Fraction()) / period
            check(exact_capacity == beta / (q * m), 'beta disagrees with actual CRT')
            edges[q, m] = exact_capacity
            parent_source = selected['by_parent'].get(m, set())
            union = set()
            for d in children:
                e, _ = split_prime(d, q)
                a = residues[d]
                lifted = {z for z in range(period)
                          if z % q == residues[q] % q
                          and ((z % (q ** e)) // q) == ((a % (q ** e)) // q)
                          and (z - a) % m == 0}
                check(Fraction(len(lifted), period) == Fraction(1, d),
                      'wrong full-height prime-root lift mass')
                excluded = {z for z in lifted
                            if all(z % p != residues[p] % p for p in primes if p != q)}
                check(Fraction(len(excluded), period) == rho / d,
                      'prime-private exclusions did not have the stated exact mass')
                selected_label = selected['by_label'].get(d, set())
                check(selected_label <= excluded, 'selected source violates actual prime exclusions')
                check(union.isdisjoint(selected_label), 'one source reused a cofactor at two heights')
                union.update(selected_label)
            check(union == parent_source, 'height union changed the actual selected source')
            mass = Fraction(len(parent_source), period)
            check(mass <= alpha * rho / (q * m), 'source capacity with prime exclusions')
            charge = beta * mass / (alpha * rho)
            check(charge <= exact_capacity, 'weighted source exceeds allocated target')
            global_source += charge
            # A nonconstant actual source density, with an explicit nonunit bound M_q.
            density_bound = Fraction(q)
            weighted_mass = sum((density_bound * Fraction(1 + (z + q) % 5, 5)
                                 for z in parent_source), Fraction()) / period
            check(weighted_mass <= density_bound * mass, 'source density domination')
            global_variable_source += beta * weighted_mass / (alpha * rho * density_bound)
            fixed_prime_source += mass / (alpha * rho)
            fixed_prime_targets += Fraction(len(target), period)
            composite_sensitive_source += mass / (base * alpha_q)
            label_rows.append(dict(prime=q, parent=m, children=children,
                                   source_points=len(parent_source), alpha=str(alpha),
                                   free_primes=list(free), beta=str(beta), rho=str(rho),
                                   allocation_coefficient=str(beta / (alpha * rho)),
                                   source_charge=str(charge), target_capacity=str(exact_capacity)))
        good_mass = Fraction(len(selected['good']), period)
        check((q - 1) * good_mass <= alpha_q * model['surplus'],
              'all-tuple fixed-prime finite-height bound')
        check(fixed_prime_source <= fixed_prime_targets <= model['surplus'],
              'fixed-prime parent budget')
        coarse_source += Fraction(q - 1, 2) * good_mass / alpha_q
        distinct_parent_factor = q - 1 - Fraction(min(q - 1, len(primes) - 1), 2)
        distinct_parent_source += distinct_parent_factor * good_mass / alpha_q
        source_rows.append(dict(prime=q, full_height=height, alpha_q=str(alpha_q),
                                prime_private_points=selected['private_count'],
                                synchronized_good_points=len(selected['good']),
                                chosen_tuple_count=len(selected['tuples']),
                                matching_count=selected['matching_count'],
                                hall_subset_checks=selected['hall_checks'],
                                missing_original_parents=selected['missing'],
                                fixed_prime_weighted_source=str(fixed_prime_source)))
    naive_violations = 0
    pointwise_maximum = Fraction()
    for z, labels in enumerate(model['covers']):
        incoming = sum(q in labels and m in labels for q, m in edges)
        k = model['prime_counts'][z]
        allocated = Fraction(incoming, k) if k else Fraction()
        check(allocated <= len(labels) - 1, 'global pointwise surplus reused')
        naive_violations += incoming > len(labels) - 1
        pointwise_maximum = max(pointwise_maximum, allocated)
    allocated_capacity = sum(edges.values(), Fraction())
    check(coarse_source <= distinct_parent_source <= composite_sensitive_source <= global_source,
          'coarse source implication')
    check(global_variable_source <= global_source <= allocated_capacity <= model['surplus'],
          'global integrated source/capacity/surplus budget')
    return dict(name=model['name'], period=period, original_ap_count=len(residues),
                primes=list(primes), surplus=str(model['surplus']),
                sources=source_rows, parent_columns=label_rows,
                global_source=str(global_source),
                nonconstant_dominated_source=str(global_variable_source),
                composite_sensitive_source=str(composite_sensitive_source),
                coarse_all_prime_source=str(coarse_source),
                distinct_parent_all_prime_source=str(distinct_parent_source),
                allocated_target_capacity=str(allocated_capacity),
                maximum_pointwise_allocated_load=str(pointwise_maximum),
                unallocated_pair_count_violations=naive_violations)


def main():
    fixtures = (
        ('period12', ((0, 2), (0, 3), (1, 4), (5, 6), (7, 12))),
        ('period144', ((0, 2), (0, 3), (1, 4), (5, 6), (7, 24),
                       (7, 36), (19, 48), (67, 72), (91, 144))),
        ('period960', ((0, 2), (0, 3), (3, 4), (0, 5), (1, 8), (1, 10),
                       (13, 16), (17, 20), (13, 40), (69, 160),
                       (149, 320), (469, 480), (629, 960))),
    )
    results = [examine(prepare(name, aps)) for name, aps in fixtures]
    check(results[0]['unallocated_pair_count_violations'] > 0,
          'regression fixture did not detect naive cross-prime double charging')
    print(json.dumps(dict(scope='finite even-cover fixtures; not an odd-cover resolution',
                          exact_arithmetic=True, fixtures=results), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
