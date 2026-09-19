#!/usr/bin/env python3
"""Exact finite AP checks for swaps and first-prime-digit private transport.

All listed whole covers have even moduli. They test general finite mechanisms,
not existence or nonexistence of distinct odd covers. The normalized fixed-D
minimum is certified only for D=(2,3,4,6,12). Other fixtures need neither divisor
closure nor lexicographic extremality. No Lean verification is asserted.
Only the Python standard library is used; checks remain active under -O.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import gcd, lcm, prod
import json


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def factors(n):
    answer = []
    q = 2
    while q * q <= n:
        if n % q == 0:
            answer.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        answer.append(n)
    return tuple(answer)


def prime_power(n, q):
    power = 1
    while n % q == 0:
        n //= q
        power *= q
    return power


def hits(y, ap):
    return (y - ap[0]) % ap[1] == 0


def prepare(name, aps):
    aps = tuple(aps)
    residues = {d: a for a, d in aps}
    check(len(residues) == len(aps), name + ': repeated modulus')
    check(all(d > 1 and 0 <= a < d for a, d in aps), name + ': bad AP')
    period = lcm(*residues)
    primes = factors(period)
    check(all(q in residues for q in primes), name + ': missing prime label')
    for i, (a, d) in enumerate(aps):
        for b, e in aps[i + 1:]:
            if d % e == 0 or e % d == 0:
                check((a - b) % gcd(d, e) != 0,
                      name + ': intersecting comparable originals')
    cover_sets = [frozenset(d for a, d in aps if hits(y, (a, d)))
                  for y in range(period)]
    check(all(cover_sets), name + ': not a whole cover')
    private = {d: {y for y, labels in enumerate(cover_sets) if labels == {d}}
               for d in residues}
    check(all(private.values()), name + ': redundant original')
    excess_count = sum(len(labels) - 1 for labels in cover_sets)
    check(Fraction(excess_count, period) ==
          sum((Fraction(1, d) for d in residues), Fraction()) - 1,
          name + ': excess identity')
    return dict(name=name, aps=aps, residues=residues, period=period,
                primes=primes, covers=cover_sets, private=private,
                excess_count=excess_count)


def reset(model, y, selected_primes):
    """Change only each selected first digit, retaining all higher digits."""
    period = model['period']
    for q in selected_primes:
        power = prime_power(period, q)
        other = period // power
        target = y % power - y % q + model['residues'][q] % q
        y = (y + other * ((target - y) * pow(other, -1, power) % power)) % period
    return y


def check_coordinates(model, source, target, selected):
    for q in model['primes']:
        power = prime_power(model['period'], q)
        if q in selected:
            check(target % q == model['residues'][q] % q, 'wrong reset root')
            check((target % power) // q == (source % power) // q,
                  'reset discarded a higher prime digit')
        else:
            check(target % power == source % power, 'reset changed another coordinate')


def single_resets(model):
    rows = []
    for q in model['primes']:
        counts = Counter()
        proper_counts = Counter()
        roots = set()
        for d, points in model['private'].items():
            if d % q:
                continue
            roots.add(model['residues'][d] % q)
            for y in points:
                z = reset(model, y, (q,))
                check_coordinates(model, y, z, {q})
                check(model['covers'][z] == {q}, 'reset image is not prime-private')
                counts[z] += 1
                if d == q:
                    check(z == y, 'prime parent reset should be identity')
                else:
                    check(y % q != model['residues'][q] % q, 'proper source at prime root')
                    proper_counts[z] += 1
        cap = len(roots)
        check(all(v <= cap for v in counts.values()), 'actual-root pointwise cap')
        check(all(v <= q - 1 for v in proper_counts.values()), 'proper-parent root cap')
        check(sum(counts.values()) <= cap * len(model['private'][q]), 'integrated root cap')
        rows.append(dict(prime=q, actual_source_roots=sorted(roots), root_cap=cap,
                         source_points=sum(counts.values()),
                         prime_private_points=len(model['private'][q]),
                         maximum_preimages=max(counts.values()),
                         improper_q_minus_one_cap_detected=max(counts.values()) > q - 1))
    return rows


def multi_resets(model):
    """Strong touch-support source: composite d with gcd(d, product(S))>1."""
    rows = []
    target_cells = []
    weighted_source = Fraction()
    stage_source = {q: Fraction() for q in model['primes']}
    for size in range(2, len(model['primes']) + 1):
        for selected_tuple in combinations(model['primes'], size):
            selected = frozenset(selected_tuple)
            source_moduli = [d for d in model['private'] if d not in model['primes']
                             and gcd(d, prod(selected)) > 1]
            source = set().union(*(model['private'][d] for d in source_moduli))
            check(len(source) == sum(len(model['private'][d]) for d in source_moduli),
                  'private sources overlap')
            cell = {y for y, labels in enumerate(model['covers']) if labels == selected}
            counts = Counter()
            for y in source:
                check(all(y % q != model['residues'][q] % q for q in selected),
                      'composite-private source already in a reset prime class')
                z = reset(model, y, selected_tuple)
                check_coordinates(model, y, z, selected)
                check(z in cell, 'multi-reset image not covered by exactly the chosen primes')
                check(reset(model, y, tuple(reversed(selected_tuple))) == z,
                      'prime-coordinate resets do not commute')
                counts[z] += 1
            cap = prod(q - 1 for q in selected)
            check(all(v <= cap for v in counts.values()), 'multi-root pointwise cap')
            check(len(source) <= cap * len(cell), 'multi-root integrated cap')
            check(all(cell.isdisjoint(old) for old in target_cells), 'different target cells overlap')
            target_cells.append(cell)
            weighted_source += Fraction((size - 1) * len(source), cap)
            stage_source[max(selected)] += Fraction(len(source), cap)
            rows.append(dict(primes=list(selected_tuple), source_moduli=source_moduli,
                             source_points=len(source), exact_target_points=len(cell),
                             image_points=len(counts), root_cap=cap,
                             maximum_preimages=max(counts.values(), default=0)))
    target_excess = sum((len(model['covers'][y]) - 1)
                        for cell in target_cells for y in cell)
    check(weighted_source <= target_excess <= model['excess_count'],
          'disjoint multi-reset excess budget')
    stages = []
    for q, charge in stage_source.items():
        earlier = {y for y in range(model['period'])
                   if any(max(factors(d)) < q for d in model['covers'][y])}
        prime_earlier = {y for y in earlier if q in model['covers'][y]}
        check(charge <= len(prime_earlier), 'largest-prime-stage target budget')
        stages.append(dict(prime=q, source_charge=str(charge / model['period']),
                           actual_prime_earlier_overlap=str(Fraction(len(prime_earlier), model['period']))))
    return dict(subsets=rows, weighted_source=str(weighted_source / model['period']),
                target_excess=str(Fraction(target_excess, model['period'])), stages=stages)


def base_source(aps, p, base):
    return {x for x in range(base) if not any(d % p and hits(x, (a, d)) for a, d in aps)}


def swap(model, p, d):
    period = model['period']
    power = prime_power(d, p)
    m = d // power
    check(power > 1 and m > 1 and m in model['residues'], 'missing p-free divisor parent')
    a, b = model['residues'][d], model['residues'][m]
    base = period // prime_power(period, p)
    B = {x for x in range(base) if (x - b) % m == 0}
    C = {x for x in range(base) if (x - a) % m == 0}
    check(B.isdisjoint(C), 'parent and child shadow intersect')
    other_free = {x for x in range(base) if any(e % p and e != m and hits(x, (c, e))
                                               for c, e in model['aps'])}
    E = B - other_free
    R = base_source(model['aps'], p, base)
    K = {y for y in range(period) if (y - a) % power == 0}
    escape = model['private'][m] - K
    check(all(y % base in E for y in model['private'][m]), 'private projection outside exclusive cell')
    new_child = a % power + power * ((b - a % power) * pow(power, -1, m) % m)
    new_aps = tuple((a % m if e == m else new_child if e == d else c, e)
                    for c, e in model['aps'])
    uncovered = {y for y in range(period) if not any(hits(y, ap) for ap in new_aps)}
    check(uncovered == escape, 'single swap holes are not exactly private escapes')
    new_R = base_source(new_aps, p, base)
    check((R - C).isdisjoint(E) and new_R == (R - C) | E, 'survivor set identity')
    check(len(new_R) - len(R) == len(E) - len(C & R), 'survivor mass change')
    excess_region = {y for y in range(period) if y % base in E and y not in K} - escape
    check(all(len(model['covers'][y]) >= 2 for y in excess_region), 'charge outside original excess')
    check(Fraction(len(E), base) * (1 - Fraction(1, power)) -
          Fraction(len(escape), period) == Fraction(len(excess_region), period),
          'exclusive excess-or-escape identity')
    return dict(parent=m, child=d, base=base, E=E, R=R, C=C, escape=escape,
                new_R=new_R, new_aps=new_aps, excess_region=excess_region, power=power)


def tuple_budget(model, p, children):
    check(p == max(model['primes']) and len(children) == p - 1,
          'tuple stage must be largest prime, with exactly p-1 children')
    swaps = [swap(model, p, d) for d in children]
    check({model['residues'][d] % p for d in children} ==
          set(range(p)) - {model['residues'][p] % p}, 'tuple roots')
    check(len({s['parent'] for s in swaps}) == len(children), 'tuple cofactors repeat')
    base = swaps[0]['base']
    U = set.intersection(*(s['C'] for s in swaps)) & swaps[0]['R']
    tail_size = prime_power(model['period'], p) // p
    J = {t for t in range(tail_size) if all(
        (model['residues'][d] % p + p * t - model['residues'][d]) % s['power'] == 0
        for d, s in zip(children, swaps))}
    maximum_power = max(s['power'] for s in swaps)
    theta = Fraction(len(J), tail_size)
    lam = Fraction(len(U), base) * theta
    check(U and J and theta == Fraction(p, maximum_power), 'common tuple product mass')
    check(lam / theta == Fraction(len(U), base), 'tuple tail factor was lost')
    region_union = set()
    for s in swaps:
        check(region_union.isdisjoint(s['excess_region']), 'exclusive excess double charged')
        region_union |= s['excess_region']
    earlier = {y for y in range(model['period']) if any(d % p for d in model['covers'][y])}
    p_bearing = {y for y in range(model['period']) if any(d % p == 0 for d in model['covers'][y])}
    check(region_union <= earlier & p_bearing, 'localized P-overlap charge')
    groups = {}
    for s in swaps:
        groups.setdefault(min(factors(s['parent'])), []).append(s)
    weighted = Fraction()
    prime_budget = Fraction()
    alpha = Fraction()
    group_rows = []
    for q, members in groups.items():
        roots = {model['residues'][s['parent']] % q for s in members}
        cap = len(roots)
        bq = int(any(s['parent'] == q for s in members))
        check(cap <= q - 1 + bq, 'prime-parent root correction')
        counts = Counter(reset(model, y, (q,)) for s in members for y in s['escape'])
        check(all(z in model['private'][q] and count <= cap for z, count in counts.items()),
              'tuple escape reset cap')
        check(sum(counts.values()) <= cap * len(model['private'][q]), 'tuple escape mass cap')
        weighted += sum((Fraction(len(s['E']), base) * (1 - Fraction(1, s['power'])) / cap
                         for s in members), Fraction())
        prime_budget += Fraction(len(model['private'][q]), model['period'])
        alpha = max(alpha, Fraction(1, cap))
        group_rows.append(dict(prime=q, actual_parent_roots=sorted(roots), root_cap=cap,
                               prime_parent_present=bool(bq), escape_points=sum(counts.values())))
    bound = alpha * Fraction(len(earlier & p_bearing), model['period']) + prime_budget
    check(weighted <= bound, 'actual-root weighted swap-reset budget')
    return swaps, dict(children=list(children), raw_product_mass=str(lam),
                       common_tail_mass=str(theta), common_base_mass=str(lam / theta),
                       exclusive_excess=str(Fraction(len(region_union), model['period'])),
                       actual_P_overlap=str(Fraction(len(earlier & p_bearing), model['period'])),
                       parent_escape_counts={str(s['parent']): len(s['escape']) for s in swaps},
                       reset_groups=group_rows, weighted_lhs=str(weighted),
                       overlap_coefficient=str(alpha), weighted_rhs=str(bound))


def minimum_and_swaps():
    D = (2, 3, 4, 6, 12)
    covers = []
    for a4, a6, a12 in product(range(4), range(6), range(12)):
        residues = (0, 0, a4, a6, a12)
        aps = tuple(zip(residues, D))
        if all(any(hits(y, ap) for ap in aps) for y in range(12)):
            covers.append(prepare('normalized fixed-D cover', aps))
    expected = {(0, 0, 1, 1, 11), (0, 0, 1, 5, 7),
                (0, 0, 3, 1, 5), (0, 0, 3, 5, 1)}
    check({tuple(a for a, d in m['aps']) for m in covers} == expected, 'fixed-D exhaustive covers')
    minimum = min(len(base_source(m['aps'], 3, 4)) for m in covers)
    check(minimum == 1, 'fixed-D survivor minimum')
    legal = failed = 0
    for model in covers:
        swaps, budget = tuple_budget(model, 3, (6, 12))
        for s in swaps:
            if not s['escape']:
                legal += 1
                check(len(s['R']) == minimum, 'original not a source minimizer')
                check(len(s['new_R']) >= len(s['R']), 'legal swap reduces minimum source')
                check(len(s['E']) >= len(s['C'] & s['R']), 'swap-source inequality reversed')
            else:
                failed += 1
        theta = Fraction(budget['common_tail_mass'])
        lam = Fraction(budget['raw_product_mass'])
        lower = (lam / theta) * sum((1 - Fraction(1, s['power'])
                                     for s in swaps if not s['escape']), Fraction())
        check(lower <= Fraction(budget['actual_P_overlap']), 'strengthened tuple coefficient')
    check((legal, failed) == (4, 4), 'swap classification')
    return dict(normalized_candidates=4 * 6 * 12, whole_covers=len(covers),
                residue_vectors=sorted(expected), minimum_R3_mass=str(Fraction(minimum, 4)),
                legal_swaps=legal, escape_blocked_swaps=failed,
                normalization='Any fixed-D residue system has a CRT translation making A2=A3=0; translation preserves survivor mass.')


def private_windows(name, aps):
    """Check the CVE consequences on actual periodic private points, not a theorem replay."""
    period = lcm(*(d for a, d in aps))
    cover_sets = [frozenset(d for a, d in aps if hits(y, (a, d)))
                  for y in range(period)]
    parent_count = prefix_count = positive_lower = large_prefix = zero_kappa = long_window = 0
    for a, m in aps:
        private = {y for y, labels in enumerate(cover_sets) if labels == {m}}
        check(private, 'window fixture parent is not essential')
        kappa = sum(d != m and (a - b) % gcd(m, d) == 0 for b, d in aps)
        window = 2 ** kappa
        parent_period = period // m
        y_private = sorted(y for y in range(parent_period) if (a + m * y) % period in private)
        cyclic_gaps = [right - left for left, right in
                       zip(y_private, y_private[1:] + [y_private[0] + parent_period])]
        check(max(cyclic_gaps) <= window, 'an actual cyclic CVE window has no private point')
        check(Fraction(len(private), period) >= Fraction(1, m * window), 'private density lower bound')
        parent_count += 1
        zero_kappa += kappa == 0
        long_window += window > parent_period
        for p in factors(period):
            if m % p == 0:
                continue
            power = p
            while parent_period % power == 0:
                floor_count = (power - 1) // window
                lower = Fraction(floor_count, m * power)
                inside_counts = Counter(y % power for y in private)
                for residue in range(power):
                    escape_count = len(private) - inside_counts[residue]
                    check(Fraction(escape_count, period) >= lower, 'prefix escape density lower bound')
                    prefix_count += 1
                    positive_lower += floor_count > 0
                    if power >= 2 * window:
                        check(lower >= Fraction(1, 2 * m * window), 'large-prefix half-density bound')
                        large_prefix += 1
                power *= p
    return dict(name=name, period=period, whole_cover=all(cover_sets),
                covered_points=sum(bool(s) for s in cover_sets),
                essential_parents=parent_count, prime_prefix_checks=prefix_count,
                positive_prefix_lower_checks=positive_lower,
                large_prefix_checks=large_prefix, zero_kappa_parents=zero_kappa,
                window_longer_than_parent_period=long_window)


def run():
    fixtures = [
        ('even period-12 whole cover', [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)]),
        ('even refined period-144 whole cover',
         [(0, 2), (0, 3), (1, 4), (5, 6), (7, 24), (7, 36),
          (19, 48), (67, 72), (91, 144)]),
        ('even three-prime period-960 whole cover',
         [(0, 2), (0, 3), (3, 4), (0, 5), (1, 8), (1, 10),
          (13, 16), (17, 20), (13, 40), (69, 160), (149, 320),
          (469, 480), (629, 960)]),
    ]
    results = []
    models = []
    for name, aps in fixtures:
        model = prepare(name, aps)
        models.append(model)
        results.append(dict(name=name, APs=aps, period=model['period'],
                            whole_cover=True, distinct_odd_cover=False,
                            private_counts={str(d): len(v) for d, v in model['private'].items()},
                            excess=str(Fraction(model['excess_count'], model['period'])),
                            single_resets=single_resets(model), multi_resets=multi_resets(model)))
    check(all(row['improper_q_minus_one_cap_detected']
              for row in results[0]['single_resets']), 'prime-parent omission not detected')
    prime_counterexample = {y for d in (3, 6, 12) for y in models[0]['private'][d]}
    check(prime_counterexample == {3, 7, 11} and
          {reset(models[0], y, (3,)) for y in prime_counterexample} == {3},
          'literal prime-parent omitted-root countercheck')
    check(len(prime_counterexample) > (3 - 1) * len(models[0]['private'][3]),
          'old cap did not fail on actual original private sources')
    check(results[0]['multi_resets']['subsets'][0]['source_moduli'] == [4, 6, 12],
          'touch-support source regressed to all-primes-divide condition')
    check(models[2]['private'][480] == {949} and models[2]['private'][960] == {629},
          'three-prime private witnesses')
    selected = [(2,), (3,), (5,), (2, 3), (2, 5), (3, 5), (2, 3, 5)]
    expected = {629: [884, 309, 245, 564, 500, 885, 180],
                949: [244, 309, 565, 564, 820, 885, 180]}
    for y, targets in expected.items():
        check([reset(models[2], y, S) for S in selected] == targets,
              'literal CRT multi-reset witness mismatch')
    _, base_budget = tuple_budget(models[0], 3, (6, 12))
    _, deep_budget = tuple_budget(models[1], 3, (6, 36))
    check(deep_budget['common_tail_mass'] == '1/3' and
          deep_budget['raw_product_mass'] == '1/12' and
          deep_budget['common_base_mass'] == '1/4', 'nontrivial tuple tail coefficient')
    window_rows = [private_windows(name, aps) for name, aps in fixtures]
    odd_noncover = [(0, 3), (0, 5), (1, 75)]
    odd_window = private_windows('odd NONCOVER: local private-window check only', odd_noncover)
    check(not odd_window['whole_cover'] and odd_window['covered_points'] == 36,
          'odd local window fixture falsely treated as a whole cover')
    odd_private = {y for y in range(75) if hits(y, odd_noncover[0]) and
                   not any(hits(y, ap) for ap in odd_noncover[1:])}
    odd_escape = {y for y in odd_private if y % 25 != 1}
    check(len(odd_private) == 20 and len(odd_escape) == 19 and (25 - 1) // 2 == 12,
          'literal odd noncover window witness')
    window_rows.append(odd_window)
    check(any(r['zero_kappa_parents'] for r in window_rows) and
          any(r['window_longer_than_parent_period'] for r in window_rows) and
          any(r['large_prefix_checks'] for r in window_rows), 'window boundary cases missing')
    return dict(success=True,
                scope='Exact complete-period checks on distinct EVEN whole covers, plus one explicitly NONCOVER odd list for private-window bounds. These are not odd-cover certificates or Lean proofs. Fixed-D minimization is only for the explicitly enumerated modulus set.',
                multi_source_rule='composite original d with gcd(d, product(S)) > 1; |S| >= 2',
                fixtures=results, normalized_minimum=minimum_and_swaps(),
                tuple_budgets=[base_budget, deep_budget],
                private_window_checks=window_rows,
                odd_noncover_window=dict(APs=odd_noncover, period=75, whole_cover=False,
                    parent=3, P=5, prefix_power=25, prefix_residue=1, kappa=1, window=2,
                    private_points=20, escape_points=19, lower_numerator_over_mD=12,
                    exact_escape_mass='19/75', lower_bound='4/25',
                    scope='Only the general essential-parent CVE consequence; no odd whole-cover or extremality claim.'),
                prime_parent_countercheck=dict(prime=3, source_moduli=[3, 6, 12],
                    source_points=sorted(prime_counterexample), common_target=3,
                    true_source_mass='1/4', incorrect_q_minus_one_bound='1/6'),
                literal_multi_reset_witnesses={str(y): targets for y, targets in expected.items()})


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
