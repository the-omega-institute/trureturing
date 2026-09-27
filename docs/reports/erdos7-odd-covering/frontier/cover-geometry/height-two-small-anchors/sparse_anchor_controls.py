"""Independent exact controls of actual common laws; not Lean certification.
Python 3 standard library; run with --output PATH from any working directory.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import reduce
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import json


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


COEFF = (1, 3, 3, 5, 9, 5, 15, 15, 25)
DIVISORS = (1, 5, 7, 25, 35, 49, 175, 245, 1225)
B3_CAPS = tuple(map(Q, ('1', '25/84', '3/7', '5/28', '5/42', '5/28', '1/14', '5/84', '1/28')))
B4_CAPS = tuple(map(Q, ('1', '25/87', '12/29', '5/29', '10/87', '5/29', '2/29', '5/87', '1/29')))
H4_CAPS = tuple(map(Q, ('1', '2/7', '3/7', '6/35', '1/7', '1/7', '3/35', '1/21', '1/28')))
NS = {0: 4, 1: 5, 2: 5, 3: 5}
CHOICES = {r: list(combinations(range(n), 2 if r == 0 else 3)) for r, n in NS.items()}


def actual_control(kind):
    all49 = set(product(range(7), repeat=2))
    fibres = {(r, c): set(all49) for r, n in NS.items() for c in range(n)}
    if kind == 'H4-two':
        root = 0
        anchor_labels = {(0, 0), (0, 1), (0, 2)}
        for c in range(3):
            fibres[root, c] = {(0, 0), (0, c + 1)}
        eta_points = [(root, 0, 0, 0), (root, 0, 0, 1), (root, 1, 0, 2), (root, 2, 0, 3)]
        alpha, beta, bounds = Q(6, 7), Q(1, 7), H4_CAPS
        anchor_children = (0, 1)
    else:
        root = 1
        label_count = 3 if kind == 'B3' else 4 if kind == 'B4-spread' else int(kind[1:])
        anchor_labels = {(0, 0), (0, 1)} | {(g, 0) for g in range(1, label_count - 1)}
        require(3 <= label_count <= 8 and all(0 <= g < 7 for g, h in anchor_labels), 'original seven-column domain')
        fibres[root, 0] = set(anchor_labels)
        fibres[root, 1] = {(0, 0)}
        fibres[root, 2] = {(0, 0)}
        eta_points = [(root, 1, 0, 0)] + [(root, 0, g, h) for g, h in sorted(anchor_labels - {(0, 0)})]
        denominator = 25 + label_count
        alpha, beta = Q(25, denominator), Q(label_count, denominator)
        bounds = (Q(1), Q(25, 3 * denominator), Q(12, denominator),
                  Q(max(5, label_count - 1), denominator), Q(10, 3 * denominator),
                  Q(5, denominator), Q(2, denominator), Q(5, 3 * denominator), Q(1, denominator))
        require(sum(x * c for x, c in zip(bounds, COEFF)) == 1 + Q(196 + 5 * max(5, label_count - 1), denominator), 'general sparse-anchor envelope')
        anchor_children = (0, 1, 2)
    require(set().union(*(fibres[root, c] for c in anchor_children)) == anchor_labels, 'complete original anchor projection')
    tests = 0
    for r, s in combinations(range(4), 2):
        for cs in CHOICES[r]:
            for ds in CHOICES[s]:
                leaves = set().union(*(fibres[r, c] for c in cs), *(fibres[s, c] for c in ds))
                require(sum(sum(g == i for g, h in leaves) >= 3 for i in range(7)) >= 3, 'complete original paired restriction')
                tests += 1
    psi = defaultdict(Q)
    for r in range(4):
        if r == root:
            continue
        for cs in CHOICES[r]:
            leaves = set().union(*(fibres[r, c] for c in cs))
            if kind == 'H4-two':
                selected = [(g, h) for g in (1, 2) for h in range(3)]
            else:
                tree = [(g, h) for g in (0, 1, 2) for h in sorted(h for gg, h in leaves - anchor_labels if gg == g)[:3]]
                require(len(tree) == 9 and set(tree) <= leaves | anchor_labels, 'actual paired ternary tree')
                selected, columns = [], Counter()
                for point in sorted(set(tree) - anchor_labels):
                    if columns[point[0]] < 2 and len(selected) < 5:
                        selected.append(point)
                        columns[point[0]] += 1
                require(len(selected) == 5, 'balanced remaining selection')
            for g, h in selected:
                c = next(c for c in cs if (g, h) in fibres[r, c])
                psi[r, c, g, h] += Q(1, 3 * len(CHOICES[r]) * len(selected))
    require(sum(psi.values()) == 1, 'one psi normalized')
    require(not any((g, h) in anchor_labels for r, c, g, h in psi), 'global complete F avoidance')
    if kind == 'H4-two':
        require(not any(g == 0 for r, c, g, h in psi), 'global monochromatic column avoidance')
    law = {point: alpha * mass for point, mass in psi.items()}
    for point in eta_points:
        law[point] = law.get(point, Q()) + beta / len(eta_points)
    require(sum(law.values()) == 1 and all((g, h) in fibres[r, c] for r, c, g, h in law), 'one law on complete actual source')
    caps = []
    for divisor, bound in zip(DIVISORS, bounds):
        masses = [Q() for _ in range(divisor)]
        for (r, c, g, h), mass in law.items():
            a, b = r + 5 * c, g + 7 * h
            x = (a + 50 * (b - a)) % 1225
            require(x % 25 == a and x % 49 == b, 'literal CRT encoding')
            masses[x % divisor] += mass
        caps.append(max(masses))
        require(max(masses) <= bound, 'actual numerical cylinder cap')
    return {'name': kind, 'complete_source_points': sum(map(len, fibres.values())),
            'all_original_pair_tests': tests, 'numerical_cylinders': sum(DIVISORS),
            'psi_global_F_mass': '0', 'actual_caps': list(map(str, caps)),
            'actual_envelope': str(sum(x * c for x, c in zip(caps, COEFF)))}


def remaining_shape_inventory():
    remaining = []
    for capacity in range(75, 82):
        for n in (4, 5):
            q = 2 if n == 4 else 3
            for delta in range(3):
                for public in range(3):
                    for private in combinations_with_replacement(range(4), n - delta):
                        if 63 + 7 * (delta + public) + 2 * sum(private) != capacity:
                            continue
                        if public == 0 and 0 in private:
                            continue
                        cheap = len(private) >= q and public + sum(private[:q]) <= 2
                        four_singletons = n == 5 and public == 0 and private.count(1) >= 4
                        full_11122 = n == 5 and public == 0 and delta == 0 and private == (1, 1, 1, 2, 2)
                        gap_1222 = n == 4 and public == 0 and delta == 0 and private == (1, 2, 2, 2)
                        common_singletons = public == 1 and delta == 0 and private == ((0, 1, 1, 1, 1) if n == 5 else (1, 1, 1, 1))
                        if not any((cheap, four_singletons, full_11122, gap_1222, common_singletons)):
                            remaining.append((capacity, n, delta, public, ''.join(map(str, private))))
    require(len(remaining) == 14 and sum(row[0] <= 80 for row in remaining) == 9, 'necessary IA-unhandled inventory')
    return remaining


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(sum(x * c for x, c in zip(B3_CAPS, COEFF)) == Q(249, 28), 'B3 rational envelope')
    require(sum(x * c for x, c in zip(H4_CAPS, COEFF)) == Q(249, 28), 'H4-two rational envelope')
    require(sum(x * c for x, c in zip(B4_CAPS, COEFF)) == Q(250, 29), 'B4-spread rational envelope')
    owner_counts = {}
    for labels, max_owner in ((3, 2), (4, 3)):
        for owners in (2, 3):
            count = 0
            for sets in product(range(1, 2 ** labels), repeat=owners):
                if reduce(int.__or__, sets) != 2 ** labels - 1:
                    continue
                require(any(max(Counter(a).values()) <= max_owner for a in product(range(owners), repeat=labels)
                            if all(sets[a[label]] & (1 << label) for label in range(labels))), 'actual bounded owner assignment')
                count += 1
            owner_counts[f'{labels}_labels_{owners}_owners'] = count
    sparse_envelopes = {n: 1 + Q(196 + 5 * max(5, n - 1), 25 + n) for n in range(3, 9)}
    require(list(sparse_envelopes.values()) == list(map(Q, ('249/28', '250/29', '251/30', '252/31', '129/16', '8'))), 'all six exact sparse-anchor values')
    require(max(sparse_envelopes.values()) == Q(249, 28), 'uniform sparse-anchor bound')
    result = {'result': 'PASS', 'actual_controls': [actual_control(kind) for kind in ('B3', 'H4-two', 'B4-spread', 'B5', 'B6', 'B7', 'B8')],
              'sparse_anchor_envelopes': {str(n): str(v) for n, v in sparse_envelopes.items()},
              'owner_incidence_pattern_counts': owner_counts, 'necessary_IA_unhandled_shapes_75_81': remaining_shape_inventory(),
              'scope': 'Independent exact finite common-law controls and necessary cost-shape arithmetic; no Lean, no exhaustive actual-source enumeration, no realization claim for cost shapes.'}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
