"""Check a literal mixed parent exchange and every older ML6 union cap.

Usage: python3 -I -S -B mixed_parent_exchange.py --input INPUT.json --output OUTPUT.json
Requires Python 3.9+ with only its standard library; no installation is needed.
Checks remain enabled under -O. Input and output paths are explicit.
"""
import argparse
from collections import defaultdict
from itertools import combinations, product
import json
from math import isqrt, lcm
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def divisors(n):
    low = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return sorted(set(low + [n // d for d in low]))


def valuation(n, p):
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def class_map(rows, label):
    require(isinstance(rows, list) and bool(rows), label + ': nonempty list required')
    result = {}
    for row in rows:
        require(isinstance(row, list) and len(row) == 2, label + ': pair required')
        d, a = row
        require(type(d) is int and type(a) is int and d > 1 and d % 2 == 1,
                label + ': odd nonunit modulus and integer residue required')
        require(0 <= a < d and d not in result, label + ': noncanonical residue or duplicate')
        result[d] = a
    return result


def repair_count(h, p, Q):
    H, a = valuation(Q, p), valuation(h, p)
    t = len(divisors(h // p ** a))
    r = p ** (H - a + 1)
    if p * t <= (p - 1) * r:
        return None
    if t >= r:
        return r
    delta = p * t - (p - 1) * r
    J = 0
    while p ** J * delta < t:
        J += 1
    numerator = p * t - p ** J * delta
    require(numerator % (p - 1) == 0, 'nonintegral final layer')
    return t * J + numerator // (p - 1)


def check(data):
    original = class_map(data['classes'], 'original')
    labels = sorted(original)
    Q = lcm(*labels)
    require(all(e in original for d in labels for e in divisors(d) if e > 1),
            'original palette is not divisor-closed above one')
    require(all(original[p] == 0 for p in labels if prime(p)), 'prime classes not normalized')
    comparable = [(d, e) for d, e in combinations(labels, 2) if e % d == 0]
    require(all(original[e] % d != original[d] for d, e in comparable),
            'comparable originals intersect')
    private_counts = dict.fromkeys(labels, 0)
    private_witnesses = {}
    original_covered = 0
    for x in range(Q):
        owners = [d for d in labels if x % d == original[d]]
        original_covered += bool(owners)
        if len(owners) == 1:
            d = owners[0]
            private_counts[d] += 1
            private_witnesses.setdefault(d, x)
    require(all(private_counts.values()), 'some original has no private point')

    # Any interface with a nonempty parent set divides an original, hence is in D.
    # ML2 implies tau(h/p^a) >= p, so primes above this finite bound cannot qualify.
    tau_bound = max(len(divisors(h)) for h in labels)
    candidate_primes = [p for p in range(3, tau_bound + 1, 2) if prime(p)]
    interfaces = []
    subset_count = choice_count = explicit_empty_count = 0
    for h in labels:
        for p in candidate_primes:
            N = repair_count(h, p, Q)
            if N is None:
                continue
            old_groups = defaultdict(list)
            for d in labels:
                if d % h == 0:
                    old_groups[original[d] % h].append(d)
            maximum = 0
            local_subsets = local_choices = 0
            for old_phase, available in sorted(old_groups.items()):
                for mask in range(1, 1 << len(available)):
                    parents = {d for i, d in enumerate(available) if mask >> i & 1}
                    menus = []
                    for d in sorted(parents):
                        groups = defaultdict(set)
                        for m in labels:
                            if m not in parents and m > d and m % d == 0:
                                groups[original[m] % d].add(m)
                        menu = list(groups.values())
                        # Choosing an unoccupied new phase yields the empty group.
                        # It cannot increase any union; include it explicitly anyway.
                        if len(groups) < d:
                            menu.append(set())
                            explicit_empty_count += 1
                        menus.append(menu)
                    local_subsets += 1
                    for selection in product(*menus):
                        deleted = set().union(*selection)
                        local_choices += 1
                        maximum = max(maximum, len(deleted))
                        require(len(deleted) <= N - 1,
                                'old ML6 cap fails at ' + str((h, p, old_phase, sorted(parents))))
            subset_count += local_subsets
            choice_count += local_choices
            interfaces.append({'h': h, 'p': p, 'N': N, 'max_deleted_union': maximum,
                               'parent_subsets': local_subsets, 'phase_group_choices': local_choices})

    h, p, c = (data['interface'][key] for key in ('h', 'p', 'old_phase'))
    require(h in original and prime(p) and p % 2 == 1 and 0 <= c < h,
            'invalid exchange interface')
    N = repair_count(h, p, Q)
    require(N is not None, 'exchange interface is not ML2-qualified')
    moved = class_map(data['moved'], 'moved')
    E, J = set(data['deleted_parents']), set(data['deleted_children'])
    require(len(E) == len(data['deleted_parents']) and len(J) == len(data['deleted_children']),
            'duplicate deleted label')
    R = set(moved)
    P = R | E
    require(R.isdisjoint(E) and P.isdisjoint(J) and P | J <= set(original),
            'exchange label sets not disjoint original subsets')
    require(all(d % h == 0 and original[d] % h == c for d in P),
            'selected OLD parents do not share the declared h-phase')
    actual_J = {m for m in labels if m not in P and any(
        m > d and m % d == 0 and original[m] % d == b for d, b in moved.items())}
    require(J == actual_J, 'deleted children are not the exact selected phase union')
    repairs = class_map(data['repairs'], 'repairs')
    require(set(repairs).isdisjoint(original), 'repair label is not fresh')
    H, a = valuation(Q, p), valuation(h, p)
    n = h // p ** a
    require(all(valuation(d, p) > H and n % (d // p ** valuation(d, p)) == 0
                for d in repairs), 'repair outside ML1 palette')
    require(len(repairs) == N, 'repair has wrong minimum-cardinality count')
    repair_period = lcm(h, *repairs)
    require(all(any(x % d == b for d, b in repairs.items())
                for x in range(c, repair_period, h)), 'repair fails on the full target class')
    S = sum(repairs)
    require(S < h * N * N, 'repair fails the strict sum comparison')
    require(len(E) + len(J) > N - 1, 'fixture does not violate mixed bound')
    replacement = {d: b for d, b in original.items() if d not in E | J}
    replacement.update(moved)
    replacement.update(repairs)
    period = lcm(Q, *replacement)
    counts = {'old_covered': 0, 'new_covered': 0, 'lost': 0, 'added': 0}
    for x in range(period):
        old = any(x % d == b for d, b in original.items())
        new = any(x % d == b for d, b in replacement.items())
        counts['old_covered'] += old
        counts['new_covered'] += new
        counts['lost'] += old and not new
        counts['added'] += new and not old
    require(counts['lost'] == 0, 'replacement loses old covered points')
    require(len(replacement) == len(original) and sum(replacement) < sum(original),
            'claimed tie-count sum improvement fails')
    hole = data['persistent_hole']
    require(not any(hole % d == b for d, b in original.items()) and
            not any(hole % d == b for d, b in replacement.items()), 'claimed hole is covered')
    return {'scope': 'finite noncover control; ordinary exact arithmetic, not Lean verification',
            'original_period': Q, 'original_covered': original_covered,
            'original_holes': Q - original_covered, 'comparable_pairs': len(comparable),
            'private_counts': private_counts, 'private_witnesses': private_witnesses,
            'exhaustion': {'max_tau': tau_bound, 'candidate_primes': candidate_primes,
                           'qualified_interfaces': len(interfaces), 'parent_subsets': subset_count,
                           'phase_group_choices': choice_count,
                           'explicit_empty_menu_options': explicit_empty_count},
            'old_ML6_interfaces': interfaces,
            'exchange': {'h': h, 'p': p, 'N': N, 'B': N - 1,
                         'deleted_parents': sorted(E), 'deleted_children': sorted(J),
                         'repair_sum': S, 'removed_sum': sum(E | J),
                         'class_count': len(original), 'old_sum': sum(original),
                         'new_sum': sum(replacement), 'persistent_hole': hole,
                         'comparison_period': period, **counts}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    result = check(json.loads(args.input.read_text(encoding='utf-8')))
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
