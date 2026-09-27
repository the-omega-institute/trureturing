"""Verify fixed actual phase-cycle obstructions for every outside law.

Root multiplicities, rather than a sampled probability vector, certify the
all-law expense. Only CRT labels and short outside periods are enumerated.
The arbitrary-depth statement is proved separately in ordinary mathematics.
"""
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
INPUT = 'phase_balanced_ancestor_input.json'
PIN = 'ab4110a23c179c2f84df7197837b6d89a174b60a21aa380d1994bb8e225a7a27'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def construct(p, primes, reference, depth, cycles):
    rows = []
    for q in primes:
        for index in range(1, cycles * q + 1):
            exponent = depth + index
            old = p ** exponent
            multiplier = ((index - reference) * pow(old, -1, q)) % q
            residue = reference + old * multiplier
            rows.append({'outside_prime': q, 'index': index,
                         'old_exponent': exponent, 'modulus': old * q,
                         'residue': residue})
    return rows


def check_rows(rows, p, primes, reference, depth, cycles, scale):
    expected_indices = {(q, i) for q in primes for i in range(1, cycles * q + 1)}
    require({(row['outside_prime'], row['index']) for row in rows} == expected_indices
            and len(rows) == len(expected_indices), 'complete original phase-cycle inventory')
    seen = set()
    multiplicities = {q: [0] * q for q in primes}
    max_exponent = 0
    for row in rows:
        q, index, exponent, m, a = (row[k] for k in ('outside_prime', 'index', 'old_exponent', 'modulus', 'residue'))
        require(exponent == depth + index and m == p ** exponent * q,
                'actual numerical factorization and old depth')
        require(m > 1 and m % 2 == 1 and m not in seen, 'distinct odd numerical moduli')
        require(0 <= a < m and a % (p ** exponent) == reference % (p ** exponent)
                and a % q == index % q, 'fixed complete CRT residue')
        require(a % (p ** (depth + 1)) == reference % (p ** (depth + 1)),
                'every actual class lies in the same old cylinder')
        seen.add(m)
        multiplicities[q][a % q] += 1
        max_exponent = max(max_exponent, exponent)
    require(all(count == cycles for counts in multiplicities.values() for count in counts),
            'equal phase multiplicities certify every outside law')
    # At each old source cofactor the only available divisors are successive p powers.
    ancestors = {exponent for row in rows for exponent in range(row['old_exponent'] + 1)}
    require(ancestors == set(range(max_exponent + 1)), 'complete reachable ancestor cut')
    demand = scale * len(primes) * cycles
    require(demand > len(ancestors), 'strict all-law Hall obstruction')
    return multiplicities, demand, len(ancestors)


def verify(input_dir):
    raw = (Path(input_dir) / INPUT).read_bytes()
    require(hashlib.sha256(raw).hexdigest() == PIN, 'pinned input')
    data = json.loads(raw)
    require(data['schema'] == 'phase-balanced-ancestor-input-v1', 'schema')
    p, primes, reference, scale = (data[k] for k in ('old_prime', 'outside_primes', 'old_reference', 'pure_axis_scale'))
    require((p, primes, reference, scale) == (3, [23, 29, 31], 1, 28), 'declared fixed arithmetic interface')
    source_cap = Fraction(data['source_domination'])
    require(source_cap == Fraction(27, 2), 'inherited source domination constant')
    results = []
    for case in data['cases']:
        depth, cycles = case['old_depth'], case['cycles']
        primes = case['active_outside_primes']
        require(primes in ([29, 31], [23, 29, 31]), 'declared active outside prime set')
        require(type(depth) is int and depth >= 0 and type(cycles) is int and cycles >= 1,
                'finite natural depth and positive cycles')
        rows = construct(p, primes, reference, depth, cycles)
        multiplicities, demand, capacity = check_rows(rows, p, primes, reference, depth, cycles, scale)
        mass = Fraction(1, p ** (depth + 1))
        require(demand == 28 * len(primes) * cycles and capacity == depth + 31 * cycles + 1,
                'literal universal-demand and ancestor-capacity formulas')
        require(demand - capacity == (28 * len(primes) - 31) * cycles - depth - 1, 'capacity deficit formula')
        # Every elementary outside law gives the same cost; arbitrary laws are their mixtures.
        outside_period = 1
        for q in primes:
            outside_period *= q
        point_costs = {scale * sum(multiplicities[q][x % q] for q in primes)
                       for x in range(outside_period)}
        require(point_costs == {demand}, 'pointwise constant expense on the entire outside period')
        partitions = []
        if len(primes) == 3:
            for mask in range(8):
                groups = {side: [q for j, q in enumerate(primes) if bool(mask & (1 << j)) == (side == 'R')]
                          for side in ('R', 'S')}
                cuts = {}
                for side, selected in groups.items():
                    ancestors = {e for row in rows if row['outside_prime'] in selected
                                 for e in range(row['old_exponent'] + 1)}
                    cost = (22 if side == 'R' else 28) * len(selected) * cycles
                    cuts[side] = {'primes': selected, 'expense': cost, 'capacity': len(ancestors),
                                  'deficit': cost - len(ancestors)}
                require(any(c['deficit'] > 0 for c in cuts.values()), 'every grouping has a failing pure account')
                partitions.append(cuts)
        sample_rows = [row for row in rows if row['index'] in (1, cycles * row['outside_prime'])]
        results.append({'old_depth': depth, 'cycles': cycles, 'original_count': len(rows),
                        'phase_multiplicities': {str(q): counts for q, counts in multiplicities.items()},
                        'universal_scaled_expense': demand, 'reachable_ancestor_columns': capacity,
                        'strict_deficit': demand - capacity, 'nonunit_Haar_deletion_upper': str(mass),
                        'conditional_source_deletion_upper': str(source_cap * mass),
                        'Haar_survival_lower': str(1 - mass), 'outside_period': outside_period, 'all_grouping_cuts': partitions,
                        'outside_point_costs': sorted(point_costs),
                        'actual_labels_sha256': hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest(),
                        'extreme_actual_labels': sample_rows})
    return {'schema': 'phase-balanced-ancestor-result-v1', 'input_sha256': PIN,
            'cases': results,
            'scope': 'Fixed CRT and phase-multiplicity controls for an all-law raw-transport obstruction. Arbitrary-depth proof is ordinary mathematics. The constructed families are noncovering; no unrestricted conclusion, source reconstruction or Lean verification.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.input_dir)
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    else:
        require(encoded == Path(__file__).with_suffix('.json').read_text(), 'retained exact result mismatch')
    print(json.dumps([{k: case[k] for k in ('old_depth', 'cycles', 'original_count',
                     'universal_scaled_expense', 'reachable_ancestor_columns', 'strict_deficit')}
                      for case in result['cases']], indent=2))


if __name__ == '__main__':
    main()
