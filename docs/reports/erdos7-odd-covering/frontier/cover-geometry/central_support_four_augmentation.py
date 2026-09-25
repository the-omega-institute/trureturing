#!/usr/bin/env python3
"""Pay two complete support-four slices on the Report598 source.

The 160-label and 190-label consequences use Report601 staged fees,
with every outside prime at least53 or67 respectively. Arithmetic is exact.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from math import prod
from pathlib import Path


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def cap(p, exponent):
    if exponent == 0:
        return F(1)
    if p == 3:
        return F(2, 3**exponent)
    if exponent == 1:
        return F(1, p-1)
    return F(1, (p-2)*p**(exponent-1))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    base = Path(__file__).parent
    checks, sources = {}, {}

    def require(name, condition):
        if not condition:
            raise ArithmeticError(name)
        checks[name] = True

    def load(name):
        path = base / name
        raw = path.read_bytes()
        data = json.loads(raw)
        require(name + '_checks_true', bool(data['checks'])
                and all(v is True for v in data['checks'].values()))
        require(name + '_producer_fingerprint',
                data['producer_sha256'] == sha256(path.with_suffix('.py').read_bytes()).hexdigest())
        sources[name] = dict(sha256=sha256(raw).hexdigest(),
                             producer_sha256=data['producer_sha256'])
        return data

    head = load('central_high_support_augmentation.json')
    staged = load('staged_two_parent_attachment.json')
    primes = (3, 5, 7, 11, 13, 17, 19)
    added = []
    for exponents in product(range(3), repeat=7):
        active_centres = sum(e > 0 for e in exponents[:2])
        outside_support = sum(e > 0 for e in exponents[2:])
        if active_centres != 1 or max(exponents[:2]) != 2 or outside_support != 3:
            continue
        modulus = prod(p**e for p, e in zip(primes, exponents))
        source_cap = prod(cap(p, e) for p, e in zip(primes, exponents))
        added.append(dict(modulus=modulus, exponents=exponents, source_cap=source_cap))
    added.sort(key=lambda row: row['modulus'])
    added_moduli = {row['modulus'] for row in added}
    require('160_distinct_literal_new_labels', len(added) == len(added_moduli) == 160)
    independent_labels = {centre**2 * prod(p**e for p, e in zip(support, exps))
                          for centre in (3, 5)
                          for support in combinations(primes[2:], 3)
                          for exps in product((1, 2), repeat=3)}
    require('independent_support_factorization', added_moduli == independent_labels)
    for row in added:
        require('literal_factorization_' + str(row['modulus']),
                prod(p**e for p, e in zip(primes, row['exponents'])) == row['modulus']
                and sum(e > 0 for e in row['exponents']) == 4)
    raw_cap = sum((row['source_cap'] for row in added), F())
    polynomial_cap = (F(2, 9)+F(1, 15)) * sum(
        (prod(F(1, q-1)+F(1, q*(q-2)) for q in support)
         for support in combinations(primes[2:], 3)), F())
    require('complete_160_cap_sum', raw_cap == polynomial_cap
            == F(2261681116741, 813717439920000))

    old_added = {row['modulus'] for row in head['inventory']['added']}
    old_remaining = head['inventory']['remaining']
    old_remaining_moduli = {row['modulus'] for row in old_remaining}
    require('strict_augmentation_of_598', len(old_added) == 800
            and added_moduli.isdisjoint(old_added) and added_moduli <= old_remaining_moduli)
    remaining = [row for row in old_remaining if row['modulus'] not in added_moduli]
    counts = Counter(row['support'] for row in remaining)
    require('remaining_253_complete_partition', len(remaining) == 253
            and dict(counts) == {2: 23, 3: 110, 4: 120})
    require('support_four_remainder_has_both_centres',
            all(row['exponents'][0] > 0 and row['exponents'][1] > 0
                for row in remaining if row['support'] == 4))

    c = F(head['constants']['continuation_c'])
    density = F(head['constants']['source_density_D'])
    multiplier = F(head['constants']['continuation_density_multiplier'])
    old_gate = F(head['consequence']['new_gate'])
    alpha = 1 / (density * multiplier)
    require('same_continuation_and_staged_source',
            c == F(staged['constants']['c'])
            and density == F(staged['constants']['density_D'])
            and multiplier == F(staged['constants']['continuation_multiplier'])
            and old_gate == F(staged['constants']['inherited_gate'])
            and alpha == F(staged['constants']['alpha']))
    new_gate = old_gate - (1-c)*raw_cap
    haar = alpha * new_gate
    require('strict_gate_after_all_160', new_gate
            == F(10852138121266998757700791, 74836215488560103424000000000) > 0)
    require('ten_head_haar_lower', haar
            == F(10852138121266998757700791, 3872557174103117660160000000000)
            > F(1, 360000))

    added30 = []
    for a, b in ((2, 1), (1, 2), (2, 2)):
        for pair in combinations(primes[2:], 2):
            exponents = (a, b) + tuple(2 if q in pair else 0 for q in primes[2:])
            modulus = prod(p**e for p, e in zip(primes, exponents))
            source_cap = prod(cap(p, e) for p, e in zip(primes, exponents))
            added30.append(dict(modulus=modulus, exponents=exponents, source_cap=source_cap))
    added30.sort(key=lambda row: row['modulus'])
    labels30 = {row['modulus'] for row in added30}
    require('30_distinct_both_centre_labels', len(added30) == len(labels30) == 30)
    independent30 = {row['modulus'] for row in old_remaining
                     if row['exponents'][0] > 0 and row['exponents'][1] > 0
                     and max(row['exponents'][:2]) == 2
                     and sum(e > 0 for e in row['exponents'][2:]) == 2
                     and all(e in (0, 2) for e in row['exponents'][2:])}
    require('independent_both_centre_slice', labels30 == independent30)
    for row in added30:
        require('literal_factorization_' + str(row['modulus']),
                prod(p**e for p, e in zip(primes, row['exponents'])) == row['modulus']
                and sum(e > 0 for e in row['exponents']) == 4)
    raw30 = sum((row['source_cap'] for row in added30), F())
    polynomial30 = (F(2, 9)*F(1, 4)+F(2, 3)*F(1, 15)+F(2, 9)*F(1, 15)) * sum(
        (prod(F(1, q*(q-2)) for q in pair) for pair in combinations(primes[2:], 2)), F())
    require('complete_30_cap_sum', raw30 == polynomial30 == F(564029593, 5509545166125))
    labels190 = added_moduli | labels30
    require('disjoint_800_160_30_inventory', added_moduli.isdisjoint(labels30)
            and labels30.isdisjoint(old_added) and labels190 <= old_remaining_moduli)
    remaining190 = [row for row in old_remaining if row['modulus'] not in labels190]
    counts190 = Counter(row['support'] for row in remaining190)
    require('remaining_223_complete_partition', len(remaining190) == 223
            and len(labels190) == 190 and dict(counts190) == {2: 23, 3: 110, 4: 90})
    raw190 = raw_cap + raw30
    gate190 = old_gate - (1-c)*raw190
    haar190 = alpha * gate190
    require('same_source_sequential_restriction', gate190 == new_gate-(1-c)*raw30)
    require('strict_gate_after_all_190', gate190
            == F(23005581948964911238467983, 532657769065633677312000000000) > 0)
    require('ten_head_190_haar_lower', haar190
            == F(23005581948964911238467983, 27563495180381013934080000000000)
            > F(1, 1200000))

    pair_density = F(staged['constants']['early_pair_density'])
    extensions = {}
    for count, minimum, gate, row_count, bound in (
            (160, 53, new_gate, 148, F(1, 9000000)),
            (190, 67, gate190, 145, F(1, 3400000))):
        fees = {}
        for key, table in staged['fee_tables'].items():
            rows = [row for row in table['finite_rows'] if row['entry_prime'] >= minimum]
            require(key + '_later_entries_from' + str(minimum), len(rows) == row_count
                    and rows[0]['entry_prime'] == minimum and rows[-1]['entry_prime'] == 967)
            finite = sum((F(row['blocker_fee_upper']) for row in rows), F())
            tail = F(table['analytic_tail'])
            fees[key] = dict(finite=finite, analytic_tail=tail, total=finite+tail)
        early_loss = pair_density * fees['3_5']['total']
        branch_gate = gate - (1-c)*early_loss
        branch_head = alpha * branch_gate
        ordinary_fee = F(1, 2**((minimum-3)//2))
        branch_reserve = branch_head - fees['3_23']['total'] - ordinary_fee
        require('positive_early_gate_from' + str(minimum), branch_gate > 0)
        require('ordinary_fee_geometric_from' + str(minimum),
                ordinary_fee == F(1, 2**((minimum-1)//2)) / (1-F(1, 2)))
        require('simultaneous_branch_reserve_from' + str(minimum), branch_reserve > bound)
        extensions[str(count) + '_from' + str(minimum)] = dict(
            minimum_outside_prime=minimum, fees=fees, finite_rows_per_pair=row_count,
            early_pair_density=pair_density, early_loss_upper=early_loss,
            gate_lower=branch_gate, head_lower=branch_head, ordinary_fee=ordinary_fee,
            extendible_head_lower=branch_reserve, strictly_greater_than=bound,
            full_density_lower='1/(' + str(bound.denominator) + ' Q_outside)')

    data = dict(schema='central-support-four-augmentation-v1', sources=sources,
                scope=dict(head_primes=primes, continuation_primes=[23, 29, 31],
                           added160='Exactly one of3,5, squared; exactly three of7,11,13,17,19 with exponents1 or2',
                           added30='Both3,5 with exponents(2,1),(1,2),(2,2); exactly two other primes, both squared',
                           arbitrary_original_residues=True, arbitrary_finite_heights=True,
                           transport='Any ten ordered odd primes with the same coordinate roles',
                           branch_extension='Report600 private branches:160 from53,190 from67',
                           excluded=['The remaining223 central labels', 'General cross-branch constraints',
                                     'New190 labels combined with all Report601 entries from37',
                                     'Unrestricted Erdos7 resolution', 'Lean verification']),
                constants=dict(c=c, density_D=density, continuation_multiplier=multiplier,
                               alpha=alpha, inherited_gate=old_gate),
                slices=dict(one_centre_160=dict(count=160, added=added, raw_cap=raw_cap),
                            both_centres_30=dict(count=30, added=added30, raw_cap=raw30)),
                inventory=dict(added_count=190, added=sorted(added+added30, key=lambda r:r['modulus']),
                               combined_augmentation_count=990, remaining_count=223,
                               remaining_counts_by_support=dict(counts190), remaining=remaining190,
                               intermediate_160=dict(remaining_count=253,
                                                     remaining_counts_by_support=dict(counts))),
                consequences={
                    '160': dict(raw_cap=raw_cap, gate_cost=(1-c)*raw_cap,
                                new_gate=new_gate, head_haar_lower=haar,
                                strictly_greater_than=F(1, 360000)),
                    '190': dict(raw_cap=raw190, gate_cost=(1-c)*raw190,
                                new_gate=gate190, head_haar_lower=haar190,
                                strictly_greater_than=F(1, 1200000))},
                branch_extensions=extensions,
                checks=checks, producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(data), indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks), added=190, remaining=223,
                                raw_cap=raw190, gate=gate190, head_haar_lower=haar190,
                                branch_extendible_lower={key: value['extendible_head_lower']
                                                         for key, value in extensions.items()}))))


if __name__ == '__main__':
    main()
