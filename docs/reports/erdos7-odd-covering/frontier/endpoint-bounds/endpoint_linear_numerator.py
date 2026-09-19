#!/usr/bin/env python3
"""Exact arithmetic for the endpoint joint linear numerator bound in note59.

Standard library, read-only unless --output is given. The ordinary proof
handles arbitrary original labels and limiting families. The finite probes
also compute all-test suprema, with exact periodic tails, on two fixed sources.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PINS = {
    'verify_joint_frontier.py': '85341d7f8fa2d0b109697bc17b005a7e75f7f6ec412fd2eb3d26383cf9fce24f',
    'frontier/source-budgets/sharp_source_mass_endpoints.py': '79bb947d96c36895069f58568d7a5de2c22aa561753f03352e9eb741313147d9',
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
}
FRONTIER_PIN = '98631aaec7edbf0bbec41befad13df4ae9bcab2f6163675da10d8d7c9273c44c'
ROOT = (0, 0, 1, 1, 1)
ETA = tuple(map(F, ('1/18', '1/9', '1/9', '1/9', '1/9')))
MASS = tuple(map(F, ('1/24', '1/12', '1/36', '1/24', '1/18')))
LATE_INTERVAL = (F(1, 90), F(1, 72))
SLOTS = ('pure5_first', 'alpha_first', 'beta_first', 'higher_tail', 'source_free')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(base, relative, name):
    path = base/relative
    require(sha256(path.read_bytes()).hexdigest() == PINS[relative], 'Pinned source: '+relative)
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned source')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def slot_matrices(late_beta):
    """Source masses, then four retained common-deletion cofactor families."""
    require(LATE_INTERVAL[0] <= late_beta <= LATE_INTERVAL[1], 'Endpoint late deletion interval')
    source = []
    for cell, eta in enumerate(ETA):
        row = [F(0), eta/5 if ROOT[cell] == 0 else F(0),
               eta/5 if cell != 2 else F(0),
               eta*(F(3, 20) if ROOT[cell] == 0 else F(1, 20) if cell == 2 else F(1, 10)),
               eta/5]
        if cell == 3:
            row[2] -= late_beta
            row[3] -= F(1, 72)-late_beta
        require(min(row) >= 0 and sum(row) == MASS[cell], 'Actual endpoint row mass')
        source.append(row)
    kept = [[source[cell][slot]*(1-F(int(ROOT[cell] == 0)+int(cell == 1)
                                     +int(slot == 4)+int(ROOT[cell] == 1 and slot == 4), 5))
             for slot in range(5)] for cell in range(5)]
    require(all(0 <= kept[cell][slot] <= source[cell][slot]
                for cell, slot in product(range(5), repeat=2)), 'Positive selected-deletion remainder')
    return source, kept


def endpoint_tables():
    tables = []
    for late_beta in LATE_INTERVAL:
        source, kept = slot_matrices(late_beta)
        columns = [sum(kept[cell][slot] for cell in range(5)) for slot in range(5)]
        roots = [[sum(kept[cell][slot] for cell in range(5) if ROOT[cell] == root)
                  for slot in range(5)] for root in range(2)]
        require(max(columns) == F(1, 18), 'Every original label5 cylinder has surviving mass at most1/18')
        require(max(map(max, roots)) == F(1, 25), 'Every original label15 cylinder has surviving mass at most1/25')
        tables.append({'late_in_beta_first': late_beta, 'source_cell_slots': source,
                       'selected_deletion_remainder': kept, 'slot_caps': columns,
                       'root_slot_caps': roots})
    # The entries depend affinely on the only remaining parameter, so both
    # interval endpoints give every intermediate slot bound as well.
    cells = [MASS[cell]*(1-F(int(ROOT[cell] == 0)+int(cell == 1), 5))
             -ETA[cell]*F(1+int(ROOT[cell] == 1), 20) for cell in range(5)]
    roots = [sum(cells[cell] for cell in range(5) if ROOT[cell] == root) for root in range(2)]
    require(cells == list(map(F, ('11/360', '2/45', '1/60', '11/360', '2/45'))),
            'Complete positive-five cofactor tails yield exact cell cap table')
    require(roots == [F(3, 40), F(11, 120)], 'Exact root cap table')
    old_caps = {3: F(1, 8), 9: F(1, 12), 5: F(1, 10), 15: F(1, 15)}
    new_caps = {3: max(roots), 9: max(cells), 5: F(1, 18), 15: F(1, 25)}
    loss = sum(old_caps[label]-new_caps[label] for label in old_caps)
    require(loss == F(43, 300), 'Four original-label source/deletion losses')
    d = tuple(map(F, ('3/4', '3/4', '1/4', '1/2', '1/2')))
    deep3_coefficients = [d[cell]*(1-F(int(ROOT[cell] == 0)+int(cell == 1), 5))
                          -F(1+int(ROOT[cell] == 1), 20) for cell in range(5)]
    require(max(deep3_coefficients) == F(11, 20), 'Uniform all-depth pure3 test cap')
    deep3_loss = (max(d)-max(deep3_coefficients))*F(1, 18)
    pure5_coefficient = sum(ETA[cell]*(1-F(int(ROOT[cell] == 0)+int(cell == 1), 5))
                            for cell in range(5))
    pure5_loss = (sum(ETA)-pure5_coefficient)*F(1, 20)
    require((deep3_loss, pure5_coefficient, pure5_loss) == (F(1, 90), F(4, 9), F(1, 360)),
            'Additional complete test-tail improvements')
    tail_loss = deep3_loss+pure5_loss
    require(tail_loss == F(1, 72), 'Complete tail improvement beyond the four shallow tests')
    # Seven cofactor categories, each with its complete geometric exponent tails.
    source_caps = {'3': F(1, 8), '9': F(1, 12), 'deep3': F(3, 4)*F(1, 18),
                   'pure5': sum(ETA)/4, '3_times5': sum(ETA[2:])/4,
                   '9_times5': max(ETA)/4, 'deep35': F(1, 18)*F(1, 4)}
    require(sum(source_caps.values()) == F(1, 2), 'Complete nonunit raw35 linear cap sum')
    require(F(1, 18)*F(1, 5) == LATE_INTERVAL[0], 'Full late b=1 budget lies in beta first slot')
    require(F(1, 18)*F(1, 4) == LATE_INTERVAL[1], 'Complete late35 budget')
    S = F(3, 20)
    four_label_zero7 = S+sum(source_caps.values())-loss
    zero7 = four_label_zero7-tail_loss
    positive7 = F(1, 5)*(F(1, 4)+sum(source_caps.values()))
    numerator = zero7+positive7
    require(four_label_zero7+positive7 == F(197, 300), 'Four-label intermediate numerator bound')
    require(numerator == F(1157, 1800), 'Absolute full357 surviving-load endpoint bound')
    return {'slots': SLOTS, 'late_interval': LATE_INTERVAL, 'endpoint_tables': tables,
            'all_positive5_cell_caps': cells, 'all_positive5_root_caps': roots,
            'old_cylinder_caps': old_caps, 'new_cylinder_caps': new_caps,
            'complete_source_cap_categories': source_caps, 'four_label_loss': loss,
            'deep3_cap_coefficients': deep3_coefficients, 'deep3_tail_loss': deep3_loss,
            'pure5_deep_cap_coefficient': pure5_coefficient, 'pure5_tail_loss': pure5_loss,
            'complete_test_tail_loss': tail_loss, 'total_cylinder_loss': loss+tail_loss,
            'four_label_numerator_upper': four_label_zero7+positive7,
            'zero7_upper': zero7, 'positive7_upper': positive7, 'linear_numerator_upper': numerator,
            'surviving_mass': S, 'absolute_margin_C6': 6*S-numerator}


def periodic_linear_norm(values, height, denominator):
    """Sum of independently maximizing cylinder masses, including both tails."""
    width3, width5 = 3**height, 5**height
    caps = {}
    for a, b in product(range(height+1), repeat=2):
        mod3, mod5 = 3**a, 5**b
        counts = [0]*(mod3*mod5)
        for x, row in enumerate(values):
            start = (x % mod3)*mod5
            for y, weight in enumerate(row):
                counts[start+y % mod5] += weight
        caps[a, b] = F(max(counts), width3*width5*denominator)
    norm = sum((F(3, 2) if a == height else 1)*(F(5, 4) if b == height else 1)*cap
               for (a, b), cap in caps.items())
    return norm, caps


def finite_source(constructor, height):
    width3, width5 = 3**height, 5**height
    all_five = (1 << width5)-1
    source = [all_five]*width3
    groups = {j: [0]*width3 for j in (1, 2, 3, 5)}
    cache = {}

    def cylinder(depth, residue):
        key = depth, residue
        if key not in cache:
            cache[key] = sum(1 << y for y in range(residue, width5, 5**depth))
        return cache[key]

    for a, b in product(range(height+1), repeat=2):
        if a+b == 0:
            continue
        aa, ra, bb, rb = constructor.source(a, b, 'off-diagonal')
        removed = cylinder(bb, rb)
        for x in range(ra, width3, 3**aa):
            source[x] &= all_five ^ removed
        group, aa, ra, bb, rb = constructor.mixed(a, b, 'off-diagonal')
        removed = cylinder(bb, rb)
        for x in range(ra, width3, 3**aa):
            require(not (groups[group][x] & removed), 'Exact within-class cofactor disjointness')
            groups[group][x] |= removed
    kappa = (1-F(1, 7**height))/(5+F(1, 7**height))
    pure7_mass = (5+F(1, 7**height))/6
    raw = [[int((source[x] >> y) & 1) for y in range(width5)] for x in range(width3)]
    kept = [[raw[x][y]*(kappa.denominator-kappa.numerator
                       *sum((row[x] >> y) & 1 for row in groups.values()))
             for y in range(width5)] for x in range(width3)]
    require(min(map(min, kept)) >= 0, 'Actual normalized surviving marginal is nonnegative')
    source_norm, source_caps = periodic_linear_norm(raw, height, 1)
    survivor_norm, _ = periodic_linear_norm(kept, height, kappa.denominator)
    S = F(sum(map(sum, kept)), width3*width5*kappa.denominator)
    # Every positive-seven test cylinder can lie in the unused first7 class4.
    full_norm = survivor_norm+source_norm/(6*pure7_mass)
    return {'height': height, 'source_mass': source_caps[0, 0], 'surviving_mass': S,
            'pure7_normalizer': pure7_mass, 'raw35_all_test_supremum': source_norm,
            'surviving35_all_test_supremum': survivor_norm,
            'full357_all_test_supremum': full_norm,
            'complete_periodic_tail_factors': [F(3, 2), F(5, 4)]}


def calculate(base):
    source = load(base, 'verify_joint_frontier.py', 'endpoint_linear_source')
    constructor = load(base, 'frontier/source-budgets/sharp_source_mass_endpoints.py', 'endpoint_linear_constructor')
    io = load(base, 'certificate_io.py', 'endpoint_linear_certificate_io')
    dat = source.data(list(source.vertices())[404])
    require(dat[1:3] == (MASS, ETA) and dat[3:] == (F(1, 4), F(3, 20)), 'Original source vertex404')
    raw = io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/full_linear_carrier_frontier.json')
    require(sha256(raw).hexdigest() == FRONTIER_PIN, 'Logical predecessor frontier certificate hash')
    frontier = json.loads(raw)['frontier']
    row = next(row for block in frontier['row_blocks'] for row in block if row['index'] == 404)
    direction = row['linear_directions'][40]
    require(direction['name'] == 'linear' and F(direction['constant']) == 6
            and frontier['carriers'][8] == [0, 1], 'Actual live linear direction40 and carrier')
    old_margin, weight = F(direction['conditional'][8]), F(direction['weight'])
    require(old_margin == F(4507, 24300) and weight > 0, 'Old exact positive-weight margin')
    endpoint = endpoint_tables()
    improvement = endpoint['absolute_margin_C6']-old_margin
    require(endpoint['absolute_margin_C6'] == F(463, 1800) and improvement == F(3487, 48600),
            'Absolute margin and comparison with the old live direction')
    finite = [finite_source(constructor, height) for height in (3, 4)]
    require(finite[0]['full357_all_test_supremum'] > endpoint['linear_numerator_upper']
            > finite[1]['full357_all_test_supremum'],
            'A finite source refutes unqualified extension of the endpoint bound')
    return {'schema': 'erdos7-endpoint-linear-numerator-v1', 'source_sha256': PINS,
            'predecessor_logical_certificate_sha256': FRONTIER_PIN, 'source_vertex': 404,
            'carrier': [0, 1], 'direction': 40, 'cost': 'f(v)=v', 'barrier': F(6),
            'direction_weight': weight, 'old_margin': old_margin, 'endpoint': endpoint,
            'absolute_margin_improvement': improvement, 'fixed_source_all_test_suprema': finite,
            'scope': ('Ordinary endpoint and approaching-sequence bound for arbitrary independently '
                      'labelled original357 linear tests. Exact rational cap tables and fixed-source '
                      'all-test suprema are checked here. No finite-neighborhood or global K bound '
                      'and no Lean verification are claimed.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    if args.check:
        certificate = args.base/'certificates/source_norms/endpoint-bounds/endpoint_linear_numerator.json'
        require(json.loads(certificate.read_text()) == result, 'Exact canonical certificate reconstruction')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS: endpoint linear numerator1157/1800, absolute margin463/1800, improvement3487/48600.')
    print('Two fixed-source complete test suprema checked; endpoint scope is essential.')


if __name__ == '__main__':
    main()
