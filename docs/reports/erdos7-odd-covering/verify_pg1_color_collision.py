#!/usr/bin/env python3
"""Exact original-label color obstruction over one actual PG1 source law.

The old family consists of the eleven PG1 classes and pure zero classes
modulo 11, 121, 13 and 169. Eighteen new mixed 17 classes have old cofactors
d*t, with d in (3,5,7) and t in (1,11,13,121,143,169). Their old cylinders
form K18 although at most twelve are active in any supported old row.

Every assignment of the eighteen classes to current roots is dominated,
for mixed union and assigned charge, by a partition into sixteen nonempty
non-pure roots. The 816 triple partitions and 9180 two-pair partitions
are all enumerated with exact integers. A concrete partition attains both
optima and is independently replayed through actual CRT residue tests and
the distortion kernel. Large old periods are handled by exact cylinder
counts; they are never expanded into all their residues.

This verifies the stated fixed original inventory and source probability.
It does not optimize complete-test energy or improve a full Gamma bound.
All checks remain active under python -O. Only the standard library is used.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import comb, gcd, lcm
from pathlib import Path
import argparse
import json


HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-color-collision-v1'
SOURCE = 'mod3_conditioned_geometry_certificate.json'
OLD_BASE = 315
P = 17
DELTA = F(7, 15)
BASE_CYLINDERS = ((3, 2), (5, 4), (7, 4))
MULTIPLIERS = ((1, 0, 0), (11, 1, 0), (13, 0, 1),
               (121, 2, 0), (143, 1, 1), (169, 0, 2))


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def digest(value):
    data = json.dumps(encode(value), sort_keys=True, separators=(',', ':')).encode()
    return sha256(data).hexdigest()


def crt(d, a, q, b):
    require(d > 0 and q > 0 and gcd(d, q) == 1 and 0 <= a < d and 0 <= b < q,
            'admissible CRT input')
    residue = a+d*((b-a)*pow(d, -1, q) % q)
    require(0 <= residue < d*q and residue % d == a and residue % q == b,
            'exact CRT residue')
    return residue


def normalized_kernel(alpha):
    clipped = min(alpha, DELTA)
    g = 1/(1-clipped)
    h = clipped/(alpha*(1-clipped)) if alpha else F()
    beta = max(F(), alpha-DELTA)/(1-DELTA)
    require(0 <= alpha <= 1 and g-h*alpha == 1 and g-h >= 0,
            'normalized nonnegative distortion kernel')
    return g, h, beta


def charge_numerator(occupied):
    require(type(occupied) is int and 0 <= occupied <= 16, 'occupied surviving roots')
    return max(15*occupied-112, 0)


def categories(p):
    """Exact partition of nonzero-root residues modulo p squared."""
    result = [
        {'depth': 0, 'representative': 2, 'count': (p-2)*p},
        {'depth': 1, 'representative': 1+p, 'count': p-1},
        {'depth': 2, 'representative': 1, 'count': 1},
    ]
    direct = [0, 0, 0]
    for y in range(p*p):
        if y % p:
            depth = 2 if y == 1 else 1 if y % p == 1 else 0
            direct[depth] += 1
    require(direct == [row['count'] for row in result]
            and sum(direct) == p*(p-1), 'literal prime-square category counts')
    for row in result:
        y = row['representative']
        require(y % p and all((y % p**e == 1) == (row['depth'] >= e)
                             for e in (1, 2)), 'category residue predicates')
    return result


def load_source(directory, expected_hashes):
    raw = (directory/SOURCE).read_bytes()
    hashes = {SOURCE: sha256(raw).hexdigest()}
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'unchanged canonical source certificate')
    source = json.loads(raw)
    require(source['schema'] == 'erdos7-mod3-conditioned-geometry-v1', 'source schema')
    cases = [case for case in source['cases'] if case['name'] == 'PG1']
    require(len(cases) == 1, 'unique PG1 source')
    case = cases[0]
    points, weights, den = case['points'], case['weight_numerators'], case['weight_denominator']
    family = [tuple(pair) for pair in case['family']]
    divisors = [d for d in range(2, OLD_BASE+1) if OLD_BASE % d == 0]
    require(len(family) == 11 and {d for d, a in family} == set(divisors)
            and all(type(d) is int and type(a) is int and 0 <= a < d for d, a in family),
            'original PG1 class inventory')
    require(points == [x for x in range(OLD_BASE) if not any(x % d == a for d, a in family)]
            and len(points) == len(weights) == 75 and den == 1000000007
            and all(type(w) is int and w > 0 for w in weights) and sum(weights) == den,
            'exact positive PG1 survivor law')
    return points, weights, den, family, hashes


def build_geometry(points, weights, den, base_family):
    c11, c13 = categories(11), categories(13)
    suffix_count = 110*156
    total_mass = den*suffix_count
    old_period = OLD_BASE*121*169
    old_family = base_family+[(11, 0), (121, 0), (13, 0), (169, 0)]
    require(len(old_family) == len({d for d, a in old_family}) == 15
            and lcm(*(d for d, a in old_family)) == old_period,
            'actual fifteen-class old family and period')
    vertices = []
    for base, (d, a) in enumerate(BASE_CYLINDERS):
        for t, e11, e13 in MULTIPLIERS:
            require(t == 11**e11*13**e13, 'original multiplier identity')
            residue, modulus = a, d
            for q, e in ((11, e11), (13, e13)):
                if e:
                    residue = crt(modulus, residue, q**e, 1)
                    modulus *= q**e
            require(modulus == d*t and old_period % modulus == 0,
                    'genuine original old cofactor')
            vertices.append({'index': len(vertices), 'base': base, 'base_modulus': d,
                             'base_residue': a, 'multiplier': t, 'e11': e11, 'e13': e13,
                             'old_modulus': modulus, 'old_residue': residue,
                             'current_modulus': P*modulus})
    require(len(vertices) == len({v['old_modulus'] for v in vertices}) == 18,
            'eighteen distinct original cofactors')
    base_masks, base_masses = [], {mask: 0 for mask in range(8)}
    for x, weight in zip(points, weights):
        mask = sum(1 << i for i, (d, a) in enumerate(BASE_CYLINDERS) if x % d == a)
        base_masks.append(mask)
        base_masses[mask] += weight
    require(base_masses[7] == 0 and max(mask.bit_count() for mask in base_masks) == 2,
            'empty triple intersection and exact base row maximum')
    pair_results = []
    pair_base = {}
    for i, j in combinations(range(3), 2):
        indices = [k for k, mask in enumerate(base_masks) if mask & (1 << i) and mask & (1 << j)]
        numerator = sum(weights[k] for k in indices)
        require(numerator > 0, 'every base pair intersects positively')
        pair_base[(i, j)] = numerator
        pair_results.append({'bases': [i, j], 'points': [points[k] for k in indices],
                             'mass': F(numerator, den), 'numerator': numerator})
    require([row['numerator'] for row in pair_results] == [106787589, 81877150, 28161457],
            'exact triangle pair masses')
    states, samples = {}, []
    for x, weight, base_mask in zip(points, weights, base_masks):
        for a, b in product(c11, c13):
            z = crt(OLD_BASE, x, 121, a['representative'])
            z = crt(OLD_BASE*121, z, 169, b['representative'])
            require(not any(z % d == residue for d, residue in old_family),
                    'actual old survivor CRT support')
            active = sum(1 << v['index'] for v in vertices
                         if base_mask & (1 << v['base'])
                         and a['depth'] >= v['e11'] and b['depth'] >= v['e13'])
            literal = sum(1 << v['index'] for v in vertices
                          if z % v['old_modulus'] == v['old_residue'])
            require(active == literal, 'independent literal old-cofactor activation')
            mass = weight*a['count']*b['count']
            states[active] = states.get(active, 0)+mass
            samples.append((z, mass, active))
    require(sum(states.values()) == sum(mass for z, mass, active in samples) == total_mass
            and max(mask.bit_count() for mask in states) == 12,
            'normalized reduced source and exact twelve-label row maximum')

    def intersection_numerator(indices):
        bases = {vertices[i]['base'] for i in indices}
        base_mass = sum(mass for mask, mass in base_masses.items()
                        if all(mask & (1 << base) for base in bases))
        e11 = max(vertices[i]['e11'] for i in indices)
        e13 = max(vertices[i]['e13'] for i in indices)
        n11 = sum(row['count'] for row in c11 if row['depth'] >= e11)
        n13 = sum(row['count'] for row in c13 if row['depth'] >= e13)
        answer = base_mass*n11*n13
        query = sum(1 << i for i in indices)
        require(answer == sum(mass for mask, mass in states.items() if mask & query == query),
                'symbolic and reduced-state cylinder intersections agree')
        return answer

    edges = {(i, j): intersection_numerator((i, j)) for i, j in combinations(range(18), 2)}
    triples = {indices: intersection_numerator(indices) for indices in combinations(range(18), 3)}
    require(len(edges) == 153 and all(mass > 0 for mass in edges.values()), 'actual overlap graph K18')
    m_numerator = min(pair_base.values())
    require(min(edges.values()) == m_numerator, 'exact minimum original-label edge mass')
    return {'vertices': vertices, 'old_family': old_family, 'old_period': old_period,
            'states': states, 'samples': samples, 'total_mass': total_mass,
            'edges': edges, 'triples': triples, 'm_numerator': m_numerator,
            'base_pair_results': pair_results, 'base_pattern_numerators': base_masses,
            'categories11': c11, 'categories13': c13}


def enumerate_partitions(geometry):
    vertices, states = geometry['vertices'], geometry['states']
    edges, triples = geometry['edges'], geometry['triples']
    mass_den, m_num = geometry['total_mass'], geometry['m_numerator']
    mean_active_num = sum(mask.bit_count()*mass for mask, mass in states.items())
    ideal_charge_num = sum(charge_numerator(mask.bit_count())*mass for mask, mass in states.items())
    records, counts = [], {'triple': 0, 'two-pairs': 0}
    best_loss = best_charge_gap = None
    loss_minimizers = charge_minimizers = 0
    best_partition = None

    def visit(kind, blocks):
        nonlocal best_loss, best_charge_gap, loss_minimizers, charge_minimizers, best_partition
        block_masks = [sum(1 << i for i in block) for block in blocks]
        require(sum(len(block) for block in blocks)-len(blocks) == 2,
                'partition has exactly sixteen nonempty colors')
        closed_loss = (sum(edges[pair] for pair in combinations(blocks[0], 2))-triples[blocks[0]]
                       if kind == 'triple' else sum(edges[block] for block in blocks))
        loss = charge_gap = 0
        for mask, mass in states.items():
            R = mask.bit_count()
            missing = sum(max((mask & block).bit_count()-1, 0) for block in block_masks)
            loss += mass*missing
            charge_gap += mass*(charge_numerator(R)-charge_numerator(R-missing))
        require(loss == closed_loss and loss >= 2*m_num,
                'complete partition collision lower bound and independent intersection formula')
        require(charge_gap >= 30*m_num, 'complete partition assigned-charge lower bound')
        counts[kind] += 1
        if best_loss is None or loss < best_loss:
            best_loss, loss_minimizers = loss, 1
        elif loss == best_loss:
            loss_minimizers += 1
        if best_charge_gap is None or charge_gap < best_charge_gap:
            best_charge_gap, charge_minimizers = charge_gap, 1
        elif charge_gap == best_charge_gap:
            charge_minimizers += 1
        records.append([kind, blocks, loss, charge_gap])
        if blocks == ((9, 17), (11, 15)):
            best_partition = {'blocks': blocks, 'loss_numerator': loss,
                              'charge_gap_numerator': charge_gap}

    for triple in combinations(range(18), 3):
        visit('triple', (triple,))
    for a, b, c, d in combinations(range(18), 4):
        for blocks in (((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c))):
            visit('two-pairs', blocks)
    require(counts == {'triple': comb(18, 3), 'two-pairs': 3*comb(18, 4)}
            and counts == {'triple': 816, 'two-pairs': 9180}
            and len(records) == 9996, 'all partitions of eighteen labels into sixteen colors')
    require(best_loss == 2*m_num and best_charge_gap == 30*m_num and best_partition is not None,
            'exact collision and charge optima')
    require(best_partition['loss_numerator'] == best_loss
            and best_partition['charge_gap_numerator'] == best_charge_gap,
            'one concrete partition simultaneously attains both optima')
    expected_pairs = {(5*121, 7*169), (5*169, 7*121)}
    require({tuple(vertices[i]['old_modulus'] for i in block) for block in best_partition['blocks']}
            == expected_pairs, 'specified original-cofactor achiever')
    return {'partition_counts': counts, 'partition_outcomes_sha256': digest(records),
            'minimum_collision_loss': F(best_loss, mass_den),
            'minimum_assigned_charge_gap': F(best_charge_gap, 128*mass_den),
            'mean_active_labels': F(mean_active_num, mass_den),
            'max_mean_occupied_surviving_roots': F(mean_active_num-best_loss, mass_den),
            'max_mean_mixed_haar_mass': F(mean_active_num-best_loss, P*mass_den),
            'max_mean_conditional_mixed_density': F(mean_active_num-best_loss, 16*mass_den),
            'ideal_row_union_charge': F(ideal_charge_num, 128*mass_den),
            'maximum_actual_assigned_charge': F(ideal_charge_num-best_charge_gap, 128*mass_den),
            'collision_minimizer_count': loss_minimizers,
            'charge_minimizer_count': charge_minimizers, 'achiever': best_partition}


def check_charge_argument(geometry):
    """Finite arithmetic used by the all-root-assignment ordinary proof."""
    checked = 0
    for n0, n1, n2 in product(range(7), repeat=3):
        size = n0+n1+n2
        if not size:
            continue
        pair_hits = sum(bool(a+b) for a, b in ((n0, n1), (n0, n2), (n1, n2)))
        require(pair_hits <= size+1, 'one good color contributes at most its size plus one')
        checked += 1
    # Summing over at most sixteen good colors: the three pair subfamilies
    # have 36 label occurrences, but at most 18+16=34 occupied colors.
    require(36-(18+16) == 2, 'at least two total deep-pair collision units')
    for d in range(13):
        gap = charge_numerator(12)-charge_numerator(12-d)
        require(F(gap, 128) == min(F(15*d, 128), F(17, 32))
                and gap >= 15*min(d, 2), 'positive-part clipping in deep-pair charge loss')
    triples_checked = 0
    for deficits in product(range(13), repeat=3):
        if sum(deficits) >= 2:
            require(sum(min(d, 2) for d in deficits) >= 2,
                    'two collision units survive truncation at two')
            triples_checked += 1
    m = F(geometry['m_numerator'], geometry['total_mass'])
    return {'nonempty_color_count_patterns': checked,
            'deep_deficit_triples_checked': triples_checked,
            'minimum_deep_pair_event_mass': m,
            'ideal_deep_pair_charge': F(17, 32),
            'charge_after_one_lost_root_upper': F(53, 128),
            'universal_assigned_charge_gap': F(15, 64)*m,
            'clipped_loss_rule': 'min(15*d/128,17/32) >= 15*min(d,2)/128',
            'all_assignment_reason': 'For each non-pure color, the number of active base-pair groups is at most its label count plus one. Across at most16 colors this totals at most34, against36 occurrences; pure-root labels cannot improve the bound.'}


def literal_achiever(geometry, optimum):
    vertices, old_family = geometry['vertices'], geometry['old_family']
    blocks = optimum['achiever']['blocks']
    paired = {i for block in blocks for i in block}
    partition = list(blocks)+[(i,) for i in range(18) if i not in paired]
    colors = {i: color for color, block in enumerate(partition, 1) for i in block}
    require(set(colors) == set(range(18)) and set(colors.values()) == set(range(1, 17)),
            'explicit sixteen-root assignment')
    new_family = [(P, 0)]
    for v in vertices:
        new_family.append((v['current_modulus'],
                           crt(v['old_modulus'], v['old_residue'], P, colors[v['index']])))
    family = old_family+new_family
    period = geometry['old_period']*P
    require(len(family) == len({d for d, a in family}) == 34
            and all(d > 1 and d % 2 and 0 <= a < d for d, a in family)
            and lcm(*(d for d, a in family)) == period,
            'actual thirty-four distinct odd original classes')
    mean_occupied = mean_alpha = mean_charge = F()
    literal_rows = []
    for old_residue, mass, active in geometry['samples']:
        bad_roots = []
        for root in range(1, 17):
            z = crt(geometry['old_period'], old_residue, P, root)
            require(not any(z % d == a for d, a in old_family+[(P, 0)]),
                    'literal old and pure support')
            if any(z % d == a for d, a in new_family[1:]):
                bad_roots.append(root)
        occupied = len(bad_roots)
        require(set(bad_roots) == {colors[i] for i in range(18) if active & (1 << i)},
                'literal current residue tests equal labeled occupied roots')
        alpha = F(occupied, 16)
        g, h, beta = normalized_kernel(alpha)
        direct_mass = sum((g-h*int(root in bad_roots))/16 for root in range(1, 17))
        direct_charge = sum((g-h)/16 for root in bad_roots)
        require(direct_mass == 1 and direct_charge == beta
                and beta == F(charge_numerator(occupied), 128),
                'literal normalized kernel and exact assigned charge')
        mean_occupied += mass*occupied
        mean_alpha += mass*alpha
        mean_charge += mass*direct_charge
        literal_rows.append([old_residue, mass, bad_roots, alpha, g, h, beta])
    mass_den = geometry['total_mass']
    require(mean_occupied/mass_den == optimum['max_mean_occupied_surviving_roots']
            and mean_alpha/mass_den == optimum['max_mean_conditional_mixed_density']
            and mean_charge/mass_den == optimum['maximum_actual_assigned_charge'],
            'independent actual-family replay attains both enumerated maxima')
    return {'old_original_class_count': len(old_family), 'total_original_class_count': len(family),
            'old_period': geometry['old_period'], 'period': period,
            'old_representative_rows': len(geometry['samples']),
            'literal_current_point_evaluations': 16*len(geometry['samples']),
            'old_source_denominator': mass_den,
            'old_family': old_family, 'new_current_family': new_family,
            'original_cofactor_to_root': {v['old_modulus']: colors[v['index']] for v in vertices},
            'literal_row_values_sha256': digest(literal_rows),
            'mean_occupied_roots': mean_occupied/mass_den,
            'mean_conditional_mixed_density': mean_alpha/mass_den,
            'mean_assigned_charge': mean_charge/mass_den}


def evaluate(directory, expected_hashes=None):
    points, weights, den, base_family, hashes = load_source(directory, expected_hashes)
    geometry = build_geometry(points, weights, den, base_family)
    optimum = enumerate_partitions(geometry)
    charge_argument = check_charge_argument(geometry)
    require(optimum['minimum_assigned_charge_gap'] == charge_argument['universal_assigned_charge_gap'],
            'combinatorial universal charge gap is attained')
    literal = literal_achiever(geometry, optimum)
    states = [{'active_labels': [i for i in range(18) if mask & (1 << i)],
               'mass': F(mass, geometry['total_mass'])}
              for mask, mass in sorted(geometry['states'].items())]
    return encode({'schema': SCHEMA, 'source_sha256': hashes,
                   'parameters': {'prime': P, 'threshold': 8, 'delta': DELTA,
                                  'base_cylinders': BASE_CYLINDERS,
                                  'multipliers': [row[0] for row in MULTIPLIERS],
                                  'pure_old_classes': [[11, 0], [121, 0], [13, 0], [169, 0]]},
                   'result': {'source_case': 'PG1', 'source_base_point_count': len(points),
                              'source_base_weight_denominator': den,
                              'base_pair_intersections': geometry['base_pair_results'],
                              'base_pattern_numerators': geometry['base_pattern_numerators'],
                              'base_triple_mass': F(), 'categories11': geometry['categories11'],
                              'categories13': geometry['categories13'],
                              'original_labels': geometry['vertices'],
                              'positive_overlap_edges': len(geometry['edges']),
                              'overlap_graph': 'K18', 'chromatic_number': 18,
                              'maximum_row_active_labels': 12,
                              'reduced_source_states': states,
                              'partition_optimum': optimum,
                              'universal_charge_argument': charge_argument,
                              'literal_actual_achiever': literal,
                              'partition_reduction': 'Translate the unique pure17 root to0. Move every mixed label on it to any surviving root, then split color classes until sixteen roots are used; these operations cannot decrease occupied-root counts or assigned charge on any old row. Every resulting partition has one triple or two disjoint pairs. The9996 possibilities are exhausted.',
                              'scope': 'One fixed actual PG1 source times independent pure11/13 survivor laws, and eighteen distinct specified mixed17 original moduli. All current17 forbidden-root assignments are covered. Assigned charge is independent of complete-test prefixes, so its gap remains valid for any tests. No complete-test energy maximum, full Gamma improvement, arbitrary old-layout optimization, or unrestricted covering conclusion is claimed. The finite partition reduction and all-assignment counting argument are ordinary proofs checked by exact arithmetic, not Lean verification.'}})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=HERE/'pg1_color_collision_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = None if args.write else json.loads(args.certificate.read_text())
    if expected is not None:
        require(expected['schema'] == SCHEMA, 'certificate schema')
    actual = evaluate(args.source_directory, None if expected is None else expected['source_sha256'])
    if args.write:
        args.certificate.write_text(json.dumps(actual, indent=2)+'\n')
    else:
        require(actual == expected, 'complete deterministic color-collision certificate equality')
    result = actual['result']
    print(json.dumps({'status': 'written' if args.write else 'verified',
                      'partitions': sum(result['partition_optimum']['partition_counts'].values()),
                      'source_states': len(result['reduced_source_states']),
                      'minimum_collision_loss': result['partition_optimum']['minimum_collision_loss'],
                      'minimum_assigned_charge_gap': result['partition_optimum']['minimum_assigned_charge_gap'],
                      'literal_current_point_evaluations': result['literal_actual_achiever']['literal_current_point_evaluations']}))


if __name__ == '__main__':
    main()
