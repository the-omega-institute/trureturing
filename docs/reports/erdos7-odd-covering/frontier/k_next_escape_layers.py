#!/usr/bin/env python3
"""Exact next K escape layers after both original J/K control faces.

A compact dictionary reconstitutes the already certified profile71 table.
Its complete ordered endpoint-table hash must equal that prior certificate.
No source-cost enumeration is repeated and no actual-family attainment is
inferred from a relaxed table control.
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
CERTIFICATE = 'certificates/source_norms/k_next_escape_layers.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/global_control_faces.py': '649e9c395ed07896ccc93064c8634e402e1a277b2a96c06a3688e8b566f85c93',
    'certificates/source_norms/global_control_faces.json': 'd99736841c20977095c5c397c5949dec20960a4ee1afd72a3f926f2e773b8817',
    'certificates/source_norms/joint_survival_carriers.json': '9b8b6f5bfabed669cea810b759d2d02f19e47cce1999851dcd031cfa77115a72',
    'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
    'certificates/source_norms/k_signed_gap_dictionary.json': '425876003311557cec40e46a1155c2e6474144357e20e88ba07523014ceb73ae',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('next_escape_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    prior = read('certificates/source_norms/global_control_faces.json')
    for path, pin in prior['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited source')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
        used[path] = pin
    dictionary = read('certificates/source_norms/k_signed_gap_dictionary.json')
    survival = read('certificates/source_norms/joint_survival_carriers.json')
    source = module('next_escape_source', base/'verify_joint_frontier.py')
    control = module('next_escape_control', base/'frontier/global_control_faces.py')
    carriers = [tuple(c) for c in prior['carriers']]
    require(carriers == list(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4)))
            and dictionary['carriers'] == prior['carriers'], 'All18 full, partial and empty carriers')
    vertices = list(source.vertices())
    factors = list(product(*(range(n) for n in prior['factor_sizes'])))
    require(len(vertices) == len(factors) == dictionary['vertex_count'] == 1296
            and control.digest(factors) == prior['all1296_factor_indices_sha256'], 'Exact complete source product and index convention')
    rows46 = [r for block in survival['joint_survival']['row_blocks'] for rows in block for r in rows]
    require(len(rows46) == 1296 and [r['index'] for r in rows46] == list(range(1296)), 'All actual-mass carrier bounds')
    values = list(map(F, dictionary['rational_values']))
    lookup = dictionary['lower_gap_value_indices']
    require(values == sorted(set(values)) and min(values) == 0 and len(values) == 3344
            and len(lookup) == 1296*18 and all(type(j) is int and 0 <= j < len(values) for j in lookup),
            'Complete canonical rational dictionary and lower-endpoint lookup')
    A = F(prior['targets']['K']['mass_coefficient'])
    require(A > 0, 'Positive signed mass coefficient makes every lower endpoint minimal')
    table, lower, masses, mass_gains = [], [], {}, []
    for i, vertex in enumerate(vertices):
        dat = source.data(vertex)
        s = dat[3]
        for j, c in enumerate(carriers):
            old = rows46[i]['conditional'][j]
            require(tuple(old['carrier']) == c, 'Ordered common carrier')
            dc = F(old['D_c'])
            g = values[lookup[18*i+j]]
            require(dc <= s and g >= 0, 'Valid full mass interval and old nonnegative gap')
            rise = A*(s-dc)
            table.extend(((i, j, 'D_c', g), (i, j, 's', g+rise)))
            lower.append((i, j, g))
            masses[i, j] = (dc, s)
            mass_gains.append(rise)
    table_digest = control.digest(table)
    require(table_digest == dictionary['complete_endpoint_table_sha256']
            == prior['targets']['K']['all_signed_gaps_sha256'], 'Exact original71 ordered table at both46656 endpoints')
    Kset = {(r['index'], r['carrier_index']) for r in prior['targets']['K']['zero_controls']}
    Jset = {(r['index'], r['carrier_index']) for r in prior['targets']['J']['zero_controls']}
    union = Kset | Jset
    gamma1 = F(prior['targets']['K']['minimum_positive_signed_gap_both_endpoints'])
    require(len(Kset) == 6 and len(Jset) == 18 and Kset.isdisjoint(Jset)
            and all(g == 0 for i, j, g in lower if (i, j) in Kset)
            and all(g == gamma1 for i, j, g in lower if (i, j) in Jset), 'Exactly the sixK and18J low controls with their old gaps')
    require(all(F(1, 4) <= s <= F(5, 9) for dc, s in masses.values())
            and all(masses[i, j][1] == F(1, 4) for i, j in Kset),
            'The same product weights give raw mass at most1/4+11*sigma/36')

    def minimum_outside(excluded):
        both = [r for r in table if (r[0], r[1]) not in excluded]
        lo = [r for r in both if r[2] == 'D_c']
        up = [r for r in both if r[2] == 's']
        result = min(r[3] for r in both)
        require(result == min(r[3] for r in lo) <= min(r[3] for r in up), 'Both mass endpoints give the reported lower-endpoint minimum')
        witnesses = [r for r in both if r[3] == result]
        return result, witnesses, min(r[3] for r in up)

    gamma2, witnesses2, upper2 = minimum_outside(union)
    nextset = {(i, j) for i, j, endpoint, _ in witnesses2}
    require(gamma2 == F(14158742250938240063000691811817435200717494240697,
                        24344652964341558386865026089989867851282700000000)
            and [(i, carriers[j], endpoint) for i, j, endpoint, _ in witnesses2]
            == [(386, (1, 1), 'D_c'), (592, (1, 0), 'D_c')], 'Exact next layer after the whole J/K union')
    extended = union | nextset
    gamma3, witnesses3, upper3 = minimum_outside(extended)
    require(gamma3 > gamma2 > gamma1 > 0 and len(witnesses3) == 6,
            'Strict subsequent escape layer after the two extra controls')
    union_points = {factors[i]+(j,) for i, j in union}
    extended_points = {factors[i]+(j,) for i, j in extended}
    boxes = control.maximal_boxes(union_points)
    next_boxes = control.maximal_boxes(extended_points)
    require(len(boxes) == len(next_boxes) == 4, 'Four maximal Cartesian regions in each exact union')

    # Equality of these square-free product polynomials is checked on every
    # source/carrier basis tuple. Averaging gives the exact product masses.
    for i, factors_i in enumerate(factors):
        d, a, b, l, z = factors_i
        for j, c in enumerate(carriers):
            common = int(a == 2 and z == 0)
            union_polynomial = common*int(b in (3, 4, 5))*(
                int(d == 1)*(int(l == 1 and c == (1, 1))+int(l in (3, 4, 5) and c == (0, 1)))
                +int(d == 2)*(int(l == 2 and c == (1, 0))+int(l in (3, 4, 5) and c == (0, 0))))
            extra_polynomial = common*(int(d == 1 and b == 2 and l == 1 and c == (1, 1))
                                       +int(d == 2 and b == 1 and l == 2 and c == (1, 0)))
            require(union_polynomial == int((i, j) in union)
                    and union_polynomial+extra_polynomial == int((i, j) in extended), 'Exact union and extended product-mass formulas')
    for i, j, g in lower:
        rhs2 = gamma1*int((i, j) in Jset)+gamma2*int((i, j) not in union)
        rhs3 = gamma1*int((i, j) in Jset)+gamma2*int((i, j) in nextset)+gamma3*int((i, j) not in extended)
        require(g >= rhs2 and g >= rhs3, 'Every vertex and carrier satisfies both layered escape inequalities')

    late_K = {factors[i][3] for i, j in Kset}
    carrier_K = {j for i, j in Kset}
    late_J = {factors[i][3] for i, j in Jset}
    carrier_J = {j for i, j in Jset}
    require(late_K == {1, 2} and carrier_K == {13, 14}
            and late_J == {3, 4, 5} and carrier_J == {7, 8}
            and late_K.isdisjoint(late_J) and carrier_K.isdisjoint(carrier_J),
            'J and K controls occupy disjoint events in two independent product factors')
    quadratic = {'constant': F(0), 'linear': gamma2, 'quadratic': gamma1-gamma2}
    require(quadratic['quadratic'] < 0
            and quadratic['linear']+quadratic['quadratic'] == gamma1
            and quadratic['linear']/2+quadratic['quadratic']/4 == (gamma2+gamma1)/4,
            'Exact concave escape polynomial, endpoint and midpoint')

    def report(witnesses):
        return [{'index': i, 'factors': factors[i], 'carrier': carriers[j], 'carrier_index': j,
                 'endpoint': endpoint, 'gap': g, 'D_c': masses[i, j][0], 'raw_mass': masses[i, j][1],
                 'source_vertex': vertices[i]}
                for i, j, endpoint, g in witnesses]

    return {'schema': 'erdos7-k-next-escape-layers-v1', 'source_sha256': used,
            'complete_original_endpoint_table_sha256': table_digest, 'signed_endpoint_checks': len(table),
            'lower_endpoint_controls': len(lower), 'carriers': carriers, 'signed_mass_coefficient': A,
            'minimum_upper_minus_lower_gap': min(mass_gains), 'first_positive_gap': gamma1,
            'K_zero_count': len(Kset), 'J_zero_count': len(Jset), 'union_count': len(union),
            'union_maximal_cartesian_boxes': boxes,
            'union_source_face_dimensions': [sum(len(x)-1 for x in box[:5]) for box in boxes],
            'gap_outside_JK_union': gamma2, 'upper_endpoint_minimum_outside_JK_union': upper2,
            'next_layer_controls': report(witnesses2), 'next_gap_ratio_to_original': gamma2/gamma1,
            'extended_union_count': len(extended), 'extended_maximal_cartesian_boxes': next_boxes,
            'extended_source_face_dimensions': [sum(len(x)-1 for x in box[:5]) for box in next_boxes],
            'gap_outside_extended_union': gamma3, 'upper_endpoint_minimum_outside_extended_union': upper3,
            'following_layer_controls': report(witnesses3),
            'union_mass_polynomial': 'a2*z0*b345*(d1*(l1*pi11+l345*pi01)+d2*(l2*pi10+l345*pi00))',
            'extra_mass_polynomial': 'a2*z0*(d1*b2*l1*pi11+d2*b1*l2*pi10)',
            'first_layered_bound': 'B_K >= gamma1*q(Z_J)+gamma2*(1-q(Z_K)-q(Z_J))',
            'second_layered_bound': 'B_K >= gamma1*q(Z_J)+gamma2*q(A)+gamma3*(1-q(Z_K)-q(Z_J)-q(A))',
            'independent_separating_events': {'K_late_indices': sorted(late_K), 'K_carrier_indices': sorted(carrier_K),
                                            'J_late_indices': sorted(late_J), 'J_carrier_indices': sorted(carrier_J)},
            'product_mass_constraints': ['qK <= LK*PK', 'qJ <= (1-LK)*(1-PK)',
                                         'sqrt(qK)+sqrt(qJ) <= 1', 'qJ <= (1-qK)^2'],
            'escape_polynomial_in_sigma': quadratic,
            'joint_denominator_bound': {'constant': F(1, 4), 'sigma_coefficient': F(11, 36)},
            'paired_target_change_bound': 'Phi_new >= -h/4+(gamma2-11*h/36)*sigma-(gamma2-gamma1)*sigma^2 + other_valid_reserve',
            'paired_bound_hypothesis': 'Retain E<=1/4+11*sigma/36 with the same product weights and sigma=1-qK; do not count old escape twice.',
            'scope': 'Exact further escape classification of the already certified profile71 K table, including all full/partial/empty carriers and both mass endpoints. Maximal product regions and layered product-mass inequalities are ordinary consequences of the same old separately concave source functions. No new actual-face cost improvement, source realizability, global K target, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('next_escape_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact next escape classification')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: exact old46656-endpoint table; four-box J/K union; two further layers and product escape bounds.')
    print('Outside J/K: '+str(float(F(result['gap_outside_JK_union'])))
          +'; after two additional controls: '+str(float(F(result['gap_outside_extended_union'])))+'.')


if __name__ == '__main__':
    main()
