#!/usr/bin/env python3
"""Complete numerator and survival comparison on both full K-control faces.

The ordinary proof extends the old genuine convex cost functions across
the beta faces. No new endpoint table is assumed convex. Complete lcm
pair sums supply the square bound; all original AP tails remain present.
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
CERTIFICATE = 'certificates/source_norms/k_face_complete_ratio.json'
PINS = {
    "certificate_io.py": "287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232",
    "verify_joint_frontier.py": "a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe",
    "frontier/endpoint_numerator_common_costs.py": "5dc154c530994a5340549478437fc38de3b2f2d0e538842a2dd9f9a9b2e96663",
    "frontier/endpoint_k_face_forced27.py": "8e5b5267397b8ca4d9cf0477b9c9074ae9e38e8171f1e4eb05a47595ad1df961",
    "certificates/source_norms/endpoint_k_face_forced27.json": "8f4c5fe37ed46d45c914f21872b2e4d00a2091adf028a0497cdd1817f82f8da0",
    "frontier/k_face_common_seven_hinges.py": "8cc4600c9b3f2f65a11820fcb2d0d6663c765c20765bbaf1ae0de6e883cefc97",
    "certificates/source_norms/k_face_common_seven_hinges.json": "002f286cce356e477f11e98fdd7bdb9d834f0c707691eee156eb17a77f03686d",
    "certificates/source_norms/full_linear_carrier_frontier.json": "237ed11241550037c69c855742d3f6e0a3a9c362ae2a861a173d3450e32375c0",
    "certificates/source_norms/endpoint_joint_geometry_ratio.json": "e80cc5f5ce7fbe5997d518cb78b219a34a46cc251a0ff1611c26ac670957a91f",
    "frontier/ap_schedule.py": "40b6138fc9d0fc1d540880e8a4abb1933d1dcd1b2c5dbf54646008c3f2e62b9f",
    "frontier/fixed_cost.py": "2df5ca217aced5823c6c9d88324737091b11318c9625f73503ca7cd35db8c21d",
    "certificates/ap_schedule_norms.json": "7cbb82bb2ea8691136fe74779632ffb821f78dd3b0c498ea1625f84a3866d9d8"
}
FACES = (((398, 410, 422), (1, 1)), ((616, 628, 640), (1, 0)))


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
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def weighted_tail(p, start):
    return F(1, p**start)/(1-F(1, p))*(2*start+1+F(2, p-1))


def cylinder_cap(a, b, surviving):
    if b == 0:
        if a < 3:
            return ((F(53, 360), F(7, 90), F(1, 18)) if surviving
                    else (F(1, 4), F(5, 36), F(1, 12)))[a]
        return (F(7, 10) if surviving else F(3, 4))/3**a
    if a < 3:
        if surviving and b == 1:
            return (F(14, 225), F(8, 225), F(4, 225))[a]
        coefficient = ((F(2, 5), F(4, 15), F(4, 45)) if surviving
                       else (F(1, 2), F(1, 3), F(1, 9)))[a]
        return coefficient/5**b
    return F(1, 3**a*5**b)


def square_sums():
    a3, b1, b2 = weighted_tail(3, 3), weighted_tail(5, 1), weighted_tail(5, 2)
    raw = F(1, 4)+3*F(5, 36)+5*F(1, 12)+F(3, 4)*a3+F(37, 18)*b1+a3*b1
    zero = (F(53, 360)+3*F(7, 90)+5*F(1, 18)+F(7, 10)*a3
            +3*F(14, 225)+9*F(8, 225)+15*F(4, 225)+F(74, 45)*b2+a3*b1)
    factor7 = F(6, 5)*weighted_tail(7, 1)
    full = zero+factor7*raw
    require((raw, zero, factor7, full) == (F(173, 48), F(4651, 1800), F(2, 3), F(374, 75)),
            'Complete raw and surviving lcm pair sums')
    checks = []
    for cut in (3, 5, 9):
        prefixes = [sum((2*a+1)*(2*b+1)*cylinder_cap(a, b, live)
                        for a, b in product(range(cut+1), repeat=2)) for live in (False, True)]
        ta, tb = weighted_tail(3, cut+1), weighted_tail(5, cut+1)
        mixed = ta*b1+(a3-ta)*tb
        tails = [F(3, 4)*ta+F(37, 18)*tb+mixed, F(7, 10)*ta+F(74, 45)*tb+mixed]
        require([x+y for x, y in zip(prefixes, tails)] == [raw, zero], 'Independent full35 tail reconstruction')
        seven_prefix = sum(F(6*(2*e+1), 5*7**e) for e in range(1, cut+1))
        seven_tail = F(6, 5)*weighted_tail(7, cut+1)
        prefix = prefixes[1]+seven_prefix*prefixes[0]
        tail = tails[1]+seven_prefix*tails[0]+seven_tail*raw
        require(prefix+tail == full and tail > 0, 'Entire three-prime pair sum with explicit complement')
        checks.append({'cut': cut, 'prefix': prefix, 'complete_tail': tail})
    return {'raw35_pair_sum': raw, 'zero7_pair_sum': zero, 'positive7_factor': factor7,
            'full_square_upper': full, 'finite_boxes_and_complete_tails': checks}


def calculate(base):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('k_ratio_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    old = read('certificates/source_norms/full_linear_carrier_frontier.json')
    previous = read('certificates/source_norms/endpoint_joint_geometry_ratio.json')
    geometry = read('certificates/source_norms/endpoint_k_face_forced27.json')
    hinges = read('certificates/source_norms/k_face_common_seven_hinges.json')
    for record in (old, previous, geometry, hinges):
        for path, pin in record['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited dependency')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    for record in (geometry, hinges):
        require(record['face_vertices'] == list(FACES[0][0]) and record['carrier'] == list(FACES[0][1])
                and record['symmetric_face_vertices'] == list(FACES[1][0])
                and record['symmetric_carrier'] == list(FACES[1][1]), 'Exactly the same two entire faces')
    source = module('k_ratio_source', base/'verify_joint_frontier.py')
    schedule = module('k_ratio_schedule', base/'frontier/ap_schedule.py')
    fixed = module('k_ratio_fixed', base/'frontier/fixed_cost.py')
    majorant = module('k_ratio_majorant', base/'frontier/endpoint_numerator_common_costs.py')
    specs, _, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    D, L = F(geometry['surviving_mass']), F(geometry['linear_upper'])
    require((D, L) == (F(53, 360), F(1151, 1800)) and F(hinges['surviving_mass']) == D, 'One actual saturated mass')
    sums = square_sums()
    Q = sums['full_square_upper']
    cap_groups = geometry['complete_nonunit_zero7_categories']
    require([F(cap_groups[k]) for k in ('test3', 'test9', 'test5', 'test15', 'test45')]
            == [F(7, 90), F(1, 18), F(14, 225), F(8, 225), F(4, 225)], 'Inherited arbitrary-cylinder shallow bounds')
    require(list(map(F, geometry['complete_descendant5_coefficients'])) == [F(2, 5), F(4, 15), F(4, 45)]
            and F(cap_groups['pure3_deep']) == F(7, 180), 'Complete descendant coefficients')
    vertices = list(source.vertices())
    rows = {r['index']: r for block in old['frontier']['row_blocks'] for r in block}
    face_bounds, retained_rows = [], []
    for indices, carrier in FACES:
        ci = old['frontier']['carriers'].index(list(carrier))
        local = []
        for idx in indices:
            row = rows[idx]
            records = row['linear_directions']+row['quadratic_directions']
            require(len(records) == len(specs) == 46, 'Every original AP transformed cost')
            dat = source.data(vertices[idx])
            require(dat[3:] == (F(1, 4), D), 'Same mass and raw source endpoints')
            bounds = [L, Q]+[F(r['constant'])*D-F(r['conditional'][ci]) for r in records]
            bounds += [source.square357(F(81, n*n), dat) for n in range(1, 7)]
            local.append(bounds)
            retained_rows.append({'index': idx, 'carrier': carrier, 'cost_bounds': bounds})
        face_bounds.append([max(b[i] for b in local) for i in range(54)])
    require(face_bounds[0] == face_bounds[1], 'Both face-wide convex upper envelopes agree')
    bounds = face_bounds[0]
    tags = [('h', F(0)), ('s', F(0))]+[s['tag'] for s in specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    functions = [lambda v, tag=tag: source.zero5_cost(tag, v) for tag in tags]
    metadata = [source.zero5_cost_metadata(tag) for tag in tags]
    costs, proofs = [], []
    for target, alpha, weights in majorant.MAJORANTS:
        proof = majorant.verify_majorant(target, F(alpha), [(j, F(w)) for j, w in weights], functions, metadata, bounds, D)
        proofs.append(proof)
        costs.append(min(bounds[target], proof['bound']))
    require(len(costs) == 52, 'All52 all-load majorants retained')
    weights = [F(row['comparison_weight']) for row in previous['cost_rows']]
    residual, square_weight = F(previous['signed_mass_coefficient']), F(previous['complete_square_weight'])
    require(residual < 0 < square_weight and min(weights) > 0, 'Signed mass and all positive cost coefficients retained')
    N = residual*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    U4, U5 = (F(hinges['uniform_hinge_uppers'][str(t)]) for t in (4, 5))
    denominator = F(945008, 922383)*D-F(45253, 1844766)*L-F(346061, 1844766)*U4-F(4, 33)*U5
    p = lambda n: F(28, 33) if n == 1 else F(50, 3*11**n)
    r = F(1, 11)
    tail0, tail1 = F(50, 3)*r**5/(1-r), F(50, 3)*r**5*(5-4*r)/(1-r)**2
    interpolation = lambda t: (4-t)*(L-D)/3+(t-1)*U4/3
    full = D-U4/6-(p(1)*U5+sum(p(n)*n*interpolation(F(5, n)) for n in (2, 3, 4))+tail1*L-5*tail0*D)/7
    require(full == denominator > 0 and N > 0, 'Independent complete AP11 survival expansion and signs')
    comparison = source.WHOLE_CONST+N/denominator
    require(comparison > 403, 'The sufficient target remains open')
    return {'schema': 'erdos7-k-face-complete-ratio-v1', 'source_sha256': used,
            'faces': [{'vertices': i, 'carrier': c} for i, c in FACES], 'mass': D, 'linear_upper': L,
            'square_sums': sums, 'hinge_uppers': {'4': U4, '5': U5}, 'vertex_cost_inputs': retained_rows,
            'uniform_cost_constraint_bounds': bounds, 'majorants': proofs, 'improved_cost_bounds': costs,
            'improved_cost_count': sum(x < y for x, y in zip(costs, bounds[2:])),
            'cost_weights': weights, 'signed_mass_coefficient': residual, 'complete_square_weight': square_weight,
            'numerator_upper': N, 'full_AP11_tail': {'mass': tail0, 'first_moment': tail1},
            'uniform_denominator_lower': denominator, 'offset': source.WHOLE_CONST,
            'comparison_upper': comparison,
            'scope': 'Both complete actual K-control beta faces at saturated mass, with independent original tests and all exponent tails. Uses convexity only of the old genuine cost functions, not patched endpoint data. No off-face neighborhood, new global K bound, scalar sharpness, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('k_ratio_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete face certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: both entire K faces, complete square and AP11 tails,52 all-load majorants.')
    print('Numerator '+str(float(F(result['numerator_upper'])))+'; denominator '
          +str(float(F(result['uniform_denominator_lower'])))+'; comparison '+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
