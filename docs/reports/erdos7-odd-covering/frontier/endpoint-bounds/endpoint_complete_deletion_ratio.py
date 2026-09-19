#!/usr/bin/env python3
"""Complete endpoint numerator/survival with the additional pure3 deletion.

Reuse the all-load majorants; retain the same actual source and every tail.
The revised finite scalar witnesses certify only the stated relaxation.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/endpoint_complete_deletion_ratio.json'
PINS = {
    "certificate_io.py": "2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b",
    "frontier/endpoint-bounds/endpoint_numerator_common_costs.py": "1b665058c35f8aaadc60d4513939e6c4255cff212b6289d8c0e3beb7bd1d02d6",
    "certificates/source_norms/endpoint-bounds/endpoint_numerator_common_costs.json": "75154048adef87983ab5c776537f73e74f9864714b5cc24b54bfa674dcca26f6",
    "frontier/endpoint-bounds/endpoint_uniform_ratio.py": "c5360becfe50bbd4f2bcd4246db7bcd3f2a582f76744ccba3545f614fe12175b",
    "certificates/source_norms/endpoint-bounds/endpoint_uniform_ratio.json": "7bf9ac78825c4b7dedfcda601a6a7e2c6f3aaec937eff709a3fdd4a07f5df8ea",
    "frontier/endpoint-bounds/endpoint_survival_scalar_barrier.py": "10e915082ee01cef1219125367fd455374c82c98d812654cc4283b2fe7ac3358",
    "certificates/source_norms/endpoint-bounds/endpoint_survival_scalar_barrier.json": "a4a4092e9d198b126b85afe96d00b399105a35e73c1e309f3d364e19633ec430",
    "frontier/endpoint-bounds/endpoint_linear_complete_pure3_deletion.py": "c0bba2c21ed9c1d6236bfee13ff2510f71b40b44bf63600f09be3b2807897bd5",
    "certificates/source_norms/endpoint-bounds/endpoint_linear_complete_pure3_deletion.json": "7e5b2c9d2244a9aad0b1f3e1850a52bb1a1a1e7ffbe49cbf7bd42b8017bc2cfc"
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('complete_deletion_ratio_io', base/'certificate_io.py')
    read = lambda p: json.loads(io.read_artifact_bytes(base/p))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    prior = read('certificates/source_norms/endpoint-bounds/endpoint_numerator_common_costs.json')
    old = read('certificates/source_norms/endpoint-bounds/endpoint_uniform_ratio.json')
    survival = read('certificates/source_norms/endpoint-bounds/endpoint_survival_scalar_barrier.json')
    geometry = read('certificates/source_norms/endpoint-bounds/endpoint_linear_complete_pure3_deletion.json')
    for record in (prior, old, survival, geometry):
        require(record['source_vertex'] == 404 and record['carrier'] == [0, 1], 'Same actual endpoint source/carrier')
        for path, pin in record['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pin')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
            used[path] = pin
    D, Lold, L, Q = F(3, 20), F(old['first_moment_upper']), F(geometry['linear_upper']), F(old['square_upper'])
    delta = Lold-L
    require((Lold, L, Q, delta) == (F(1157, 1800), F(16, 25), F(114, 25), F(1, 360)), 'Complete deletion improvement and retained square')
    source = module('complete_deletion_ratio_source', base/'verify_joint_frontier.py')
    schedule = module('complete_deletion_ratio_schedule', base/'frontier/cover-geometry/ap_schedule.py')
    fixed = module('complete_deletion_ratio_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    majorant = module('complete_deletion_ratio_majorants', base/'frontier/endpoint-bounds/endpoint_numerator_common_costs.py')
    specs, _, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    tags = [('h', F(0)), ('s', F(0))]+[spec['tag'] for spec in specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    bounds = list(map(F, prior['universal_cost_constraint_bounds']))
    bounds[:2] = [L, Q]
    require(len(tags) == len(bounds) == 54, 'Complete54 scalar constraints')
    functions = [lambda v, tag=tag: source.zero5_cost(tag, v) for tag in tags]
    metadata = [source.zero5_cost_metadata(tag) for tag in tags]
    require(tuple(row[0] for row in majorant.MAJORANTS) == tuple(range(2, 54)), 'All52 unchanged majorants')
    rows, costs, proofs = [], [], []
    for i, (target, alpha, multipliers) in enumerate(majorant.MAJORANTS):
        weights = [(j, F(w)) for j, w in multipliers]
        proof = majorant.verify_majorant(target, F(alpha), weights, functions, metadata, bounds, D)
        cost = min(bounds[target], proof['bound'])
        require(F(0) <= cost <= F(old['cost_rows'][i]['new_upper']), 'Every old min branch preserved or improved')
        costs.append(cost)
        proofs.append(proof)
        weight = F(old['cost_rows'][i]['comparison_weight'])
        rows.append({'target': target, 'comparison_weight': weight,
                     'old70_upper': F(old['cost_rows'][i]['new_upper']), 'new_upper': cost,
                     'dual_bound': proof['bound'], 'linear_multiplier': sum(w for j, w in weights if j == 0),
                     'weighted_gain': weight*(F(old['cost_rows'][i]['new_upper'])-cost)})
    denominator_old = F(old['uniform_actual_endpoint_denominator'])
    residual, square_weight = F(old['positive_cost_residual_slope']), F(old['square_direct_coefficient'])
    N = residual*D+sum(row['comparison_weight']*cost for row, cost in zip(rows, costs))+square_weight*Q
    require(N == F(old['numerator_upper'])-sum(row['weighted_gain'] for row in rows), 'Complete signed numerator and positive-weight gain agree')
    require(residual < 0, 'Retain the signed residual mass coefficient')
    U25, U4, U5 = map(F, survival['original53_hinge_uppers'])
    denominator = F(945008, 922383)*D-F(45253, 1844766)*L-F(346061, 1844766)*U4-F(4, 33)*U5
    require(denominator-denominator_old == F(45253, 1844766)*delta > 0, 'Exact full-AP11 survival gain')
    def upper(t):
        if t >= 4:
            require(t in (4, 5), 'Only native high hinges needed')
            return U4 if t == 4 else U5
        if t <= 1:
            return L-t*D
        return (4-t)*(L-D)/3+(t-1)*U4/3
    p = lambda n: F(28, 33) if n == 1 else F(50, 3*11**n)
    r = F(1, 11)
    T0, T1 = F(50, 3)*r**5/(1-r), F(50, 3)*r**5*(5-4*r)/(1-r)**2
    full_survival = D-U4/6-(sum(p(n)*n*upper(F(5, n)) for n in range(1, 5))+T1*L-5*T0*D)/7
    require(full_survival == denominator > 0, 'Independent complete-AP11 expansion with infinite affine tail')
    W = [(v, F(mass)) for v, mass in survival['laws']['W']['support']]
    V = [(v, F(mass)) for v, mass in survival['laws']['V']['support']]
    Wnew = [(v, mass+delta/3 if v == 1 else mass-delta/3 if v == 4 else mass) for v, mass in W]
    all_functions = functions+[lambda v, t=t: max(F(v)-t, F(0)) for t in (F(5, 2), F(4), F(5))]
    all_bounds = bounds+[U25, U4, U5]
    laws = {}
    for name, law in (('W_revised', Wnew), ('V', V)):
        require(sum(m for _, m in law) == D and min(m for _, m in law) > 0, 'Positive scalar law of the same mass')
        slacks = [cap-sum(m*fn(v) for v, m in law) for cap, fn in zip(all_bounds, all_functions)]
        require(min(slacks) >= 0, 'All57 revised scalar constraints are feasible')
        laws[name] = {'support': law, 'constraint_slacks': slacks, 'first_moment': sum(v*m for v, m in law)}
    require(laws['W_revised']['first_moment'] == L and sum(m*max(v-4, 0) for v, m in Wnew) == U4, 'Revised W jointly attains the new mean and h4')
    require(sum(m*max(v-5, 0) for v, m in V) == U5, 'V retains the high-hinge extremum')
    for t in (F(5, 2), F(5, 3), F(5, 4), F(1)):
        require(sum(m*max(F(v)-t, 0) for v, m in Wnew) == upper(t), 'Revised W attains every interpolated and affine hinge')
    offset = F(old['offset'])
    ratio = offset+N/denominator
    require(403 < ratio < F(old['endpoint_comparison_upper']), 'Strict endpoint improvement with unresolved threshold')
    return {'schema': 'erdos7-endpoint-complete-deletion-ratio-v1', 'source_vertex': 404, 'carrier': [0, 1],
            'source_sha256': used, 'mass': D, 'old_linear_upper': Lold, 'linear_upper': L, 'linear_gain': delta,
            'square_upper': Q, 'cost_rows': rows, 'majorants': proofs,
            'improved_cost_count': sum(row['weighted_gain'] > 0 for row in rows),
            'signed_mass_coefficient': residual, 'complete_square_weight': square_weight,
            'numerator_upper': N, 'numerator_gain': F(old['numerator_upper'])-N,
            'full_AP11_tail': {'mass': T0, 'first_moment': T1},
            'original_hinge_caps': [U25, U4, U5], 'uniform_endpoint_denominator': denominator,
            'denominator_gain': denominator-denominator_old, 'offset': offset,
            'endpoint_comparison_upper': ratio, 'endpoint_comparison_gain': F(old['endpoint_comparison_upper'])-ratio,
            'scalar_laws': laws,
            'scope': 'Uniform actual404 endpoint numerator/survival using complete pure3 deletion, retained square114/25 and all52 existing majorants. The revised57-constraint survival relaxation is sharp by abstract laws only; no actual realization, globalK update or Lean claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('complete_deletion_ratio_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete endpoint certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:52 all-load majorants, complete AP11 tail,114 scalar feasibility checks and common signed numerator.')
    print('Endpoint numerator '+str(float(F(result['numerator_upper'])))+'; denominator '+str(float(F(result['uniform_endpoint_denominator'])))+'; ratio '+str(float(F(result['endpoint_comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
