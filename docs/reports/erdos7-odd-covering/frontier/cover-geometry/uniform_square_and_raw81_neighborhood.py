#!/usr/bin/env python3
"""Complete LCM square and the adopted raw81 first row on one K neighborhood."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/cover-geometry/uniform_square_and_raw81_neighborhood.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/moments-survival/uniform_ap_survival_denominator.py': '191f9fdc7507b6774010af6672abb3159cb59e8c7607cabbe923b4070b307780',
    'certificates/source_norms/moments-survival/uniform_ap_survival_denominator.json': '9b53845d4ed4e830793b98d210bc596b6864287927a8b72e83ab60e59ae8c4a2',
    'frontier/moments-survival/uniform_quadratic_cost_portfolio.py': 'd99e2b890d4393eb2545f2e73d04cd74a9f12eafd8d1f8113a2fa1784cec844f',
    'frontier/comparison-bounds/uniform_k_neighborhood_cost.py': '75ee1c64408773a857dc92e6ab659c2ecb129fffd61f059a4a663af9f7ed791b',
    'frontier/moments-survival/complete_off_face_factorial_tail.py': 'c3a0f508de3fc025f0418f0e496742410230204e77c160bfa7b3a20a33e53594',
    'frontier/cover-geometry/complete_off_face_omitted_tails.py': 'ff157414ae99b5bb47ce58f7b59870bc13827fbfb1d726fc6655435fdce1f91d',
    'frontier/endpoint-bounds/k_face_complete_ratio.py': 'e94a6532ff6951d464a224f1a56415aaea90251c520c7b06fc9afe4e6a82c5db',
    'certificates/source_norms/endpoint-bounds/k_face_complete_ratio.json': 'ccb1debedef1dc49cbc6a31e01c712f156992dc238bd0576e4f51ee8dd6f6888',
    'certificates/source_norms/moments-survival/whole_quadratic_same_head.json': 'ed24ce03bd65f29684a606ba601f88b06040562e7dd7a690d360cea5aa4a2852',
    'verify_joint_frontier.py': '85341d7f8fa2d0b109697bc17b005a7e75f7f6ec412fd2eb3d26383cf9fce24f',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def uniform_square(par, denominator, factorial, tails):
    """Weighted original cylinder caps, preserving the raw/surviving split."""
    delta, rho = par['delta'], par['rho']
    H1 = denominator.uniform_H1(par)
    weights = {3: 3, 9: 5, 5: 3, 15: 9, 45: 15}
    bounded = [{**row, 'LCM_weight': weights[row['modulus']],
                'weighted_upper': weights[row['modulus']]*row['upper']}
               for row in H1['bounded_labels']]
    weighted_tails = []
    for multiplier, original in zip((1, 1, 3, 5), H1['complete_exponent_tails']):
        prime, start = original['prime'], original['start']
        c, H, e = original['reference_coefficient'], original['envelope'], original['error']
        row = {'prime': prime, 'start': start, 'raw': c+H, 'branches': ((c, e, H),)}
        upper = factorial.weighted_family(tails, row, 2*multiplier, multiplier)
        N = original['crossing']
        error = (F(0) if N is None else
                 e*(N*N-start*start)+H*factorial.geometric(prime, N, 2, 1))
        reference = c*factorial.geometric(prime, start, 2, 1)
        require(upper == multiplier*(reference+error), 'Independent exact weighted error crossing')
        weighted_tails.append({'family': original['name'], **row, 'LCM_multiplier': multiplier,
                               'crossing': N, 'reference_weighted_sum': multiplier*reference,
                               'error_weighted_sum': multiplier*error, 'upper': upper})
    aw, bw = factorial.geometric(3, 3, 2, 1), factorial.geometric(5, 1, 2, 1)
    mixed = aw*bw
    require((aw, bw, mixed) == (F(4, 9), F(7, 8), F(7, 18)), 'Complete mixed LCM pair series')
    S_upper = F(53, 360)+5*delta/9+rho
    zero7 = S_upper+sum(r['weighted_upper'] for r in bounded)+sum(r['upper'] for r in weighted_tails)+mixed
    raw_caps = (F(1, 4)+delta/2, F(5, 36)+delta/2, F(1, 12)+delta/2,
                F(3, 4)+delta/4, F(1, 2)+delta/18, F(1, 3), F(1, 9), F(1))
    raw_weights = (F(1), F(3), F(5), aw, bw, 3*bw, 5*bw, mixed)
    raw35 = sum(a*w for a, w in zip(raw_caps, raw_weights))
    require(raw35 == F(173, 48)+F(671, 144)*delta, 'Complete positive raw-cap perturbation')
    seven_factor = F(6, 5)*factorial.geometric(7, 1, 2, 1)
    require(seven_factor == F(2, 3), 'All positive seven depths, including their LCM multiplicities')
    full = zero7+seven_factor*raw35
    if delta == rho == 0:
        require((zero7, raw35, full) == (F(4651, 1800), F(173, 48), F(374, 75)),
                'Exactly the adopted84 full square, with actual unit-unit mass')
    return {'mass_upper': S_upper, 'bounded_cylinders': bounded, 'complete_weighted_tails': weighted_tails,
            'complete_mixed_pair_sum': mixed, 'zero7_pair_upper': zero7,
            'raw_cap_order': ('s', 'N3', 'N9', 'D', 'h', 'h1', 'eta_max', 'deep_mixed'),
            'raw_cap_upper': raw_caps, 'raw_LCM_weights': raw_weights, 'raw35_pair_upper': raw35,
            'positive7_factor': seven_factor, 'full_square_upper': full,
            'face_square_upper': F(374, 75), 'square_excess': full-F(374, 75)}


def retained_raw81(source, quadratic, previous, old84, delta):
    """Index46 is the original raw square357(81), with no deletion credit."""
    tag = ('s', F(81))
    prices = quadratic.raw_source_lipschitz(source, tag)
    projection_price = prices['mass_L1']/2+prices['pure_L1']/9+5*prices['availability_Linfinity']/4
    require(projection_price == F(7726415908741, 7564571872200), 'Complete raw81 first-row source price')
    parameters = list(source.vertices())
    vertices = tuple(source.square357(F(81), source.data(parameters[i])) for i in (398, 410, 422, 616, 628, 640))
    adopted = F(previous['improved_cost_bounds'][46])
    require(max(vertices) == adopted == F(old84['improved_cost_bounds'][46])
            == F(646314683124386207, 393988118343750000), 'The unchanged adopted84 raw81 first-row controller')
    require(all(x == adopted for x in vertices), 'Both original beta faces have the same three vertex values')
    upper = adopted+projection_price*delta
    return {'index': 46, 'tag': tag, 'source_prices': prices, 'delta_price': projection_price,
            'face_vertex_indices': (398, 410, 422, 616, 628, 640), 'face_vertex_values': vertices,
            'face_upper': adopted, 'uniform_upper': upper, 'uniform_excess': upper-adopted,
            'outside_weight': F(previous['cost_weights'][46])}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('square_raw81_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    denominator = module('square_raw81_denominator', base/'frontier/moments-survival/uniform_ap_survival_denominator.py')
    uniform = module('square_raw81_uniform', base/'frontier/comparison-bounds/uniform_k_neighborhood_cost.py')
    quadratic = module('square_raw81_quadratic', base/'frontier/moments-survival/uniform_quadratic_cost_portfolio.py')
    factorial = module('square_raw81_factorial', base/'frontier/moments-survival/complete_off_face_factorial_tail.py')
    tails = module('square_raw81_tails', base/'frontier/cover-geometry/complete_off_face_omitted_tails.py')
    source = module('square_raw81_source', base/'verify_joint_frontier.py')
    pins = dict(PINS)
    for producer in (denominator, uniform, quadratic, factorial, tails):
        for path, pin in producer.PINS.items():
            require(path not in pins or pins[path] == pin, 'Consistent inherited source pin '+path)
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited source '+path)
            pins[path] = pin
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name)))
    previous, old84 = read('whole_quadratic_same_head.json'), read('k_face_complete_ratio.json')
    square_weight = F(previous['complete_square_weight'])
    require(square_weight > 0 and F(previous['complete_square_upper']) == F(374, 75),
            'The original positive full-square complement coefficient')
    results = []
    for delta, rho in ((F(0), F(0)), (F(1, 10000), F(1, 100000))):
        par = uniform.parameters(delta, rho)
        square = uniform_square(par, denominator, factorial, tails)
        raw81 = retained_raw81(source, quadratic, previous, old84, delta)
        weighted = square_weight*square['full_square_upper']+raw81['outside_weight']*raw81['uniform_upper']
        weighted_face = square_weight*F(374, 75)+raw81['outside_weight']*raw81['face_upper']
        require(weighted >= weighted_face and (weighted == weighted_face if delta == rho == 0 else weighted > weighted_face),
                'Both independent complete terms recover their adopted zero-radius contribution')
        results.append({'parameters': par, 'square': square, 'raw81': raw81,
                        'full_square_outside_weight': square_weight, 'weighted_upper': weighted,
                        'weighted_face_upper': weighted_face, 'weighted_excess': weighted-weighted_face})
    return uniform.encode({'schema': 'erdos7-uniform-square-and-raw81-neighborhood-v1', 'source_sha256': pins,
                           'radius_results': results,
                           'scope': 'Complete source-uniform square complement and original raw81 index46 on134 K neighborhood, both orientations and whole beta face. Square uses139 surviving cylinder caps plus complete weighted tails and raw positive-seven pair caps. Raw81 retains84 adopted convex source controller via140 Lipschitz bound. Both recover exact adopted face values. Ordinary proof plus rational arithmetic; no Lean, global K or unrestricted Erdos7 result.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('square_raw81_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact full-square and raw81 certificate')
    for row in result['radius_results']:
        print('PASS: delta='+row['parameters']['delta']+', square='+row['square']['full_square_upper']
              +', raw81='+row['raw81']['uniform_upper'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
