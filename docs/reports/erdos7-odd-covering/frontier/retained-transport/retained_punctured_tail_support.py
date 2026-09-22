#!/usr/bin/env python3
"""Join fixed retained-row prices to the complete punctured infinite tails.

The finite cut library is minimized only after each support covers the whole
source domain. The consumer is eight original225/226 controller duals, not the
untransported pruning alternatives or a complete off-face K comparison.
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
CERTIFICATE = 'certificates/source_norms/retained-transport/retained_punctured_tail_support.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/retained-transport/complete_retained_row_transport.py': '44aa053a1338334db06218cb429b0f3397ec2b3eb170d5e9c47fbb184893d1b9', 'frontier/retained-transport/retained_pair_row_transport.py': 'e56a18d6bde9430a508115c01724b4055488bbcab09ea82929cd2666e706e82f', 'frontier/retained-transport/joint_deletion_row_transport.py': 'ee4a5393fc33368c7f25c50ef39ed8debafd4a1f2d4ca64ef0a6a10ac4b03233', 'frontier/retained-transport/selected_deletion_mask_row_transport.py': '7d9c35291258c338b6eea2a84ad14c2fc10ceb8549fdea932b4cae94d0c9f6a4', 'frontier/retained-transport/retained135_heavy_comparison.py': '93ad67489e6ce429f45bd8888cfd8f6e5ac91b0bc3d4fbeebfedef9f7d4b84ac', 'frontier/retained-transport/retained135125_heavy_comparison.py': '06fa084b5ce23b8abd6119e8e767ab648c06b183690fe6c60f9d8d20788c58e2', 'frontier/retained-transport/retained135125_survival_comparison.py': 'ba1911ccd385f22d2156e46c41620427af1330d92fa82806760dc02c1b8a774c', 'frontier/endpoint-bounds/k_face_common_seven_hinges.py': 'c382bed2ef52cc22c624c33f8aa2b1313df3a43935916f985c9c11060433c1e3', 'frontier/source-budgets/joint_selected_source_comparison.py': '849ecfdffec509678ace0ab6e059450a72959a44641a46715bcb489a5d376db8', 'frontier/retained-transport/retained_deletion_heavy_comparison.py': '553c281d5de5a9bcd9098ea933f6cccf046b587132e6fa49ec4aa8b44b4ec86f', 'frontier/endpoint-bounds/k_neighborhood_radius_study.py': 'f5b6d2df57ee047a3d47660812e8fc3ff0a81239db15881634b4ad0b01633b0f', 'frontier/source-budgets/wide_fresh_full_slot_source_comparison.py': '4180ce2f7cb27179e7f8f10092d31c61f7da90e4c03623c07ff796c43f9a599d', 'frontier/source-budgets/extended_source_bridge_comparison.py': '2c40c799b23de126166ba8e95c942f36f27587896d536a2fece790b508ffe92a', 'certificates/source_norms/retained-transport/retained135125_heavy_comparison.json': '451537f6ee699920c955ba0401cedba672f0aaabc97ad193cb282163bcfaf6cf', 'certificates/source_norms/retained-transport/retained135125_survival_comparison.json': '51e1c09c96c819b1fb292762dbc082f293d9ba3f6c22a504959f04ae508ca47e', 'certificates/source_norms/source-budgets/wide_fresh_full_slot_source_comparison.json': '31f20d1d614a6b961fe00642340a9fc3b5ac61d16862e02617337dabbbd8d427', 'certificates/source_norms/source-budgets/extended_source_bridge_comparison.json': '381ee12bc564ba3c36fb1ff1b14de9d237bff16c5bf7875fdae8e2bf6c66bea2', 'profile-notes/065-128/125-the-complete-off-face-omitted-tails-recover-every-face-constant.md': '5faf1c5ff5edf0881951c9337a431805e70edcbb8d81a8dce76cbc42d230f5b9', 'profile-notes/129-192/134-one-complete-cost-is-uniform-on-a-nonzero-k-neighborhood.md': '156ca174c75e7ed974a164d536a10212d25928f4b20d2cfb5158ea81e4e5bdca', 'profile-notes/129-192/156-exposing-each-loss-gives-exact-rational-joint-price-bounds.md': 'dd28a0704a8cc025d79781093236bd4fe328e4e404c0d92e78d7c30ec99a7bd9', 'profile-notes/129-192/157-a-signed-tail-comparison-covers-the-one-over-twenty-seven-neighborhood.md': 'b860f0a543a00174b43a3fad90d96fdbba6511801f796b1b66fda58079bb0d02', 'profile-notes/129-192/158-the-seven-containing-pair-tails-have-one-exposed-source-price.md': 'ed87fe2ddb3a36687fdcfe02fa6142e5999cb79cdd1e811074b793f4ea1fe841', 'profile-notes/193-256/195-the-complete-source-comparison-extends-beyond-the-old-radius-domain.md': '6925b9aecf2e7be0bc46d78c919f9cc6f6c10e84199014fc85bab854829231bb', 'profile-notes/193-256/208-the-expanded-seven-survival-bound-covers-both-wide-source-domains.md': '4f90b9c454f4d19aab6ea9e8bf3fe41b1cee1d3e586a03f6a3d3ab9c8faca6d6', 'profile-notes/193-256/211-all-four-selected-labels-can-be-retained-above-the-first-hinge.md': 'a57b7a5e6d531412b5cebc11d42c1ce2617cc8d3f19651887447b30fe0f13781', 'profile-notes/193-256/223-the-original135-test-enters-the-complete-heavy-bridge.md': '36e09df1322b87a428b52f36b295e74292ce5ce66addb1e6b8737c8c6513bf9e', 'profile-notes/193-256/225-two-original-tests-share-the-complete-retained-bridge.md': '27d5e9c311b5f1a949d35d5eab4d3dd5ec7f22febf6703bf12a728daf957b686', 'profile-notes/193-256/226-the-joint135125-records-strengthen-two-complete-survival-bounds.md': 'c07abb74484f7b84e4858d2431ee7e4975e08f5321b253bd60d5fb3d841f5621'}
FAMILIES = ('pure3', 'pure5', 'root5', 'cell5')
BASES = (3, 5, 5, 5)
STARTS = (3, 2, 2, 2)
PUNCTURED_STARTS = (5, 4, 3, 2)
PRIMITIVES = ('shallow_five_shifted_defect', 'shallow_alpha_shifted_defect',
              'pure_three_27_defect', 'pure_three_later_defect',
              'pure_deep_five_defect', 'alpha_deep_five_defect', 'union_overlap')
DOMAINS = ('wide_fresh_full_slot_source_comparison', 'extended_source_bridge_comparison')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable proof provider')
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


def geometric_support(p, first, cut):
    """Exact full mass, finite error count and infinite geometric continuation."""
    require(type(p) is int and p > 1 and type(first) is int and first >= 1
            and type(cut) is int and cut >= 1, 'Integer geometric support parameters')
    n = max(first, cut)
    return F(1, (p-1)*p**(first-1)), max(cut-first, 0), F(1, (p-1)*p**(n-1))


def envelopes(d):
    d = F(d)
    require(0 <= d <= F(1, 12), 'Proved uniform source radius through1/12')
    c = (F(7, 10)+d/4, F(2, 5)+13*d/90, F(4, 15)+d/15, F(4, 45)+d/45)
    h = (F(1, 20), F(1, 10)-4*d/45, (1-d)/15, (1-d)/45)
    return c, h


def hinge_weights(coefficients):
    require(isinstance(coefficients, dict) and coefficients, 'Finite original hinge coefficients')
    parsed = {}
    for key, value in coefficients.items():
        require((type(key) is int or isinstance(key, str) and key == str(int(key)))
                and int(key) >= 1 and F(value) >= 0, 'Positive hinge index and nonnegative coefficient')
        require(int(key) not in parsed, 'One coefficient per hinge')
        parsed[int(key)] = F(value)
    return parsed.get(1, F(0)), sum((a for t, a in parsed.items() if t >= 2), F(0))


def face_tail(coefficients):
    w0, w6 = hinge_weights(coefficients)
    return w0*(F(163, 1800)+F(2669, 88200))+w6*(F(7579, 405000)+F(2669, 88200))


def compile_tail_support(d, hinge_coefficients, cuts):
    """Compile one fixed eight-cut support into the existing seven defects.

    `cuts` has four integers in each of `unpunctured` and `punctured`, in
    FAMILIES order. The latter removes25,27,75,81,135,125 at their actual
    exponent locations. No finite exponent cutoff replaces the continuation.
    """
    d = F(d)
    c, h = envelopes(d)
    w0, w6 = hinge_weights(hinge_coefficients)
    require(set(cuts) == {'unpunctured', 'punctured'}, 'Both occurrence classes have fixed cuts')
    require(all(len(cuts[k]) == 4 and all(type(n) is int and n >= b
                for n, b in zip(cuts[k], STARTS)) for k in cuts), 'Four legal cuts per occurrence class')
    ell, slopes, continuation = [], [], []
    for j, p in enumerate(BASES):
        empty = geometric_support(p, STARTS[j], cuts['unpunctured'][j])
        retained = geometric_support(p, PUNCTURED_STARTS[j], cuts['punctured'][j])
        for target, k in ((ell, 0), (slopes, 1), (continuation, 2)):
            target.append(w0*empty[k]+w6*retained[k])
    m3, m5, m15, m45 = slopes
    kappa = (6-d)/(3-2*d)
    seven = F(2669, 88200)+23*d/5880
    intercept = sum(cj*lj+hj*bj for cj, hj, lj, bj in zip(c, h, ell, continuation))
    intercept += d*m5/240+w0/72+7*w6/1080+(w0+w6)*seven
    primitive = dict(zip(PRIMITIVES, (m3, kappa*m3, m5, m5, m3, kappa*m3,
                                    m3+m5+m15+m45)))
    require(min(primitive.values()) >= 0 and all(0 <= b <= l for b, l in zip(continuation, ell)),
            'Nonnegative shared residual prices and exact remaining geometric masses')
    return {'delta': d, 'cuts': cuts, 'w0': w0, 'w6': w6, 'geometric_masses': ell,
            'error_slopes': slopes, 'geometric_continuations': continuation,
            'intercept': intercept, 'wrong_slot_prices_over_gap': [m3, kappa*m3],
            'primitive_additions': primitive, 'positive_seven_upper': seven,
            'face_tail': face_tail(hinge_coefficients)}


def support_candidates(d, residual_radius, hinge_coefficients):
    """81 deterministic supports; no claim to global cut optimality."""
    d, radius = F(d), F(residual_radius)
    _, h = envelopes(d)
    hinge_weights(hinge_coefficients)
    require(radius > 0, 'Positive residual radius for this finite candidate generator')
    maximum_errors = ((6-d)/(3-2*d)*radius, radius+d/240, radius, radius)
    starts = []
    for firsts in (STARTS, PUNCTURED_STARTS):
        row = []
        for p, first, headroom, error in zip(BASES, firsts, h, maximum_errors):
            cut = first
            while headroom/F(p**cut) >= error:
                cut += 1
            row.append(cut)
        starts.append(row)
    return [{'unpunctured': [a+k for a, k in zip(starts[0], offsets)],
             'punctured': [a+k for a, k in zip(starts[1], offsets)]}
            for offsets in product(range(3), repeat=4)]


def _raw_vertices(row, parameters, caps, budgets, bridge):
    d, radius, gap = [F(parameters[k]) for k in ('delta', 'rho', 'gap')]
    envelopes(d)
    require(radius >= 0 and gap > 0, 'Nonnegative radius and positive common wrong-slot gap')
    caps, budgets = list(map(F, caps)), list(map(F, budgets))
    require(len(caps) == 25 and len(budgets) == 3 and min(caps+budgets) >= 0,
            'The fixed nonnegative25-node, three-group raw polytope')
    base_prices = list(map(F, row['raw_base_prices']))
    node = list(map(F, row['common_raw_node_prices']))
    require(len(base_prices) == len(node) == 25 and min(base_prices+node) >= 0
            and set(row['primitive_prices']) == set(PRIMITIVES)
            and min(map(F, row['primitive_prices'].values())) >= 0,
            'Complete current230 row with seven nonnegative prices and zero survivor-mass price')
    result = []
    for q5, q15 in ((F(0), F(0)), (radius/gap, F(0)), (F(0), radius/gap)):
        coefficients = [base_prices[i]+node[i]*(d/5*int(i//5 != 0)+q5*int(i % 5 == 4)
                        +q15*int(i//5 >= 2 and i % 5 == 4)) for i in range(25)]
        raw, witness = bridge.lp_bound(coefficients, caps, budgets)
        result.append({'q': [q5, q15], 'residual_radius': radius-gap*(q5+q15),
                       'signed_raw_transport': raw-F(row['raw_face_subtraction']),
                       'raw_primal_dual_witnesses': witness})
    return result


def _evaluate(row, parameters, support, raw_vertices):
    require(F(parameters['delta']) == F(support['delta']), 'One common source radius')
    gap = F(parameters['gap'])
    primitive = {k: F(row['primitive_prices'][k])+F(support['primitive_additions'][k]) for k in PRIMITIVES}
    largest = max(primitive.values())
    vertices = []
    for raw in raw_vertices:
        q5, q15 = raw['q']
        wrong = gap*sum(a*q for a, q in zip(support['wrong_slot_prices_over_gap'], (q5, q15)))
        value = F(row['combined_source_upper'])+support['intercept']+raw['signed_raw_transport']
        value += wrong+raw['residual_radius']*largest
        vertices.append({**raw, 'tail_wrong_slot_upper': wrong, 'row_and_tail_upper': value})
    bound = max(v['row_and_tail_upper'] for v in vertices)
    return {'support': support, 'joint_primitive_prices': primitive, 'joint_residual_price': largest,
            'triangle_vertices': vertices, 'row_and_tail_upper': bound,
            'row_and_tail_minus_face_tail_upper': bound-support['face_tail']}


def evaluate_row_support(row, parameters, caps, budgets, bridge, support):
    """Evaluate one support for an arbitrary230 row on the complete domain.

    `rho` in parameters is the domain radius R; actual rho may lie in[0,R].
    Current230 records have zero survivor-mass price. A future signed mass
    extension must add that price and the fourth(q5,q15,rho) vertex explicitly.
    """
    return _evaluate(row, parameters, support, _raw_vertices(row, parameters, caps, budgets, bridge))


def choose_support(row, parameters, caps, budgets, bridge, hinge_coefficients, candidates):
    """Maximize each fixed support on the whole domain, then minimize the list."""
    require(candidates, 'An actual nonempty finite support list')
    raw = _raw_vertices(row, parameters, caps, budgets, bridge)
    values, best = [], None
    for index, cuts in enumerate(candidates):
        support = compile_tail_support(parameters['delta'], hinge_coefficients, cuts)
        result = _evaluate(row, parameters, support, raw)
        values.append({'index': index, 'cuts': cuts, 'row_and_tail_upper': result['row_and_tail_upper']})
        if best is None or result['row_and_tail_upper'] < best['row_and_tail_upper']:
            best = {**result, 'candidate_index': index}
    return {'candidate_count': len(values), 'candidates': values, 'selected': best}


def _selected_bank(encoded, keys, provider):
    buckets = {}
    for key in sorted(keys):
        buckets.setdefault(key[0], {}).setdefault(key[1], {})[key] = encoded['dual_buckets'][key[0]][key[1]][key]
    return provider.decode_dual_bank({**encoded, 'dual_buckets': buckets}, 7163, 56)


def calculate(base):
    require(PINS, 'Audited source pins')
    io = module('tail_support_io', base/'certificate_io.py')
    read = lambda rel: json.loads(io.read_artifact_bytes(base/rel))
    heavy, survival = [read(io.named_artifact(base/'certificates/source_norms', name + '.json').relative_to(base).as_posix()) for name in
                       ('retained135125_heavy_comparison', 'retained135125_survival_comparison')]
    domains = {name: read(io.named_artifact(base/'certificates/source_norms', name + '.json').relative_to(base).as_posix()) for name in DOMAINS}
    pins = dict(PINS)
    for doc in [heavy, survival]+list(domains.values()):
        for path, pin in doc['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    load = lambda name: module('tail_support_'+name, io.named_artifact(base/'frontier', name+'.py'))
    complete, partial, old, e5 = map(load, ('complete_retained_row_transport', 'retained_pair_row_transport',
                                         'joint_deletion_row_transport', 'selected_deletion_mask_row_transport'))
    exact, pair, bridge = map(load, ('retained135_heavy_comparison', 'retained135125_heavy_comparison',
                                   'k_face_common_seven_hinges'))
    tests = []
    for row in heavy['heavy_results']:
        tests.append({'name': 'heavy-'+str(row['index']), 'bank': 'heavy',
                      'hinge_coefficients': row['scan']['coefficients'], 'scan': row['scan']})
    for name, row in (('AP13', survival['AP13_result']), ('AP11-block0', survival['AP11_block_results'][0])):
        require(row['hinge_coefficients'] == row['scan']['coefficients'], 'Same original survival objective')
        tests.append({'name': name, 'bank': 'survival', 'hinge_coefficients': row['hinge_coefficients'], 'scan': row['scan']})
    require([v['name'] for v in tests] == ['heavy-0', 'heavy-16', 'AP13', 'AP11-block0'], 'Four original objectives')
    banks = {}
    for kind, packed in (('heavy', heavy['encoded_rational_duals']), ('survival', survival['rational_duals'])):
        keys = {key for t in tests if t['bank'] == kind
                for key in t['scan']['maximizing_witness']['nested_disjoint_dual_keys'].values()}
        require(len(keys) == 4, 'Two distinct branch controllers per objective')
        banks[kind] = _selected_bank(packed, keys, exact)
    pre, _, density, descendant = bridge.source_tables(2)
    wi = [int(5*w) for row in density for w in row]
    raw = load('joint_selected_source_comparison').RawSelectedLP(bridge)
    original = load('retained_deletion_heavy_comparison').RetainedDeletionLP(raw, wi)
    inventories, constraints, lps = {}, {}, {}
    for branch in ('nested', 'disjoint'):
        oldlp = exact.lp_class(base)(original, wi, pre, branch)
        lp = pair.lp_class(base)(original, wi, pre, descendant, branch)
        require(lp.specification() == heavy['branch_lps'][branch] == survival['branch_lps'][branch],
                'The same original complete branch matrix')
        e5.check_row_meanings(oldlp, wi)
        inventory = old.row_inventory(oldlp, wi), partial.new_inventory(lp, pre, descendant, wi)
        constraints[branch] = complete.complete_inventory(lp, original, bridge, wi, *inventory)
        inventories[branch], lps[branch] = inventory, lp
    study = load('k_neighborhood_radius_study').Study(base)
    require(all(pins.get(path) == pin for path, pin in study.pins.items()), 'Same proved source-domain providers')
    output = []
    for name, domain in domains.items():
        par, guards = study.get(name).parameters_and_guards(study)
        require(encode(guards) == domain['guards'], 'Original full source-domain guards')
        caps, budgets = [list(map(F, domain['complete_heads'][key])) for key in ('uniform_caps', 'uniform_budgets')]
        results = []
        for test in tests:
            coefficients = test['hinge_coefficients']
            witness = test['scan']['maximizing_witness']
            ftail = face_tail(coefficients)
            require(ftail == F(witness['complete_tail_constant']), 'No lost or duplicated original face tail')
            candidates = support_candidates(par['delta'], par['rho'], coefficients)
            branches = {}
            for branch, key in witness['nested_disjoint_dual_keys'].items():
                dual = banks[test['bank']][key]
                lp = lps[branch]
                y = {int(i): F(v) for i, v in dual['nonzero_inequality_duals'].items()}
                z = list(map(F, dual['equality_duals']))
                raw_upper = sum(v*lp.rhs[i] for i, v in y.items())+sum(a*b for a, b in zip(z, lp.erhs))
                require(raw_upper == F(dual['raw_objective_upper']), 'Original exact dual right-hand-side value')
                inherited, _ = partial.price_record(dual, par, caps, budgets, bridge, old, e5, *inventories[branch])
                row, _ = complete.price_record(dual, inherited, par, caps, budgets, bridge)
                choice = choose_support(row, par, caps, budgets, bridge, coefficients, candidates)
                selected = choice['selected']
                branches[branch] = {'dual_key': key, 'original_raw_dual_upper': raw_upper,
                    'original_face_branch_upper': raw_upper+ftail, 'complete_row_record': row,
                    'support_choice': choice, 'fixed_controller_row_and_tail_upper': raw_upper+selected['row_and_tail_upper'],
                    'increment_over_face_branch_upper': selected['row_and_tail_minus_face_tail_upper']}
            require(max(v['original_raw_dual_upper'] for v in branches.values()) == F(witness['joint_raw_upper']),
                    'These are the original selected nested/disjoint controllers')
            results.append({'objective': test['name'], 'hinge_coefficients': coefficients,
                            'original_layout': witness['layout'],
                            'original_projections': witness['projections21_35_63_105_147_245'],
                            'face_tail': ftail, 'branches': branches,
                            'two_branch_fixed_controller_upper': max(v['fixed_controller_row_and_tail_upper'] for v in branches.values())})
        output.append({'source_domain': name, 'delta': par['delta'], 'rho': par['rho'], 'gap': par['gap'],
                       'raw_caps': caps, 'raw_budgets': budgets, 'results': results})
    return encode({'schema': 'erdos7-retained-punctured-tail-support-v1', 'source_sha256': pins,
        'families': FAMILIES, 'bases': BASES, 'first_unpunctured_depths': STARTS,
        'first_punctured_depths': PUNCTURED_STARTS, 'primitive_order': PRIMITIVES,
        'constraint_inventory': constraints, 'domains': output,
        'scope': 'Complete fixed-row residual plus complete infinite tails for eight original225/226 maximizing-controller duals on two208 source domains.81 fixed supports per controller are individually maximized over the whole domain before the smallest is selected. Finite support-library optimum only; current230 zero survivor-mass guard. No new full head scan, no transport of every other dual or pruned alternative, no off-face/global52-cost K bound, no actual-family attainment, no Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('tail_support_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact fixed-support tail certificate')
    for domain in result['domains']:
        for test in domain['results']:
            print(domain['source_domain']+' '+test['objective']+': fixed-controller upper='
                  +str(float(F(test['two_branch_fixed_controller_upper']))))
    print('PASS:16 controller-domain cases,81 complete supports each; no complete off-face K claim.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
