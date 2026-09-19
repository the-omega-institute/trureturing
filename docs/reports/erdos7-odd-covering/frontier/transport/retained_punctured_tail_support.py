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
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/transport/complete_retained_row_transport.py': '1780245b41e81b3b4e3706c2dce7ef5db6b89612bda88624b9d8e1d80126efde', 'frontier/transport/retained_pair_row_transport.py': '97efea8c615889c73964130b597f6246620a0133c4e2144a18e6cfb4f24528be', 'frontier/transport/joint_deletion_row_transport.py': '22eea33556056edb038580598002e32c74d4cfa9297a6c07c4bfc2ae34469d3d', 'frontier/transport/selected_deletion_mask_row_transport.py': '5a1ac7bfc00bf04edc27ec4b87e2fd232eaa989cc6e50edad1536f10ae7b1ae9', 'frontier/transport/retained135_heavy_comparison.py': 'f9bef9ef1d78395ca57da56e64e7ab218e6b45bd49de91adfafddd2220d61907', 'frontier/transport/retained135125_heavy_comparison.py': '5e7a8bdd7ee1e93afd3115c80a8792d0afbf035ac50be715cf69631b75c70ff5', 'frontier/transport/retained135125_survival_comparison.py': '600cc560ea2d8c7d5698aca79539e0c1b1de8fc4440bda7f323fef605ab7cdff', 'frontier/k_face_common_seven_hinges.py': '8cc4600c9b3f2f65a11820fcb2d0d6663c765c20765bbaf1ae0de6e883cefc97', 'frontier/transport/joint_selected_source_comparison.py': 'ab18c0c4ac40af60f7c974393d82738ec4d762ccefa7f5efe61cf4b963b3673c', 'frontier/transport/retained_deletion_heavy_comparison.py': '3283d6a9fbd0863ab2c8a22042b2b4e2bec8feeff24f3bf94a86e77e0a86ce1c', 'frontier/k_neighborhood_radius_study.py': '41cbad92bacf1cd7b573afb48ecc0811fc0df05fe9a56cfa274d3f4fbb175682', 'frontier/wide_fresh_full_slot_source_comparison.py': '8b92c7eda87c06ca763d50015b5dd6078730cdb3c7af81aa8a46c989ba3f425d', 'frontier/transport/extended_source_bridge_comparison.py': '4b9e21988e129c3aff849afefe563e92154cca7075e40eff5d20ae33418a403d', 'certificates/source_norms/retained-transport/retained135125_heavy_comparison.json': '98195f65f9d5acc4a27b8275952488b928e5204c56871e9a41cf4f32cf0e4ff6', 'certificates/source_norms/retained-transport/retained135125_survival_comparison.json': '67d7003462bde8fa391245e76f226694cea286ab005d0404a7cfe4046453b797', 'certificates/source_norms/wide_fresh_full_slot_source_comparison.json': '7e8ba6cbd1fa404bf9274cd32e102fa40bf9b7bc7c4ad4c46c2b42b71a61a71a', 'certificates/source_norms/extended_source_bridge_comparison.json': 'd38c7de4dc87e8467f4ee6e3a4ae3a71affccf652d88aa169e093b888e675451', 'profile-notes/125-the-complete-off-face-omitted-tails-recover-every-face-constant.md': 'cbe1fc88855354bd58e7a11ff22574bd8f9f9f94dceb57612c3ac8b1d943df17', 'profile-notes/134-one-complete-cost-is-uniform-on-a-nonzero-k-neighborhood.md': '34faadac8c86d5ae038a88fa2f70c0eb29bd2400c72881d3032d183182d4a60e', 'profile-notes/156-exposing-each-loss-gives-exact-rational-joint-price-bounds.md': '97e06983dc0c964fb935a34e6561f1cbcfaaad3adef845c6ab24dd9d56f5c3a1', 'profile-notes/157-a-signed-tail-comparison-covers-the-one-over-twenty-seven-neighborhood.md': 'a321a53464c451476f9193c75e28af366c0cffe36121605e50e99cc15d451fbf', 'profile-notes/158-the-seven-containing-pair-tails-have-one-exposed-source-price.md': '782a5b48fb152002ec55b2753bcf976799f5c8a8cabaa37481fe9f399c932127', 'profile-notes/transport/195-the-complete-source-comparison-extends-beyond-the-old-radius-domain.md': '4ce83eb8dce7127273b13d431f23d608eed3e152218a6eaf57406c60e339b991', 'profile-notes/transport/208-the-expanded-seven-survival-bound-covers-both-wide-source-domains.md': '9beb7e1c7eb5b006d896927b536d4a85a2b11b39ad16025941907762a31ad5e2', 'profile-notes/transport/211-all-four-selected-labels-can-be-retained-above-the-first-hinge.md': 'fdccfb2e8d5a6f7162619bbce8b0c048027b1b627dc5faf0f082c25815f88c63', 'profile-notes/transport/223-the-original135-test-enters-the-complete-heavy-bridge.md': '56dc704a53e9636c60a3803b8965fb420e74e1c52113736b99267bd46932338f', 'profile-notes/transport/225-two-original-tests-share-the-complete-retained-bridge.md': 'c0fb6383f17d2e9550481b98c64796eff4e9c2ef2b323b456911a1610047dfaf', 'profile-notes/transport/226-the-joint135125-records-strengthen-two-complete-survival-bounds.md': 'c8335f3d5ca7d81c35ef90d76b1752366053ec131a43a46d2746ef9085261ae5'}
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
    heavy, survival = [read('certificates/source_norms/retained-transport/'+name+'.json') for name in
                       ('retained135125_heavy_comparison', 'retained135125_survival_comparison')]
    domains = {name: read('certificates/source_norms/'+name+'.json') for name in DOMAINS}
    pins = dict(PINS)
    for doc in [heavy, survival]+list(domains.values()):
        for path, pin in doc['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    load = lambda name: module('tail_support_'+name, base/'frontier'/(name+'.py'))
    complete, partial, old, e5 = (load('transport/complete_retained_row_transport'), load('transport/retained_pair_row_transport'), load('transport/joint_deletion_row_transport'), load('transport/selected_deletion_mask_row_transport'))
    exact, pair, bridge = (load('transport/retained135_heavy_comparison'), load('transport/retained135125_heavy_comparison'), load('k_face_common_seven_hinges'))
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
    raw = load('transport/joint_selected_source_comparison').RawSelectedLP(bridge)
    original = load('transport/retained_deletion_heavy_comparison').RetainedDeletionLP(raw, wi)
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
    for (name, domain), provider in zip(domains.items(), (study.get('wide_fresh_full_slot_source_comparison'), study.get('transport/extended_source_bridge_comparison')), strict=True):
        par, guards = provider.parameters_and_guards(study)
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
