#!/usr/bin/env python3
"""Complete original J comparison from actual aligned own-load bounds.

Checks every whole-integer envelope and uses no saturated numerical source
bound or old independent-moment witness. Python 3 standard library only.
"""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_aligned_complete_moment_comparison.json'
ORIGINAL = 'certificates/source_norms/j-geometry/j_face_heavy_positive175189_complete_moment_cost_comparison.json'
SOURCE_NAMES = (
    'j_aligned_own_test_interface',
    'j_aligned_joint_selected_heads',
    'j_aligned_remaining_hinges',
    'j_aligned_retained375_heavy553_prefix',
    'j_aligned_retained375_heavy553_heads',
    'j_aligned_retained375_h4_prefix',
    'j_aligned_retained375_h4_heads',
    'j_aligned_quadratic_complete_heads',
)
HELPERS = (
    'certificate_io.py', 'verify_joint_frontier.py',
    'frontier/source-budgets/source_barrier_saturation.py',
    'frontier/cover-geometry/ap_schedule.py', 'frontier/comparison-bounds/fixed_cost.py',
    'frontier/j-geometry/j_face_complete_moment_cost_comparison.py',
    'frontier/j-geometry/j_face_complete_survival_linear_heads.py',
    'frontier/j-geometry/j_aligned_own_test_interface.py',
    'frontier/j-geometry/j_aligned_joint_selected_heads.py',
    'frontier/j-geometry/j_aligned_remaining_hinges.py',
    'frontier/j-geometry/j_aligned_retained375_source.py',
    'frontier/j-geometry/j_aligned_retained375_prefix.py',
    'frontier/j-geometry/j_aligned_retained375_heads.py',
    'frontier/j-geometry/j_aligned_quadratic_sharp_source.py',
    'frontier/j-geometry/j_aligned_quadratic_complete_heads.py',
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Readable mathematical provider')
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
    io = module('aligned_complete_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path), object_pairs_hook=io._unique)
    docs = {name: read(io.named_artifact(base/'certificates/source_norms', name + '.json').relative_to(base).as_posix()) for name in SOURCE_NAMES}
    original = read(ORIGINAL)
    paths = [ORIGINAL, *HELPERS, *(io.named_artifact(base/'certificates/source_norms', n + '.json').relative_to(base).as_posix() for n in SOURCE_NAMES)]
    pins = {p: sha256(io.read_artifact_bytes(base/p)).hexdigest() for p in paths}
    # Only the original function inventory escapes this provider. Its old
    # source bounds and parameter vertices are never supplied to this consumer.
    engine = module('aligned_complete_inventory', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    for path, pin in engine.pins.items():
        require(path not in pins or pins[path] == pin, 'Consistent original function identity')
        pins[path] = pin
    source = engine.source
    algebra = module('aligned_complete_envelopes', base/'frontier/j-geometry/j_face_complete_moment_cost_comparison.py')
    jobs, count = module('aligned_complete_counts', base/'frontier/j-geometry/j_face_complete_survival_linear_heads.py').prepare_jobs(source, engine)
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    require(len(tags) == 52 and encode(tags) == original['original_cost_tags']
            and original['all_original_indices'] == list(range(52))
            and encode(count) == original['count_law'], 'All original distinct costs and the entire count law')

    fun = {'mass': lambda n: F(1), 'mean': lambda n: F(n), 'square': lambda n: F(n*n)}
    poly = {'mass': (F(1), F(0), F(0)), 'mean': (F(0), F(1), F(0)), 'square': (F(0), F(0), F(1))}
    for t in (2, 3, 4, 5, 6, 8):
        name = 'hinge'+str(t)
        fun[name] = lambda n, t=t: F(max(n-t, 0))
        poly[name] = (F(-t), F(1), F(0))
    for t in (2, 3, 5):
        name = 'factorial'+str(t)
        fun[name] = lambda n, t=t: F(max(n-t, 0)*(n-t+1), 2)
        poly[name] = (F(t*(t-1), 2), F(1-2*t, 2), F(1, 2))
    for i in (0, 48, 49):
        name = 'cost'+str(i)
        fun[name] = lambda n, tag=tags[i]: source.zero5_cost(tag, n)
        poly[name] = algebra.cost_polynomial(source, tags[i])
    for job in jobs[:4]:
        co = job['coefficients']; name = job['name']
        fun[name] = lambda n, co=co: sum(a*max(n-t, 0) for t, a in co.items())
        poly[name] = (-sum(t*a for t, a in co.items()), sum(co.values()), F(0))
    old_basis = {r['name']: r for r in original['basis']}
    for name in fun:
        row = old_basis[name]
        require([fun[name](n) for n in range(1, 9)] == list(map(F, row['low_load_values']))
                and poly[name] == tuple(map(F, row['tail_polynomial'])), 'Exact original whole-integer function '+name)

    own = docs['j_aligned_own_test_interface']
    bounds = {'mass': F(own['source_mass']), 'mean': F(own['complete_mean_upper'])}
    origin = {'mass': '312', 'mean': '312'}
    require(bounds == {'mass': F(413, 2700), 'mean': F(293, 450)}, 'Actual aligned exact mass and complete mean')
    for name, number in (('j_aligned_joint_selected_heads', '313'), ('j_aligned_remaining_hinges', '314')):
        doc = docs[name]
        require(F(doc['actual_survivor_mass']) == bounds['mass'], 'The same actual survivor for all own-load observations')
        for row in doc['results']:
            require(row['name'] not in bounds, 'One source bound per original observation')
            bounds[row['name']] = F(row['complete_upper']); origin[row['name']] = number
    for tag, name in (('heavy553', 'cost0'), ('h4', 'hinge4')):
        prefix = docs['j_aligned_retained375_'+tag+'_prefix']
        doc = docs['j_aligned_retained375_'+tag+'_heads']
        require(doc['name'] == prefix['name'] == name
                and doc['covered_original_choices'] == prefix['covered_containing_choices'] == 3125000000
                and doc['prefix_sha256'] == pins['certificates/source_norms/j-geometry/j_aligned_retained375_'+tag+'_prefix.json']
                and doc['provider_sha256'] == pins['frontier/j-geometry/j_aligned_retained375_source.py']
                and (doc['model']['variables'], doc['model']['inequalities'], doc['model']['equalities']) == (12941, 30454, 23),
                'Complete actual retained-label bound and its own prefix')
        upper = F(doc['complete_uniform_upper'])
        require(upper < bounds[name], 'The complete retained-label source improves its earlier bound')
        bounds[name] = upper; origin[name] = '315'
    quad = docs['j_aligned_quadratic_complete_heads']
    require(quad['schema'] == 'erdos7-aligned-quadratic-complete-heads-v1'
            and F(quad['actual_raw_mass']) == F(1, 4) and F(quad['actual_survivor_mass']) == bounds['mass']
            and quad['original_choices_per_observation'] == 3125000000
            and {r['name'] for r in quad['results']} == {'square', 'factorial2', 'factorial3', 'factorial5', 'cost48', 'cost49'}
            and len(quad['results']) == 6, 'All six remaining complete observations use this same actual source')
    for row in quad['results']:
        require(row['name'] not in bounds, 'No numerical source assumption replaces an aligned observation')
        bounds[row['name']] = F(row['complete_uniform_upper']); origin[row['name']] = '316'

    targets = [('cost-'+str(i), lambda n, tag=tag: source.zero5_cost(tag, n), algebra.cost_polynomial(source, tag)) for i, tag in enumerate(tags)]
    targets += [(name, fun[name], poly[name]) for name in algebra.EXTERNAL_TARGETS]
    proofs = original['proof_data']
    require([p['name'] for p in proofs] == [t[0] for t in targets] and len(targets) == 59, 'Every original target retained')
    used = set().union(*(set(p['coefficients']) for p in proofs))
    require(used == set(bounds) and len(used) == 18, 'Exactly mass, mean and16 complete aligned observations; no inherited saturated upper remains')
    rows = []
    for proof, (name, target, target_poly) in zip(proofs, targets):
        co = {k: F(v) for k, v in proof['coefficients'].items()}
        require(all(a >= 0 for k, a in co.items() if k != 'mass'), 'Only exact actual mass has a signed envelope coefficient')
        low = [sum(a*fun[k](n) for k, a in co.items())-target(n) for n in range(1, 9)]
        tail = tuple(sum(a*poly[k][j] for k, a in co.items())-target_poly[j] for j in range(3))
        minimum, loads, values = algebra.tail_minimum(tail)
        require(min(low) >= 0 and minimum >= 0, 'Whole-positive-integer envelope for the target test own load: '+name)
        rows.append({'name': name, 'upper': sum(a*bounds[k] for k, a in co.items()),
                     'coefficients': co, 'low_load_gaps': low, 'whole_tail_polynomial': tail,
                     'tail_test_integers': loads, 'tail_test_values': values, 'whole_tail_minimum': minimum})
    upper = {r['name']: r['upper'] for r in rows}
    mass = bounds['mass']; weights = list(map(F, original['cost_weights']))
    signed = F(original['signed_mass_coefficient']); square_weight = F(original['complete_square_weight']); offset = F(original['offset'])
    require(len(weights) == 52 and min(weights) > 0 and signed < 0 and square_weight > 0
            and offset == source.WHOLE_CONST, 'Original positive weights, negative exact-mass payment and unchanged offset')
    ap = module('aligned_complete_ap_weights', base/'frontier/cover-geometry/ap_schedule.py')
    specs, groups, quadratic = ap.inventory(source, engine.fixed, read('certificates/ap_schedule_norms.json'))
    group_weights = {'R17': F(1), 'R19': source.P17, 'R5': source.EXTRA5}
    linear_tail = sum(group_weights[g['name']]*g['tail_coefficient'] for g in groups)
    linear_constant = sum(group_weights[g['name']]*(g['expectation']-g['tail_coefficient']) for g in groups)
    finite, tails = source.ap_product_distribution(ap.CAPS, 9)
    raw_high = sum(p*n*n for n, p in finite.items() if n in (7, 8))
    quad_tail = quadratic['outside_active_first_moment']
    expected_weights = ([group_weights[s['name']] for s in specs[:40]]+[linear_tail]
                        +[source.AC]*5+[finite[n]*n*n for n in range(1, 7)])
    expected_signed = source.AC*(quadratic['expectation']-quad_tail)+linear_constant-81*tails[0]-raw_high
    expected_square = source.AC*quad_tail+tails[2]+raw_high
    require(weights == expected_weights and signed == expected_signed and square_weight == expected_square,
            'All original AP weights and signed payments follow from the whole function/count inventory')
    count_tail = count['remaining_hinge1_coefficient']*(upper['mean']-mass)+count['whole_constant_coefficient']*mass
    blocks = [upper['AP11-'+str(i)] for i in range(4)]
    denominator = mass-upper['hinge4']/6-(sum(blocks)+count_tail)/7
    payments = [w*upper['cost-'+str(i)] for i, w in enumerate(weights)]
    numerator = signed*mass+sum(payments)+square_weight*upper['square']
    require(upper['mean'] >= mass and min(blocks) >= 0 and count_tail >= 0
            and numerator > 0 and denominator > 0, 'Complete ratio comparison has its required signs')
    margin = (403-offset)*denominator-numerator
    comparison = offset+numerator/denominator
    require(margin > 0 and comparison < 403, 'Complete actual aligned J comparison is strictly below403')
    return encode({'schema': 'erdos7-aligned-complete-moment-comparison-v1', 'source_sha256': pins,
                   'domain': 'Actual countable-label endpoint qJ=1, source45/135 aligned, rho=2/675; either root0 orientation.',
                   'actual_survivor_mass': mass, 'basis': [{'name': k, 'upper': bounds[k], 'source': origin[k], 'mass_is_exact': k == 'mass'} for k in sorted(bounds)],
                   'all_original_indices': list(range(52)), 'original_cost_tags': tags, 'cost_weights': weights,
                   'signed_mass_coefficient': signed, 'complete_square_weight': square_weight, 'offset': offset,
                   'count_law': count, 'results': rows,
                   'comparison_upper': {'comparison': comparison, 'numerator': numerator, 'denominator': denominator,
                       'target403_numerator_margin': margin, 'complete_count_tail': count_tail, 'AP11_block_values': blocks,
                       'signed_mass_payment': signed*mass, 'outside_square_payment': square_weight*upper['square'], 'weighted_costs': payments},
                   'counts': {'actual_source_observations': 18, 'original_costs': 52, 'targets': 59,
                              'low_load_inequalities': 472, 'whole_tail_minima': 59},
                   'scope': 'Complete ordinary J inequality on the actual aligned endpoint. Every original function retains its own load and independent residues, one actual source and survivor, and complete exponent/count tails. No old saturated numerical bound or old finite moment witness is used. No actual optimizer, Gamma19 bound, explicit finite-source neighborhood, global join, later-prime continuation, unrestricted Erdos7 result or Lean verification is asserted.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = module('aligned_complete_writer', args.base/'certificate_io.py')
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path, json.dumps(result, indent=2)+'\n')
    else:
        given = json.loads(io.read_artifact_bytes(path), object_pairs_hook=io._unique)
        require(result == given, 'All own-load envelopes and complete signed comparison regenerate')
    print('PASS complete actual aligned J <=', float(F(result['comparison_upper']['comparison'])),
          'E >=', float(F(result['comparison_upper']['denominator'])),
          '403 margin >=', float(F(result['comparison_upper']['target403_numerator_margin'])))


if __name__ == '__main__':
    main()
