#!/usr/bin/env python3
"""Same-source J hinges and complete factorial moments for original costs47/48."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j_face_joint_quadratic_heads.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j_face_joint_selected_heads.py': '01033d19b43910a667954005342d2a03fe57dd6f621bf319398cfdb77ec821ec', 'certificates/source_norms/j_face_joint_selected_heads.json': '87038435aecbfee3d5a3845c29fe9ece863652a79a35312af00f1096b952fed6', 'frontier/j_face_shared_square_factorial.py': 'ff44159c9765bcdc54139f0840ee984bd4d223647b6434b805e852519df570f6', 'certificates/source_norms/j_face_shared_square_factorial.json': '3624e60d5a7f5851450feac9005e228354ea157c7b08de24ab3c6fc042609d44', 'frontier/j_face_joint_complete_moment_cost_comparison.py': '1fbbbff3ddadcfbd9fe31e36822e70344b325659275a89502a1779c14f648f54', 'certificates/source_norms/j_face_joint_complete_moment_cost_comparison.json': '2c82ccbe68f28bc3560ac5b482e7272a108f554bd2cffeaf6d15d2436184f10f', 'frontier/whole_quadratic_same_head.py': 'd447341c1887a1be5aae4ce46aa3405f594617929d7c8aa776a4b6032668d7a2', 'profile-notes/241-one-original-j-head-controls-complete-square-and-factorial-moments.md': '92bfc46b467c91fe6c332df159700ecc21eac264c4ec60edbcd290c3bdd7f8f1', 'profile-notes/244-three-complete-j-heads-share-raw-survivor-and-marked-deletion.md': '47ee1f78c3b5c2e4163d433aac3d1f9cd21955c9c6fd494938fa3b743e30565e', 'profile-notes/246-the-joint-j-heads-and-square-improve-the-complete-cost-comparison.md': '62f1f11f8dee3baf26b2d3996ec6d2b30c921e16a26e58bb53494c940e7e07b0'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original provider')
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


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Unique JSON key: '+key)
        result[key] = value
    return result


class JointQuadraticJHead:
    def __init__(self, base, moments, joint_certificate, bank=None, proposer=None):
        self.j = module('j_quadratic_source', base/'frontier/j_face_coupled_seven_heads.py')
        self.joint = module('j_quadratic_retained', base/'frontier/j_face_joint_selected_heads.py')
        moment = module('j_quadratic_moment', base/'frontier/j_face_shared_square_factorial.py')
        self.source = self.joint.JointSelectedJHead(base, self.j)
        self.head, self.lp = self.source.head, self.source.lp
        require(self.source.specification == joint_certificate['model'], 'Exactly the complete244 same-source model')
        problem = moment.JMomentHead(self.j)
        self.heads, digest = {}, sha256()
        largest = F(-1)
        for il, layout in enumerate(self.j.layouts()):
            parts = []
            for theta in (self.j.LO, self.j.HI):
                row = problem.components(layout, theta)
                digest.update(json.dumps(encode({'layout': layout, 'theta': theta, 'components': row}),
                                         separators=(',', ':')).encode())
                cross = row['factorial_old_cross']+row['factorial_positive7_cross']
                require(cross >= 0 and row['combined_factorial_head'] == row['factorial_head']+cross,
                        'Separate the actual Phi5(B) head from its complete two cross terms')
                parts.append((row['combined_factorial_head'], cross))
                largest = max(largest, row['combined_factorial_head'])
            self.heads[layout] = tuple(parts)
            if il % 2500 == 0:
                print('J quadratic: rebuilt Phi head '+str(il), flush=True)
        self.head_digest = digest.hexdigest()
        self.pair_tail = F(moments['complete_tail_partition']['distinct_tail_pairs'])
        require(len(self.heads) == 12500 and self.head_digest == moments['all_endpoint_components_sha256']
                and largest == F(moments['combined_head_maxima']['factorial']) == F(79, 450)
                and self.pair_tail == F(5089, 7200)
                and largest+self.pair_tail == F(moments['complete_factorial_upper']) == F(6353, 7200),
                'Every complete241 head, both common-theta endpoints and the entire distinct-pair tail')
        self.bank = {} if bank is None else bank
        self.proposer, self.used, self.verified = proposer, set(), {}

    def dual_upper(self, coefficients, factorial_coefficient, layout, projection):
        obj, constant = self.joint.objective(self.j, self.head, coefficients, layout, projection)
        B = self.head.bridge.head_load(layout)
        for cell, b in enumerate(B):
            phi = F(max(b-5, 0)*(b-4), 2)
            for mask in range(16):
                obj[425+16*cell+mask] += factorial_coefficient*phi
        cross0, cross1 = (row[1] for row in self.heads[layout])
        # The complete cross is convex in the common normalized x. Its endpoint
        # secant is an upper bound, implemented inside this same LP's x column.
        obj[875] += factorial_coefficient*(cross1-cross0)
        constant += factorial_coefficient*cross0
        require(len(obj) == 876 and min(obj[:875]) >= 0,
                'The same raw/survivor objective; only the late-coordinate slope may be negative')
        key = sha256(json.dumps([self.source.specification['rows_sha256'], encode(obj)],
                                separators=(',', ':')).encode()).hexdigest()
        if key not in self.verified:
            if key not in self.bank:
                require(self.proposer is not None, 'Missing exact J quadratic dual '+key)
                self.bank[key] = self.proposer(self.lp, obj)
            self.verified[key] = self.lp.check_dual(obj, self.bank[key])
        self.used.add(key)
        return self.verified[key]+constant, key, constant

    def scan(self, index, expansion):
        j, head = self.j, self.head
        co = {int(t): F(v) for t, v in expansion['hinge_coefficients'].items() if F(v)}
        fc = F(expansion['factorial_tail_coefficient'])
        require(fc > 0 and co and min(co.values()) > 0, 'Positive original hinge plus factorial expansion')
        prepared = head.prepare(co)
        scale = prepared['factor']/j.TOTAL
        independent = head.check_compiler(prepared)
        digest, used_before = sha256(), set(self.used)
        counts = {'two_projection_branches': 0, 'two_bounded': 0,
                  'four_projection_branches': 0, 'four_bounded': 0,
                  'joint_dual_branches': 0, 'strict_affine_crossings': 0}

        def old_bounds(layout, projection):
            B = head.bridge.head_load(layout)
            cor = head.correction(prepared, B)
            r, s, c, rr, ss = projection
            extra = tuple(int(j.ROOT[a] == r)+int(b == s) for a in range(5) for b in range(5))
            first = tuple(v+int(a == c)+int(j.ROOT[a] == rr and b == ss)
                          for v, (a, b) in zip(extra, ((a, b) for a in range(5) for b in range(5))))
            two = head.objective(prepared, B, extra, cor, False)
            four = head.objective(prepared, B, first, cor, True)
            two = tuple(scale*v+fc*p[0] for v, p in zip(two, self.heads[layout]))
            four = tuple(scale*v+fc*p[0] for v, p in zip(four, self.heads[layout]))
            value, x, crossed = j.max_min_affines(two, four)
            return value, x, two, four

        seed_layout, seed_projection = (1, 4, 2, 1, 2, 4, 2), (1, 4, 4, 1, 4)
        old, x, two, four = old_bounds(seed_layout, seed_projection)
        joint, key, constant = self.dual_upper(co, fc, seed_layout, seed_projection)
        best = min(old, joint)
        witness = {'layout': seed_layout, 'projection21_35_63_105': seed_projection,
                   'old_joint_head_upper': old, 'old_maximizing_late_coordinate': x,
                   'new_joint_head_upper': joint, 'adopted_head_upper': best,
                   'dual_key': key, 'objective_constant': constant}
        seed = dict(witness)
        max_two = max_four = F(-1)
        for il, layout in enumerate(j.layouts()):
            B = head.bridge.head_load(layout)
            cor = head.correction(prepared, B)
            for r, s, extra in head.extras:
                raw_two = head.objective(prepared, B, extra, cor, False)
                two = tuple(scale*v+fc*p[0] for v, p in zip(raw_two, self.heads[layout]))
                counts['two_projection_branches'] += 1
                if max(two) <= best:
                    counts['two_bounded'] += 1
                    max_two = max(max_two, max(two))
                    digest.update(repr(('two', layout, r, s, two)).encode())
                    continue
                for c, rr, ss, added in head.added:
                    first = tuple(a+b for a, b in zip(extra, added))
                    raw_four = head.objective(prepared, B, first, cor, True)
                    four = tuple(scale*v+fc*p[0] for v, p in zip(raw_four, self.heads[layout]))
                    old, x, crossed = j.max_min_affines(two, four)
                    counts['four_projection_branches'] += 1
                    counts['strict_affine_crossings'] += int(crossed)
                    if old <= best:
                        counts['four_bounded'] += 1
                        max_four = max(max_four, old)
                        digest.update(repr(('four', layout, r, s, c, rr, ss, two, four)).encode())
                        continue
                    projection = (r, s, c, rr, ss)
                    joint, key, constant = self.dual_upper(co, fc, layout, projection)
                    value = min(old, joint)
                    counts['joint_dual_branches'] += 1
                    digest.update(repr(('joint', layout, projection, two, four, key, str(joint))).encode())
                    if value > best:
                        best = value
                        witness = {'layout': layout, 'projection21_35_63_105': projection,
                                   'old_joint_head_upper': old, 'old_maximizing_late_coordinate': x,
                                   'new_joint_head_upper': joint, 'adopted_head_upper': value,
                                   'dual_key': key, 'objective_constant': constant}
            if il % 2500 == 0:
                print('J quadratic '+str(index)+': layouts='+str(il)
                      +', LP branches='+str(counts['joint_dual_branches']), flush=True)
        require(counts['two_projection_branches'] == 125000
                and counts['four_projection_branches'] == 50*(125000-counts['two_bounded'])
                and counts['four_bounded']+counts['joint_dual_branches'] == counts['four_projection_branches']
                and 50*counts['two_bounded']+counts['four_projection_branches'] == 6250000
                and max_two <= best and max_four <= best, 'Every original complete containing choice is covered')
        old, x, two, four = old_bounds(witness['layout'], witness['projection21_35_63_105'])
        joint, key, constant = self.dual_upper(co, fc, witness['layout'], witness['projection21_35_63_105'])
        require(old == witness['old_joint_head_upper'] and joint == witness['new_joint_head_upper']
                and key == witness['dual_key'] and min(old, joint) == best,
                'Exact maximizing certificate branch, without asserting actual-source attainment')
        r, s, c, rr, ss = witness['projection21_35_63_105']
        for theta in (j.LO, j.HI, j.LO+(j.HI-j.LO)*x):
            t = (theta-j.LO)/(j.HI-j.LO)
            phi = self.heads[witness['layout']]
            charge = fc*(phi[0][0]+(phi[1][0]-phi[0][0])*t)
            unscaled = [head.rational_objective(co, witness['layout'], p, theta)+charge
                        for p in ((r, s, None, None, None), (r, s, c, rr, ss))]
            require(unscaled == [v[0]+(v[1]-v[0])*t for v in (two, four)],
                    'Unscaled whole-theta hinge compiler plus the same factorial secant')
            independent += 2
        return {'hinge_coefficients': co, 'factorial_coefficient': fc, 'joint_head_upper': best,
                'complete_pair_tail_charge': fc*self.pair_tail,
                'counts': counts, 'covered_containing_choices': 6250000,
                'seed': seed, 'maximizing_certificate_branch': witness,
                'maximum_two_pruned': max_two, 'maximum_four_pruned': max_four,
                'new_distinct_duals': len(self.used-used_before), 'independent_affine_checks': independent,
                'all_branch_decisions_sha256': digest.hexdigest()}


def calculate(base, bank=None, proposer=None):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned canonical reader')
    io = module('j_quadratic_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')), object_pairs_hook=unique)
    moments, joint, prior = (read(name) for name in ('j_face_shared_square_factorial', 'j_face_joint_selected_heads',
                                                   'j_face_joint_complete_moment_cost_comparison'))
    pins = dict(PINS)
    for data in (moments, joint, prior):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original input '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned complete mathematical input '+path)
    require(moments['geometry'] == joint['geometry'] == prior['geometry']
            and all(F(data['survivor_mass']) == F(3,20) for data in (moments,joint,prior)),
            'Every input uses both identical complete saturated J faces')
    engine = module('j_quadratic_inventory', base/'frontier/source_barrier_saturation.py').Experiment(base)
    require(all(pins.get(path) == pin for path,pin in engine.pins.items()), 'Original source-bound cost inventory')
    tags = [row['tag'] for row in engine.specs+engine.quadratic_specs]+[('s',F(81,n*n)) for n in range(1,7)]
    require(encode(tags) == prior['original_cost_tags'] and len(tags) == 52, 'Unchanged original52 labels')
    quadratic = module('j_quadratic_identity', base/'frontier/whole_quadratic_same_head.py')
    problem = JointQuadraticJHead(base, moments, joint, bank, proposer)
    previous = {row['name']:F(row['upper']) for row in prior['results']}
    rows = []
    expected = {47:{4:F(19,4),5:F(17,4)},48:{3:F(7),4:F(2)}}
    for index in (47,48):
        expansion = quadratic.quadratic_expansion(engine.source,tags[index])
        require(not expansion['negative_hinge_coefficients'] and expansion['factorial_tail_coefficient'] == 2
                and {t:v for t,v in expansion['hinge_coefficients'].items() if v} == expected[index],
                'Exact original all-integer positive hinge and complete factorial identity')
        scan = problem.scan(index, expansion)
        outside = expansion['at_one']*F(3,20)+scan['complete_pair_tail_charge']
        upper = scan['joint_head_upper']+outside
        old = previous['cost-'+str(index)]
        require(0<upper<old,'Strict improvement over the complete current246 cost for each independent original test')
        rows.append({'index':index,'tag':tags[index],'expansion':expansion,'scan':scan,
                     'constant_mass_and_complete_pair_tail':outside,'cost_upper':upper,
                     'previous_cost_upper':old,'cost_improvement':old-upper})
        print('Complete J quadratic '+str(index)+' <= '+str(float(upper)),flush=True)
    require(problem.used == set(problem.bank),'Every retained dual is used and no necessary dual is missing')
    return encode({'schema':'erdos7-j-face-joint-quadratic-heads-v1','source_sha256':pins,
        'geometry':moments['geometry'],'survivor_mass':F(3,20),'model':problem.source.specification,
        'original_cost_indices':[47,48],'quadratic_results':rows,
        'uniform_raw_square9_upper':rows[1]['cost_upper'],
        'complete_tail_distinct_pairs':problem.pair_tail,
        'factorial_head_components_sha256':problem.head_digest,
        'rational_duals':{key:problem.bank[key] for key in sorted(problem.used)},
        'distinct_dual_count':len(problem.used),'rational_column_checks':876*len(problem.used),
        'total_containing_choices':sum(row['scan']['covered_containing_choices'] for row in rows),
        'scope':'Complete original costs47/48 on both entire saturated actual J faces, each with its own independent test. One common876-variable244 source/survivor/deletion LP carries both its retained hinges and the actual Phi5(B) head. The complete241 factorial crosses use an affine upper secant in the same normalized late coordinate; every omitted distinct pair remains in5089/7200. All6250000 containing choices per target use exact whole-theta old-bound pruning and feasible rational duals, retaining all876 columns. Current246 bounds are used only to measure strict same-domain improvement. No identification of independent cost loads, actual LP attainment, off-face/global52-cost comparison, Lean or unrestricted Erdos7 result is asserted.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    require(sha256((args.base/'certificate_io.py').read_bytes()).hexdigest()==PINS['certificate_io.py'],'Pinned certificate IO')
    io = module('j_quadratic_check_io',args.base/'certificate_io.py')
    stored = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=unique)
    require(calculate(args.base,bank=stored['rational_duals'])==stored,'Every exact J quadratic certificate field recomputes')
    print('PASS:two complete original J quadratic costs and all same-source duals and tails.',flush=True)


if __name__=='__main__':
    try:
        main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError) as error:
        print('FAIL: '+str(error),file=sys.stderr)
        raise SystemExit(1)
