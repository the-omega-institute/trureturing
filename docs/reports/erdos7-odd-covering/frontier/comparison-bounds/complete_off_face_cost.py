#!/usr/bin/env python3
"""Exact integer evaluation of complete off-face common-head cost bounds."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = (0, 0, 1, 1, 1)
GROUPS = (tuple(range(5)), tuple(range(5, 10)), tuple(range(10, 25)))
ORDER = ((0, 2), (3, 0), (1, 2), (4, 0))
CERTIFICATE = 'certificates/source_norms/comparison-bounds/complete_off_face_cost.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/retained-transport/finite_source_face_transport.py': '04c99f1a0c6e1781734531923705863fbc9843c610f6d4933a81c89429aa5291',
    'frontier/retained-transport/joint_deep_mean_transport.py': 'efbb0825f227e5cc97a0fc24b71acf3e16a35f6b3db662f0e4b392afb8e3d0d0',
    'frontier/cover-geometry/complete_off_face_omitted_tails.py': '33e8c164c64790483ba512c984e8090cf5c44b92bf6ca1cb08a17cb56a93201d',
    'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765',
    'frontier/endpoint-bounds/broad_weighted_identity_source.py': 'bfc5f98109c02b318ee3e92c0951d1d33ded45971d6718623d4c60629dc2e6e6',
    'certificates/source_norms/comparison-bounds/whole_cost_mean_stop_loss.json': 'cb1decc204e827ab7ca7fd3f199364b44010e219cdc63f69d960a36520d66cf6',
    'frontier/source-budgets/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable exact input')
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


class IntegerHead:
    """Same116 finite operator, with exact common integer denominators."""
    def __init__(self, finite, record, point, q):
        self.record, self.point, self.q = record, point, q
        weights = finite.weights(point, q)
        costs, selected = {}, {}
        for i, m, v in product(range(25), range(3), range(1, 7)):
            def term(t, value):
                return weights[i]*max(value-t, 0)+finite.seven_increment(t, value, m)
            costs[i, m, v] = sum(a*term(t, v) for t, a in record['coefficients'].items())
            for k in range(1, record['highest']+1):
                selected[k, i, m, v] = sum(a*(term(t, v+k)-term(t, v+k-1))
                    for t, a in record['coefficients'].items() if record['prefix'][t] >= k)
        scale = lcm(*(v.denominator for v in tuple(costs.values())+tuple(selected.values())))
        require(all(v >= 0 for v in tuple(costs.values())+tuple(selected.values())), 'Nonnegative complete finite coefficients')
        self.cost_scale = scale
        self.head = {key: int(scale*v) for key, v in costs.items()}
        self.inc = {key: int(scale*v) for key, v in selected.items()}
        operators = []
        for a, b in ORDER[:record['highest']]:
            if b == 0:
                operators.append(tuple(tuple((5*c+j, point['pre'][5*c+j]/3**a) for j in range(5)) for c in range(5)))
            else:
                roots = (None,) if a == 0 else (0, 1)
                operators.append(tuple(tuple((5*c+j, point['descendant'][5*c+j]/25) for c in range(5)
                                             if r is None or ROOT[c] == r)
                                       for r, j in product(roots, range(5))))
        values = tuple(point['caps'])+tuple(point['budgets'])+tuple(v for choices in operators for row in choices for _, v in row)
        self.mass_scale = lcm(*(v.denominator for v in values))
        self.caps = tuple(int(self.mass_scale*v) for v in point['caps'])
        self.budgets = tuple(int(self.mass_scale*v) for v in point['budgets'])
        self.operators = tuple(tuple(tuple((i, int(self.mass_scale*v)) for i, v in row) for row in choices) for choices in operators)
        self.scale = self.mass_scale*self.cost_scale
        self.positive7 = tuple((r, j, tuple(int(ROOT[c] == r)+int(s == j) for c, s in product(range(5), repeat=2)))
                               for r, j in product(range(2), range(5)))

    def capacity(self, head, indices, budget):
        remaining, value, gamma = budget, 0, 0
        for i in sorted(indices, key=lambda i: head[i], reverse=True):
            amount = min(remaining, self.caps[i])
            value += head[i]*amount
            remaining -= amount
            if remaining == 0:
                gamma = head[i]
                break
        dual = gamma*budget+sum(self.caps[i]*max(head[i]-gamma, 0) for i in indices)
        require(value == dual and remaining >= 0, 'Exact feasible integer fill and matching capacity dual')
        return value

    def load(self, layout):
        r3, c9, s5, r15, s15, c45, s45 = layout
        return tuple(1+int(ROOT[c] == r3)+int(c == c9)+int(j == s5)
                     +int(ROOT[c] == r15 and j == s15)+int(c == c45 and j == s45)
                     for c, j in product(range(5), repeat=2))

    def branch(self, B, extra):
        head = tuple(self.head[i, extra[i], B[i]] for i in range(25))
        value = sum(self.capacity(head, indices, budget) for indices, budget in zip(GROUPS, self.budgets))
        for k, choices in enumerate(self.operators, 1):
            z = tuple(self.inc[k, i, extra[i], B[i]] for i in range(25))
            value += max(sum(weight*z[i] for i, weight in row) for row in choices)
        return value


def actual_398_case(finite, source, height):
    require(height >= 5, 'Concentrated genuine original family')
    t = sum((F(1, 3**a) for a in range(3, height+1)), F(0))
    q = sum((F(1, 5**b) for b in range(1, height+1)), F(0))
    parameter = ((9*t, F(0), F(0), F(0), F(0)), (F(0), q),
                 (F(0), F(0), q, F(0), F(0)), (t*q, F(0), F(0), F(0), F(0)), 1-q)
    v7 = F(1, 7**height)
    p, u, actual7 = 1-v7, (1-v7)/5, (1-v7)/(5+v7)
    pi = tuple(p if carrier == (1, 1) else v7 if carrier == (-1, -1) else F(0) for carrier in finite.CARRIERS)
    dat = source.data(parameter)
    d, n, eta, s, _ = dat
    h, h1, D = sum(eta), sum(eta[2:]), max(d)
    old_union_sum = F(4, 9)+t+q/9-t*q
    delta, omega = actual7*old_union_sum, (u-actual7)*old_union_sum
    T = (p*(sum(n[2:])+n[1])+D/18+(h+h1+max(eta))/4+F(1, 72))/5
    defects = {'E5': h/25-u*h/5, 'E15': h1/25-u*h1/5,
               'E3': D/90-u*D*t, 'E5d': h/100-u*h*(q-F(1, 5)),
               'E15d': h1/100-u*h1*(q-F(1, 5)), 'omega': omega, 'rho': T-delta}
    E27 = D/135-u*D/27
    require(min(defects.values()) >= 0 and E27 >= 0 and E27 <= defects['E3'], 'Actual complete defects and one union error')
    require(sum(defects[k] for k in ('E5', 'E15', 'E3', 'E5d', 'E15d', 'omega')) <= defects['rho'], 'One complete family budget')
    return {'height': height, 'parameter': parameter, 'pi': pi, 'dat': dat,
            'point': finite.source_point(parameter, pi, F(0), 2, F(0)), 'q': (v7/5, v7/5),
            'sigma': 1-(18*t)**2*(4*q)**4*p, 'qslots': (F(0), F(1, 5), F(1, 5), F(1, 5)-(q-F(1, 5)), F(1, 5)),
            'E27': E27, 'defects': defects, 'survivor_mass': s-delta}


def face_case(finite, source):
    parameter = ((F(1, 2), F(0), F(0), F(0), F(0)), (F(0), F(1, 4)),
                 (F(0), F(0), F(1, 4), F(0), F(0)), (F(1, 72), F(0), F(0), F(0), F(0)), F(3, 4))
    pi = tuple(F(int(carrier == (1, 1))) for carrier in finite.CARRIERS)
    defects = dict.fromkeys(('E5', 'E15', 'E3', 'E5d', 'E15d', 'omega', 'rho'), F(0))
    return {'height': None, 'parameter': parameter, 'pi': pi, 'dat': source.data(parameter),
            'point': finite.source_point(parameter, pi, F(0), 2, F(0)), 'q': (F(0), F(0)),
            'sigma': F(0), 'qslots': (F(0), F(1, 5), F(1, 5), F(3, 20), F(1, 5)),
            'E27': F(0), 'defects': defects, 'survivor_mass': F(53, 360)}


def complete_cost(finite, mean, tails, case, row):
    record = finite.prepare({int(t): F(a) for t, a in row['objective']['coefficients'].items()})
    compiler = IntegerHead(finite, record, case['point'], case['q'])
    tail = tails.complete_tails(case['dat'], case['pi'], case['defects'], case['parameter'][4])
    tail_cost = sum(a*(tail['old_remainders'][record['prefix'][t]]+tail['positive7'])
                    for t, a in record['coefficients'].items())
    d, _, eta, _, _ = case['dat']
    a1 = record['coefficients'].get(1, F(0))
    defects = case['defects']
    defect_parts = (case['E27'], defects['E3']-case['E27'], defects['E5d'], defects['E15d'])
    best_num, best_den, witness, ties, count = None, None, None, 0, 0
    digest = sha256()
    for layout in mean.layouts():
        data = mean.mean_data(case['sigma'], max(d), max(d[2:]), case['parameter'][4], eta, case['qslots'], layout)
        credit = mean.mean_credit(data, *defect_parts)['nonnegative_credit']
        payment = a1*credit
        B = compiler.load(layout)
        for r, j, extra in compiler.positive7:
            value = compiler.branch(B, extra)
            num, den = value*payment.denominator-payment.numerator*compiler.scale, compiler.scale*payment.denominator
            digest.update((str(num)+'/'+str(den)+';').encode())
            delta = 1 if best_num is None else num*best_den-best_num*den
            if delta > 0:
                best_num, best_den = num, den
                witness = {'layout': layout, 'positive7_root': r, 'positive7_slot': j,
                           'finite_upper': F(value, compiler.scale), 'mean_credit': credit,
                           'mean_data': data}
                ties = 1
            elif delta == 0:
                ties += 1
            count += 1
    require(count == 125000, 'Every original head and independent positive-seven projection is included')
    finite_corrected = F(best_num, best_den)
    # The109 record stores f(1)*D_face, not f(1) itself.
    at_one = F(row['constant_mass_term'])/F(53, 360)
    mass_term = at_one*case['survivor_mass']
    total = mass_term+finite_corrected+tail_cost+record['M']*defects['omega']
    require(witness['finite_upper']-a1*witness['mean_credit'] == finite_corrected, 'Same maximizing original branch')
    return {'cost_index': row['index'], 'cost_name': row['name'], 'cost_tuple': row['tuple'],
            'source_height': case['height'], 'sigma': case['sigma'], 'survivor_mass': case['survivor_mass'],
            'original_head_checks': count, 'integer_cost_scale': compiler.cost_scale,
            'integer_mass_scale': compiler.mass_scale, 'all_joint_objectives_sha256': digest.hexdigest(),
            'complete_tail_data': tail, 'complete_weighted_tail': tail_cost,
            'capacity_defects': defects, 'E27': case['E27'],
            'finite_corrected_upper': finite_corrected, 'single_bounded_error_price': record['M'],
            'single_bounded_error_cost': record['M']*defects['omega'], 'constant_mass_term': mass_term,
            'complete_cost_upper': total, 'maximizer_count': ties, 'maximizing_witness': witness}


def calculate(base):
    io = module('off_cost_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    finite = module('off_cost_finite', base/'frontier/retained-transport/finite_source_face_transport.py')
    mean = module('off_cost_mean', base/'frontier/retained-transport/joint_deep_mean_transport.py')
    tails = module('off_cost_tails', base/'frontier/cover-geometry/complete_off_face_omitted_tails.py')
    source = module('off_cost_source', base/'verify_joint_frontier.py')
    capacity = module('off_cost_capacity', base/'frontier/endpoint-bounds/broad_weighted_identity_source.py')
    old = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/whole_cost_mean_stop_loss.json'))
    row = old['cost_results'][1]
    require(row['index'] == 1 and row['name'] == 'R17' and row['tuple'] == [0, 1], 'Original complete AP cost, not a synthetic load')
    cases = [face_case(finite, source)]+[actual_398_case(finite, source, height) for height in (5, 8)]
    # Check the integer implementation against the existing rational dual solver.
    compiled_checks = 0
    for case in cases:
        record = finite.prepare({int(t): F(a) for t, a in row['objective']['coefficients'].items()})
        compiler = IntegerHead(finite, record, case['point'], case['q'])
        for layout in ((0, 1, 2, 0, 2, 1, 2), (1, 0, 0, 0, 0, 1, 1),
                       (1, 3, 4, 1, 2, 0, 3), (0, 2, 1, 1, 4, 4, 1)):
            B = compiler.load(layout)
            for r, j, extra in compiler.positive7:
                observed = F(compiler.branch(B, extra), compiler.scale)
                expected = finite.branch(capacity, record, case['point'], case['q'], layout, (r, j))['value']
                require(observed == expected, 'Exact independent rational/integer source operator agreement')
                compiled_checks += 1
    require(old['cost_results'][40]['name'] == 'linear'
            and F(old['cost_results'][40]['constant_mass_term'])/F(old['mass']) == 1,
            'The original linear cost has nonzero f(1)=1 after undoing the face mass')
    constant_regression = [{'source_height': case['height'], 'survivor_mass': case['survivor_mass'],
                            'linear_constant_mass_term': F(old['cost_results'][40]['constant_mass_term'])
                            /F(old['mass'])*case['survivor_mass']} for case in cases]
    require(all(r['linear_constant_mass_term'] == r['survivor_mass'] for r in constant_regression),
            'An actual-source constant multiplies S once, never D_face*S')
    results = []
    for case in cases:
        result = complete_cost(finite, mean, tails, case, row)
        if case['height'] is None:
            require(result['complete_cost_upper'] == F(row['uniform_cost_upper']), 'Exact existing whole-face cost recovered')
        results.append(result)
        print('Checked complete cost at height '+str(case['height'])+': '+str(result['complete_cost_upper']), flush=True)
    return {'schema': 'erdos7-complete-off-face-cost-v1', 'source_sha256': PINS,
            'independent_compiled_checks': compiled_checks, 'nonzero_constant_regression': constant_regression,
            'cost_results': results,
            'scope': 'General complete same-head off-face cost interface with full omitted tails and one actual capacity/union-error vector. Numeric instances cover the whole-face reference and two genuine finite398 source families for original AP cost1. No uniform maximization over all sources, new global K, Lean verification or Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(sha256((args.base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('off_cost_writer', args.base/'certificate_io.py')
    result = encode(calculate(args.base))
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical complete off-face cost result')
    print('PASS: one complete original AP cost on three source cases,375000 original branches and120 rational/integer comparisons.')
    print('All tails retained; no numerical extrapolation to other sources or a global K bound.')


if __name__ == '__main__':
    main()
