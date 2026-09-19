#!/usr/bin/env python3
"""Signed face-dual transport for the actual finite same-test source.

The ordinary theorem is profile116. Infinite remainders and saturation-only
mean deletions are explicit external inputs, never inferred from this LP.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/finite_source_face_transport.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'verify_joint_frontier.py': '85341d7f8fa2d0b109697bc17b005a7e75f7f6ec412fd2eb3d26383cf9fce24f',
    'frontier/endpoint-bounds/broad_weighted_identity_source.py': 'ac969b33f833eb1cea191bdb74434ad6199077cfed1e551f0c5e0e7f286d3df1',
    'frontier/endpoint-bounds/k_face_common_seven_hinges.py': '3128cab9f43ad9c89a5f129b7c7d0115a6f73684f613111a07a56f0bd71ddcdd',
}
ROOT = (0, 0, 1, 1, 1)
GROUPS = (tuple(range(5)), tuple(range(5, 10)), tuple(range(10, 25)))
ORDER = ((0, 2), (3, 0), (1, 2), (4, 0))
CARRIERS = tuple(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input '+str(path))
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


def rational(value):
    require(isinstance(value, (int, F)) and not isinstance(value, bool), 'Exact rational input')
    return F(value)


def source_point(parameter, pi, r, first_beta, r1=None):
    """Necessary actual-source constraints; passing is not realizability."""
    require(len(parameter) == 5 and [len(v) for v in parameter[:4]] == [5, 2, 5, 5],
            'Complete deficit, alpha, beta and late source coordinates')
    deficit, alpha, beta, late = tuple(tuple(map(rational, v)) for v in parameter[:4])
    z, r = rational(parameter[4]), rational(r)
    require(all(v >= 0 for v in deficit+alpha+beta+late)
            and sum(deficit) <= F(1, 2) and sum(alpha) <= F(1, 4)
            and sum(beta) <= F(1, 4) and sum(late) <= F(1, 72)
            and F(3, 4) <= z <= 1, 'Actual source budget domain')
    pi = tuple(map(rational, pi))
    require(len(pi) == 18 and min(pi) >= 0 and sum(pi) == 1, 'One actual common carrier law')
    require(first_beta in (2, 3, 4), 'First beta label is in root1')
    eta = tuple((1-v)/9 for v in deficit)
    d = tuple(z-alpha[ROOT[c]]-beta[c] for c in range(5))
    n = tuple(eta[c]*d[c]-late[c] for c in range(5))
    h, h1 = sum(eta), sum(eta[2:])
    h0 = h-h1
    if r1 is not None:
        r1 = rational(r1)
        require(0 <= r1 <= r, 'Actual root1 share of the best-slot loss')
    p, a, b = z-F(3, 4), F(1, 4)-alpha[1], F(1, 4)-sum(beta[2:])
    Delta = p+a+b
    require(0 <= Delta <= F(1, 18), 'Broad source slab')
    require(0 <= r < min(h/5, h1/5, min(eta[2:])/5), 'Actual distinct best-slot packing guard')
    pre, descendant = [], []
    for c, j in product(range(5), repeat=2):
        excluded = j == 0 or (j == 1 and c >= 2) or (j == 2 and c == first_beta)
        cap = F(0) if excluded else F(1, 5)
        if j == 3:
            root0_loss = r/h if r1 is None else min(r/h, r1/h1, (r-r1)/h0)
            root1_loss = r/h1 if r1 is None else r1/h1
            cap = min(cap, F(3, 20)+Delta+root0_loss if c < 2 else F(1, 10)+Delta+root1_loss)
        pre.append(cap)
        descendant.append(F(0) if excluded else eta[c])
    caps = tuple(eta[c]*pre[5*c+j] for c, j in product(range(5), repeat=2))
    require(all(eta[c]/5-r <= n[c] <= sum(caps[5*c:5*c+5]) for c in range(5))
            and sum(n) >= h/5-r, 'Necessary actual raw matrix row and best-slot feasibility')
    score = tuple(sum(v*(int(ROOT[c] == u)+int(c == l)) for v, (u, l) in zip(pi, CARRIERS))
                  for c in range(5))
    budgets = tuple(sum(n[c] for c in sorted({i//5 for i in group})) for group in GROUPS)
    return {'eta': eta, 'd': d, 'n': n, 's': sum(n), 'p': p, 'a': a, 'b': b,
            'Delta': Delta, 'r': r, 'r1': r1, 'first_beta': first_beta, 'score': score,
            'pre': tuple(pre), 'caps': caps, 'descendant': tuple(descendant), 'budgets': budgets}


def defect_vertices(g5, g15, e):
    """All vertices of 0<=q5,q15<=1/5, g5*q5+g15*q15<=e."""
    g5, g15, e = map(rational, (g5, g15, e))
    require(g5 > 0 and g15 > 0 and e >= 0, 'Positive shared defect prices and nonnegative budget')
    edges = ((F(1), F(0), F(0)), (F(1), F(0), F(1, 5)),
             (F(0), F(1), F(0)), (F(0), F(1), F(1, 5)), (g5, g15, e))
    found = set()
    for (a, b, c), (d, f, h) in combinations(edges, 2):
        determinant = a*f-b*d
        if determinant:
            x, y = (c*f-b*h)/determinant, (a*h-c*d)/determinant
            if 0 <= x <= F(1, 5) and 0 <= y <= F(1, 5) and g5*x+g15*y <= e:
                found.add((x, y))
    require(found, 'Nonempty shared defect polygon, including the zero-budget degeneration')
    return tuple(sorted(found))


def weights(point, q):
    q5, q15 = map(rational, q)
    require(0 <= q5 <= F(1, 5) and 0 <= q15 <= F(1, 5), 'Complete wrong or absent seven weights')
    w = tuple(1-point['score'][c]/5-(F(1, 5)-q5)*int(j == 4)
              -(F(1, 5)-q15)*int(c >= 2 and j == 4) for c, j in product(range(5), repeat=2))
    require(min(w) >= F(1, 5) and max(w) <= 1, 'Retained density range')
    return w


def prepare(coefficients):
    coefficients = {int(t): rational(v) for t, v in coefficients.items() if v}
    require(coefficients and all(1 <= t <= 8 and v > 0 for t, v in coefficients.items()),
            'Nonzero nonnegative combination including the optional mean threshold1')
    prefix = {t: min(t-1, 4) for t in coefficients}
    M = sum(v*max(6+prefix[t]-t, 0) for t, v in coefficients.items())
    return {'coefficients': coefficients, 'prefix': prefix, 'M': M,
            'highest': max(prefix.values())}


def seven_increment(t, value, extra):
    k = max(t-value, 0)
    return F(1, 5*7**max(k-extra, 0))+F(6, 35)*max(extra-k, 0)


def finite_coefficients(record, point, q, layout, positive7):
    require(len(layout) == 7 and layout[0] in (0, 1) and layout[3] in (0, 1)
            and all(layout[i] in range(5) for i in (1, 2, 4, 5, 6)), 'Original six-label head layout')
    T, slot = positive7
    require(T in (0, 1) and slot in range(5), 'Original shallow positive-seven layout')
    r3, c9, s5, r15, s15, c45, s45 = layout
    B = tuple(1+int(ROOT[c] == r3)+int(c == c9)+int(j == s5)
              +int(ROOT[c] == r15 and j == s15)+int(c == c45 and j == s45)
              for c, j in product(range(5), repeat=2))
    w = weights(point, q)
    extra = tuple(int(ROOT[c] == T)+int(j == slot) for c, j in product(range(5), repeat=2))
    def value(t, i, v):
        return w[i]*max(v-t, 0)+seven_increment(t, v, extra[i])
    head = tuple(sum(a*value(t, i, B[i]) for t, a in record['coefficients'].items()) for i in range(25))
    increments = tuple(tuple(sum(a*(value(t, i, B[i]+k)-value(t, i, B[i]+k-1))
                                 for t, a in record['coefficients'].items() if record['prefix'][t] >= k)
                             for i in range(25)) for k in range(1, record['highest']+1))
    require(all(v >= 0 for values in (head,)+increments for v in values), 'Nonnegative finite head and selected costs')
    return head, increments


def selected_values(point, coefficients, label):
    """The complete finite maximum for this one original selected cylinder."""
    a, b = label
    if b == 0:
        require(a in (3, 4), 'Selected pure3 original label')
        return tuple(sum(point['pre'][5*c+j]*coefficients[5*c+j] for j in range(5))/3**a for c in range(5))
    require(b == 2 and a in (0, 1), 'Selected descendant-five original label')
    roots = (None,) if a == 0 else (0, 1)
    return tuple(sum(point['descendant'][5*c+j]*coefficients[5*c+j]
                     for c in range(5) if root is None or ROOT[c] == root)/25
                 for root, j in product(roots, range(5)))


def branch(capacity_module, record, point, q, layout, positive7):
    head, increments = finite_coefficients(record, point, q, layout, positive7)
    lp, gammas = F(0), []
    for indices, budget in zip(GROUPS, point['budgets']):
        value, gamma = capacity_module.capacity_dual(head, point['caps'], budget, indices)
        lp += value
        gammas.append(gamma)
    selected = tuple(max(selected_values(point, z, label)) for z, label in zip(increments, ORDER))
    return {'value': lp+sum(selected), 'head': head, 'increments': increments,
            'lp': lp, 'gammas': tuple(gammas), 'selected': selected}


def signed_transport(record, point, q, layout, positive7, anchor_point, anchor):
    """Use this branch's own optimal face dual, without preserving its active set."""
    head, increments = finite_coefficients(record, point, q, layout, positive7)
    head_change = F(0)
    for indices, budget, old_budget, gamma in zip(GROUPS, point['budgets'], anchor_point['budgets'], anchor['gammas']):
        head_change += gamma*(budget-old_budget)
        head_change += sum(point['caps'][i]*max(head[i]-gamma, 0)
                           -anchor_point['caps'][i]*max(anchor['head'][i]-gamma, 0) for i in indices)
    selected_change = tuple(max(selected_values(point, z, label))-old
                            for z, label, old in zip(increments, ORDER, anchor['selected']))
    change = head_change+sum(selected_change)
    return {'upper': anchor['value']+change, 'signed_change': change,
            'head_change': head_change, 'selected_change': selected_change}


def preserve_slack(face_upper, anchors_and_changes):
    """The supplied records must cover the desired branch inventory."""
    face_upper = rational(face_upper)
    records = tuple(anchors_and_changes)
    require(records and all(anchor <= face_upper for anchor, _ in records), 'Certified common face upper')
    corrected = max(change-(face_upper-anchor) for anchor, change in records)
    upper = face_upper+corrected
    require(upper == max(anchor+change for anchor, change in records), 'Same-branch face slack is retained exactly')
    return upper


def assemble_complete_branch(record, finite_upper, tail_upper, mean_deletion_lower,
                             omega, at_one=F(0), survivor_mass=F(0)):
    """Conditional numerical interface: the caller proves each tail/deletion input.

    tail_upper includes all complete omitted old/positive-seven contributions
    and any additional nonnegative error they require. The bounded old head
    alone pays M*omega here. at_one is multiplied by the actual mass S.
    """
    finite_upper, tail_upper, mean_deletion_lower, omega, at_one, survivor_mass = map(
        rational, (finite_upper, tail_upper, mean_deletion_lower, omega, at_one, survivor_mass))
    require(tail_upper >= 0 and mean_deletion_lower >= 0 and omega >= 0 and survivor_mass >= 0,
            'Nonnegative supplied complete remainder, deletion lower, defect mass and surviving mass')
    return (at_one*survivor_mass+finite_upper+tail_upper+record['M']*omega
            -record['coefficients'].get(1, F(0))*mean_deletion_lower)


def shared_vertex_upper(costs, g5, g15, e, evaluate):
    """Finite objectives only. evaluate(record,q) must be convex in q.

    A complete finite maximum, or the fixed-face-dual upper above, satisfies
    that contract. Unknown tail functions do not satisfy it by declaration.
    """
    g5, g15, e = map(rational, (g5, g15, e))
    costs = tuple((rational(weight), record) for weight, record in costs)
    require(costs and all(weight >= 0 for weight, _ in costs), 'One nonnegative cost vector')
    M = sum(weight*record['M'] for weight, record in costs)
    values = []
    for q in defect_vertices(g5, g15, e):
        omega = e-g5*q[0]-g15*q[1]
        value = sum(weight*evaluate(record, q) for weight, record in costs)+M*omega
        values.append({'q5': q[0], 'q15': q[1], 'omega_upper': omega, 'value': value})
    return {'upper': max(row['value'] for row in values), 'bounded_transfer_coefficient': M, 'vertices': values}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('finite_transport_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(pin is not None and sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned dependency '+path)
    old = module('finite_transport_capacity', base/'frontier/endpoint-bounds/broad_weighted_identity_source.py')
    source = module('finite_transport_source', base/'verify_joint_frontier.py')
    face = module('finite_transport_face', base/'frontier/endpoint-bounds/k_face_common_seven_hinges.py')
    pi = tuple(F(int(c == (1, 1))) for c in CARRIERS)
    parameter = ((F(1, 2), F(0), F(0), F(0), F(0)), (F(0), F(1, 4)),
                 (F(0), F(0), F(1, 4), F(0), F(0)), (F(1, 72), F(0), F(0), F(0), F(0)), F(3, 4))
    anchor_point = source_point(parameter, pi, F(0), 2)
    pre, caps, w, descendant = face.source_tables(2)
    for name, expected in (('pre', pre), ('caps', caps), ('descendant', descendant)):
        require(anchor_point[name] == tuple(v for row in expected for v in row), 'Exact existing whole-face '+name)
    require(weights(anchor_point, (F(0), F(0))) == tuple(v for row in w for v in row)
            and anchor_point['budgets'] == face.GROUP_MASSES, 'Exact whole-face objective and group budgets')
    points = [anchor_point]
    for p, r in ((F(1, 1000), F(1, 24000)), (F(1, 500), F(1, 520))):
        par = parameter[:4]+(F(3, 4)+p,)
        point = source_point(par, pi, r, 2)
        dat = source.data(par)
        require((point['d'], point['n'], point['eta'], point['s']) == dat[:4], 'Reuse actual source definitions')
        if r < F(1, 12000):
            previous = old.source_tables(par, dat, old.carrier_score(pi), r, 2)
            require(point['caps'] == previous['capacities'] and point['pre'] == previous['pre_coefficients'], 'Exact88 small-r table')
        points.append(point)
    tight_point = source_point(parameter[:4]+(F(3, 4)+F(1, 500),), pi, F(1, 520), 2, r1=F(1, 1040))
    require(all(a <= b for a, b in zip(tight_point['caps'], points[-1]['caps']))
            and tight_point['caps'] != points[-1]['caps'], 'Actual root loss tightens both root caps')
    points.append(tight_point)
    layouts = (((0, 1, 2, 1, 2, 3, 2), (1, 4)), ((1, 1, 2, 1, 2, 3, 2), (1, 4)),
               ((0, 1, 2, 0, 2, 1, 1), (0, 2)), ((1, 4, 4, 0, 3, 2, 4), (1, 0)))
    records = [prepare({1: F(1)}), prepare({4: F(3), 5: F(2)}),
               prepare({1: F(7, 3), 2: F(1, 2), 5: F(4), 8: F(2, 7)})]
    g5, g15, e = F(1, 50), F(397, 36000), F(1, 300)
    vertices = defect_vertices(g5, g15, e)
    require(defect_vertices(g5, g15, F(0)) == ((F(0), F(0)),), 'Zero defect has one vertex')
    require(len(defect_vertices(g5, g15, (g5+g15)/5)) == 4, 'Saturated budget is the full box')
    checks, tight, digest = 0, 0, sha256()
    for ri, record in enumerate(records):
        for layout, positive7 in layouts:
            anchor = branch(old, record, anchor_point, (F(0), F(0)), layout, positive7)
            for pi_index, point in enumerate(points):
                for q in ((F(0), F(0)),)+vertices:
                    actual = branch(old, record, point, q, layout, positive7)
                    transported = signed_transport(record, point, q, layout, positive7, anchor_point, anchor)
                    require(actual['value'] <= transported['upper'], 'Face dual controls the actual LP with signed changes')
                    if point is anchor_point and q == (F(0), F(0)):
                        require(transported['signed_change'] == 0 and actual['value'] == anchor['value'], 'Exact face recovery')
                    checks += 1
                    tight += actual['value'] == transported['upper']
                    digest.update(json.dumps(encode([ri, layout, positive7, pi_index, q, actual['value'], transported]), separators=(',', ':')).encode())
    costs = ((F(2, 3), records[0]), (F(1, 4), records[1]), (F(3, 7), records[2]))
    def evaluate(record, q):
        return max(branch(old, record, points[1], q, layout, positive7)['value'] for layout, positive7 in layouts)
    vector = shared_vertex_upper(costs, g5, g15, e, evaluate)
    # Interior exact points check the implemented joint formula, not continuum validity.
    convex_checks = 0
    for u, v in combinations(vertices, 2):
        q = tuple((x+y)/2 for x, y in zip(u, v))
        value = sum(weight*evaluate(record, q) for weight, record in costs)
        value += vector['bounded_transfer_coefficient']*(e-g5*q[0]-g15*q[1])
        require(value <= vector['upper'], 'Joint midpoint is below the shared vertex upper')
        convex_checks += 1
    # g can have negative signed movement; never replace changes by absolute values.
    require(preserve_slack(F(10), ((F(10), F(-2)), (F(8), F(1)))) == 9, 'Retained slack blocks an inactive-branch overcharge')
    convexity_checks = 0
    for t, extra, w0 in product(range(1, 9), range(3), (F(1, 5), F(1))):
        values = [w0*max(v-t, 0)+seven_increment(t, v, extra) for v in range(13)]
        require(all(seven_increment(t, v, extra) == face.seven_increment(t, v, extra) for v in range(13)),
                'Exact existing positive-seven increment')
        require(all(values[i+1] >= values[i] for i in range(12))
                and all(values[i+2]-2*values[i+1]+values[i] >= 0 for i in range(11)), 'Increasing integer-convex mixed finite cost')
        convexity_checks += 1
    return encode({'schema': 'erdos7-finite-source-face-transport-v1', 'source_sha256': PINS,
                   'scope': 'Ordinary general finite-source theorem with exact interface regression checks. The four regression branches are not an exhaustive 125000-branch maximum. No global K or Lean claim.',
                   'original_head_labels': [1, 3, 9, 5, 15, 45], 'selected_original_labels': [25, 27, 75, 81],
                   'source_points': points, 'face_dual_checks': checks, 'tight_dual_checks': tight,
                   'all_checked_branches_sha256': digest.hexdigest(), 'convexity_checks': convexity_checks,
                   'shared_vertex_regression': vector, 'midpoint_checks': convex_checks,
                   'external_inputs': ['complete omitted old and positive-seven remainder bounds',
                                       'actual mean-head deletion lower bound when retaining109 correction',
                                       'actual surviving mass S for the constant cost term',
                                       'independent tail-error theorem; arbitrary nonlinear errors are not covered by polygon convexity']})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('finite_transport_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact semantic finite-source certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: signed face duals, same-branch slack, actual source domain and shared finite defect polygon; infinite-tail inputs remain explicit.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
