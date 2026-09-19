#!/usr/bin/env python3
"""One complete deep-pure3 defect controls the root0 projection spill.

The ordinary continuum theorem is profile120. Actual finite source cases
check its measure identity and three transported mean-head indicators.
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
CERTIFICATE = 'certificates/source_norms/cover-geometry/pure_three_root_spill.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'verify_joint_frontier.py': '85341d7f8fa2d0b109697bc17b005a7e75f7f6ec412fd2eb3d26383cf9fce24f',
    'frontier/source-budgets/source_cost_endpoint_attainment.py': '860816267cfc11da898d207f1eb48486c6630d1dd3d00a785417a244188af47d',
    'frontier/source-budgets/sharp_source_mass_endpoints.py': '79bb947d96c36895069f58568d7a5de2c22aa561753f03352e9eb741313147d9',
    'frontier/endpoint-bounds/endpoint_linear_neighborhood.py': '1c8ccd9850a12019081181f53440606583bcd9781fd9949a30cd2d8e5a2503b3',
    'frontier/cover-geometry/pure_three_projected_defect.py': '9043b1e0d84cc09a2f5a1201423886ca22c71f1936a0663bd9074a1c2c8efdd9',
}


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


def spill_bounds(dmax, root1_max, z, E3):
    dmax, root1_max, z, E3 = map(rational, (dmax, root1_max, z, E3))
    gap = dmax-root1_max
    require(0 <= root1_max < dmax <= z <= 1 and 0 <= E3 <= dmax/90,
            'Positive source root gap and complete deep3 capacity defect')
    extra = (z-dmax)/90
    return {'gap': gap, 'global_projected_defect_mass': E3+extra,
            'root1_virtual_mass_upper': root1_max*E3/gap,
            'root0_projected_defect_mass_upper': dmax*E3/gap+extra,
            'extra': extra}


def partial_head_credit(dmax, root1_max, z, E3, q_slots, r3, s5, r15, s15):
    """Three of109's five pure3 terms; q_slots may be proved lower bounds."""
    bounds = spill_bounds(dmax, root1_max, z, E3)
    q_slots = tuple(map(rational, q_slots))
    require(len(q_slots) == 5 and all(0 <= v <= F(1, 5) for v in q_slots), 'Five actual pure5 slot masses or certified lowers')
    require(r3 in (0, 1) and r15 in (0, 1) and s5 in range(5) and s15 in range(5), 'Original test root and slots')
    I, J = int(r3 == 0), int(r15 == 0)
    Mxi, Mspill = I+1+J*int(s5 == s15), I+J
    reference = (I*z+q_slots[s5]+J*q_slots[s15])/90
    E3_price = Mxi+Mspill*root1_max/bounds['gap']
    error = E3_price*E3+Mxi*bounds['extra']
    return {'reference': reference, 'global_defect_multiplier': Mxi,
            'root_spill_multiplier': Mspill, 'E3_price': E3_price,
            'error_upper': error, 'credit_lower': max(F(0), reference-error)}


def canonical_slot_lowers(p, a, b, pure5_H_loss_upper):
    p, a, b, loss = map(rational, (p, a, b, pure5_H_loss_upper))
    require(min(p, a, b, loss) >= 0 and p+a+b <= F(1, 18) and p <= F(1, 20) and loss <= F(1, 5),
            'Actual broad slab and certified pure5 H loss')
    return (F(0), F(1, 5)-a, F(1, 5)-b, F(3, 20)+p, F(1, 5)-loss)


def finite_case(source, constructor, parent, tail, mode):
    height, A, B = 3, 27, 125
    labels = [constructor.source(a, b, 'off-diagonal')
              for a, b in product(range(height+1), repeat=2) if a+b]
    q = [F(int(not any(a == 0 and y % 5**b == rb for a, _, b, rb in labels)), B) for y in range(B)]
    old = [(x, y) for x, y in product(range(A), range(B))
           if not any(x % 3**a == ra and y % 5**b == rb for a, ra, b, rb in labels)]
    parameter = parent.parameter(height)
    d, n, eta, s, _ = source.data(parameter)
    dmax, root1_max, z = max(d), max(d[2:]), sum(q)
    require(s == F(len(old), A*B) and z == parameter[4], 'Inherited exact actual source')
    if mode == 'cell1-long':
        original = [(a, e, 3) for a, e in product(range(3, 9), range(1, 7))]
    else:
        residues = {'cell0': (0, 0, 0), 'cell1': (3, 3, 3), 'root1': (7, 7, 7),
                    'removed': (2, 2, 2), 'mixed': (0, 7, 2), 'absent': (None, None, None)}[mode]
        original = [(3, e, residue) for e, residue in enumerate(residues, 1)]
    v0, v1 = [F(0)]*B, [F(0)]*B
    finite_defects, depth_masses = [], {}
    old_set = set(old)
    for a, e, residue in original:
        u = F(6, 5*7**e)
        if a <= height:
            cylinder = [] if residue is None else [(x, y) for x, y in old if x % 3**a == residue]
            marginal = [F(sum(yy == y for _, yy in cylinder), A*B) for y in range(B)]
        else:
            require(residue % 9 == 3 and all(((x, y) in old_set) == bool(q[y])
                    for x in range(3, A, 9) for y in range(B)), 'Exact product source fiber permits genuine deeper cell1 cylinders')
            marginal = [v/3**a for v in q]
        mass = sum(marginal)
        defect = dmax/3**a-mass
        require(defect >= 0, 'Each present, removed-root or absent original label has nonnegative capacity defect')
        if residue is not None and residue % 3 == 1:
            require(mass <= root1_max/3**a and mass*(dmax-root1_max) <= root1_max*defect,
                    'Each actual root1 label pays its own spill')
        if residue is not None and residue % 3 in (0, 1):
            target = v0 if residue % 3 == 0 else v1
            for y in range(B):
                target[y] += u*marginal[y]
        else:
            require(mass == 0, 'Removed-root and absent labels have zero source measure')
        finite_defects.append(u*defect)
        depth_masses[a] = depth_masses.get(a, F(0))+u*mass
    v = [x+y for x, y in zip(v0, v1)]
    E3 = dmax/90-sum(v)
    missing_capacity = dmax*(F(1, 90)-sum(F(6, 5*7**e*3**a) for a, e, _ in original))
    require(E3 == sum(finite_defects)+missing_capacity, 'All absent exponent tails remain in the same complete E3')
    xi = [x/90-y for x, y in zip(q, v)]
    xi0 = [x/90-y for x, y in zip(q, v0)]
    bounds = spill_bounds(dmax, root1_max, z, E3)
    require(min(xi) >= 0 and all(x0 == x+y for x0, x, y in zip(xi0, xi, v1)), 'Positive root0 projection identity Xi0=Xi+spill')
    require(sum(xi) == bounds['global_projected_defect_mass']
            and sum(v1) <= bounds['root1_virtual_mass_upper']
            and sum(xi0) <= bounds['root0_projected_defect_mass_upper'], 'Complete actual root spill bounds')
    tail_upper, crossing = tail.min_geometric(bounds['root0_projected_defect_mass_upper'], F(1, 90), 5, 2)
    for pattern in range(3):
        observed = sum(sum(xi0[y] for y in range(B) if y % 5**b == (pattern*(b*b+3)+1) % 5**b)
                       for b in range(2, height+1))
        require(observed <= tail_upper, 'Independent finite descendants fit the complete dominated root-spill tail')
    slots = tuple(sum(q[y] for y in range(B) if y % 5 == j) for j in range(5))
    p, a, b = z-F(3, 4), F(1, 4)-parameter[1][1], F(1, 4)-sum(parameter[2][2:])
    canonical = canonical_slot_lowers(p, a, b, F(0))
    require(all(canonical[j] <= slots[actual] for j, actual in enumerate((1, 2, 3, 0, 4))), 'Actual independent slot lower bounds')
    digest, checks, positive = sha256(), 0, 0
    for r3, s5, r15, s15 in product(range(2), range(5), range(2), range(5)):
        result = partial_head_credit(dmax, root1_max, z, E3, slots, r3, s5, r15, s15)
        observed = (int(r3 == 0)*sum(v0)+sum(v[y] for y in range(B) if y % 5 == s5)
                    +int(r15 == 0)*sum(v0[y] for y in range(B) if y % 5 == s15))
        require(observed >= result['credit_lower'], 'Three original head indicators share one projected error')
        digest.update(json.dumps(encode([r3, s5, r15, s15, observed, result]), separators=(',', ':')).encode())
        checks += 1
        positive += result['credit_lower'] > 0
    nested = []
    for k in (5, 6):
        selected_capacity = sum((F(1, 5*3**a) for a in range(3, k+1)), F(0))
        E_D = selected_capacity*dmax-sum(m for a, m in depth_masses.items() if a <= k)
        tail = dmax*(F(1, 90)-selected_capacity)-sum(m for a, m in depth_masses.items() if a > k)
        require(E_D >= 0 and tail >= 0 and E3 == E_D+tail, 'Selected E_D is a part of E3, never an independent residual')
        nested.append({'last_selected_depth': k, 'E_D': E_D, 'complement_defect': tail})
    return {'mode': mode, 'dmax': dmax, 'root1_max': root1_max, 'z': z, 'E3': E3,
            'virtual_root0_mass': sum(v0), 'virtual_root1_mass': sum(v1),
            'projected_root0_defect_mass': sum(xi0), **bounds, 'head_checks': checks,
            'positive_head_credits': positive, 'head_digest': digest.hexdigest(), 'nested_selected_defects': nested,
            'complete_descendant_spill_upper': tail_upper, 'geometric_crossing': crossing}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('root_spill_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
    source = module('root_spill_source', base/'verify_joint_frontier.py')
    constructor = module('root_spill_constructor', base/'frontier/source-budgets/sharp_source_mass_endpoints.py')
    parent = module('root_spill_parent', base/'frontier/source-budgets/source_cost_endpoint_attainment.py')
    projection = module('root_spill_projection119', base/'frontier/cover-geometry/pure_three_projected_defect.py')
    tail = module('root_spill_tail66', base/'frontier/endpoint-bounds/endpoint_linear_neighborhood.py')
    sigma_checks = []
    for sigma in (F(0), F(1, 100), F(1, 27), F(2, 27), F(1, 3), F(49, 100)):
        h_upper = F(1, 2)+sigma/18
        old_c = F(2, 5)+sigma/6-sigma*sigma/45
        shared_c = F(2, 5)+13*sigma/90
        inherited = projection.concentrated_upper(sigma)
        require(inherited['h_upper'] == h_upper and inherited['coefficient_upper'] == shared_c
                and inherited['extra_capacity_defect_upper'] == sigma/240, 'Independent audit of119 final concentration interface')
        require(old_c-shared_c == sigma*(1-sigma)/45 and shared_c <= old_c, 'Shared deficit gives the stronger reference coefficient')
        require((3*sigma/8)/90 == sigma/240, 'One common alpha0 and beta0/beta1 capacity discrepancy')
        for D0, rest in ((F(1, 2)*(1-sigma), F(0)), (F(1, 2), F(0)),
                         (F(1, 2)*(1-sigma), sigma/2)):
            h = (5-D0-rest)/9
            c_upper = h-(1-sigma)*(4-rest)/45-F(1, 90)
            require(h <= h_upper and c_upper <= shared_c, 'Same-deficit source and carrier reference upper')
        sigma_checks.append({'sigma': sigma, 'h_upper': h_upper, 'reference_upper': shared_c,
                             'weaker_reference_upper': old_c, 'extra_defect_upper': sigma/240})
    cases = [finite_case(source, constructor, parent, tail, mode)
             for mode in ('cell0', 'cell1', 'root1', 'removed', 'mixed', 'absent', 'cell1-long')]
    require(cases[-1]['positive_head_credits'] > 0, 'A genuine finite original family has positive transported credits')
    face_credits = []
    slots = (F(0), F(1, 5), F(1, 5), F(3, 20), F(1, 5))
    for r3, s5, r15, s15 in product(range(2), range(5), range(2), range(5)):
        row = partial_head_credit(F(3, 4), F(1, 2), F(3, 4), F(0), slots, r3, s5, r15, s15)
        expected = F(int(r3 == 0), 120)+slots[s5]/90+int(r15 == 0)*slots[s15]/90
        require(row['credit_lower'] == expected, 'Exact three-term109 face recovery')
        face_credits.append(row['credit_lower'])
    return encode({'schema': 'erdos7-pure-three-root-spill-v1', 'source_sha256': PINS,
                   'concentration_interface': sigma_checks, 'actual_finite_cases': cases,
                   'head_checks': sum(c['head_checks'] for c in cases), 'exact_face_checks': len(face_credits),
                   'scope': 'Ordinary complete root0 projected-defect and conditional three-term109 head transport. Forced27 cell terms and deep-five extra deletion remain open inputs. E_D is inside E3. No new global K or Lean claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('root_spill_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact semantic root-spill certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: complete root0 spill, seven actual source cases,700 shared head checks and100 exact face recoveries; no independent E_D budget.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
