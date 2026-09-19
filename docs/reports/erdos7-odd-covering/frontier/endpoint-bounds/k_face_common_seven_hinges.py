#!/usr/bin/env python3
"""Uniform fourth/fifth hinges on both complete actual K-control beta faces.

The source LP retains the whole root1 beta budget in one mass constraint.
It never interpolates fixed-beta LP optima. All arithmetic in the layout
enumeration is exact integer arithmetic with independently checked LP duals.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product, permutations
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/k_face_common_seven_hinges.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'verify_joint_frontier.py': '85341d7f8fa2d0b109697bc17b005a7e75f7f6ec412fd2eb3d26383cf9fce24f',
    'frontier/comparison-bounds/allocated_seven_thresholds.py': 'b467824a30899cd14ab35ab4a1383c4a3848e5c9dcbdaebd6f4074e9a1d8e78d',
    'frontier/endpoint-bounds/endpoint_k_face_linear.py': '4fa0effc17c4f42a419f96f76931f389b8ca0af3ff3a4f60fd227ddbe6fc8b46',
    'certificates/source_norms/endpoint-bounds/endpoint_k_face_linear.json': '71244eac4f9cce79585c17663f80fcc7e16a03fcfcfda373c9747acc5c844682',
    'certificates/source_norms/comparison-bounds/allocated_seven_thresholds.json': 'ec6c4cf8b2c2f53179eead3d0a7499ca69fb796d57df6b65a91b0d672745a1b5',
}
ROOT = (0, 0, 1, 1, 1)
ETA = (F(1, 18),)+(F(1, 9),)*4
ORDER = ((0, 2), (3, 0), (1, 2), (4, 0))
GROUPS = (tuple(range(5)), tuple(range(5, 10)), tuple(range(10, 25)))
GROUP_MASSES = (F(1, 36), F(1, 12), F(5, 36))
COST_SCALE = 12005
MASS_SCALE = 360
TOTAL_SCALE = COST_SCALE*16200


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module: '+str(path))
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


def integer(value):
    value = F(value)
    require(value.denominator == 1, 'Exact integral scaling')
    return value.numerator


def seven_increment(threshold, value, extra):
    k = max(threshold-value, 0)
    return F(1, 5*7**max(k-extra, 0))+F(6, 35)*max(extra-k, 0)


def head_load(layout):
    r3, c9, s5, r15, s15, c45, s45 = layout
    return [1+int(ROOT[c] == r3)+int(c == c9)+int(s == s5)
            +int(ROOT[c] == r15 and s == s15)+int(c == c45 and s == s45)
            for c, s in product(range(5), repeat=2)]


def source_tables(first_beta):
    pre = [[F(0), F(1, 5) if c < 2 else F(0), F(0) if c == first_beta else F(1, 5),
            F(3, 20) if c < 2 else F(1, 10), F(1, 5)] for c in range(5)]
    raw = [[ETA[c]*pre[c][s] for s in range(5)] for c in range(5)]
    w = [[1-F(int(c >= 2)+int(c == 1)+int(s == 4)+int(c >= 2 and s == 4), 5)
          for s in range(5)] for c in range(5)]
    descendant = [[F(0) if s == 0 or (s == 1 and c >= 2) or (s == 2 and c == first_beta)
                   else ETA[c] for s in range(5)] for c in range(5)]
    return pre, raw, w, descendant


def lp_bound(coefficients, capacities, budgets):
    """Three disjoint capacity groups; independently check a primal and dual."""
    total, records = 0, []
    for indices, budget in zip(GROUPS, budgets):
        remaining, gamma = budget, 0
        allocation = {i: 0 for i in indices}
        for i in sorted(indices, key=lambda j: (-coefficients[j], j)):
            take = min(capacities[i], remaining)
            allocation[i] = take
            remaining -= take
            if take:
                gamma = coefficients[i]
            if remaining == 0:
                break
        if remaining:
            gamma = 0
        alpha = {i: max(0, coefficients[i]-gamma) for i in indices}
        require(gamma >= 0 and all(gamma+alpha[i] >= coefficients[i] for i in indices), 'Feasible LP dual')
        require(all(0 <= allocation[i] <= capacities[i] for i in indices)
                and sum(allocation.values()) <= budget, 'Feasible LP primal')
        primal = sum(coefficients[i]*allocation[i] for i in indices)
        dual = gamma*budget+sum(alpha[i]*capacities[i] for i in indices)
        require(primal == dual, 'Independent primal/dual equality')
        total += dual
        records.append({'gamma': gamma, 'alpha': [alpha[i] for i in indices],
                        'allocation': [allocation[i] for i in indices], 'value': dual})
    return total, records


def old_face_caps(base):
    """Convex root1-symmetric old expressions attain their face minimum at the barycenter."""
    source = module('k_hinge_old_source', base/'verify_joint_frontier.py')
    allocated = module('k_hinge_old_allocated', base/'frontier/comparison-bounds/allocated_seven_thresholds.py')
    bases = set(source.BASES)
    for perm in permutations((2, 3, 4)):
        order = (0, 1)+perm
        require({tuple(b[i] for i in order) for b in bases} == bases, 'Old source layout set is root1-symmetric')
    rest = (F(3, 4)/18+(F(9, 2)+3+1)/36+F(1, 72))/5
    h = (F(5, 36)+F(1, 12))/5
    result = {}
    for threshold in (4, 5):
        allocation = allocated.ALLOCATIONS[threshold][1]
        zero = allocated.AllocatedCost(source, threshold, allocation, 0, (0, 1, 1, 1, 1))
        positive = [allocated.AllocatedCost(source, threshold, allocation, e, (0,)*5)
                    for e in range(1, threshold-1)]
        for cost in [zero]+positive:
            require(all(cost.g(2, v) == cost.g(3, v) == cost.g(4, v)
                        for v in range(1, cost.cut+3)), 'Equal root1 cell costs, including affine tail')
        bounds = []
        for beta in ((F(1, 12),)*3, (F(1, 4), F(0), F(0))):
            d = (F(3, 4), F(3, 4))+tuple(F(1, 2)-b for b in beta)
            n = (F(1, 36), F(1, 12))+tuple(v/9 for v in d[2:])
            dat = (d, n, ETA, F(1, 4), F(53, 360))
            complement = F(1, 4)*F(1, 5*7**(threshold-1))+sum(cost.value(dat) for cost in positive)
            complement += F(1, 5*7**(threshold-2))*source.zero5_raw(('h', F(1)), dat)
            upper = F(53, 360)-F(1, 4)+rest+h+complement+zero.value(dat)-allocated.CREDITS[threshold]
            bounds.append(upper)
        require(bounds[0] <= bounds[1], 'Convex symmetric minimum does not exceed vertex maximum')
        result[str(threshold)] = {'minimum_on_full_relaxed_face': bounds[0], 'maximum_on_full_relaxed_face': bounds[1]}
    require(result['4']['minimum_on_full_relaxed_face'] == result['4']['maximum_on_full_relaxed_face'] == F(3686027, 17364375), 'Exact old fourth-hinge face value')
    require(result['5']['minimum_on_full_relaxed_face'] == F(29347862459, 182325937500)
            and result['5']['maximum_on_full_relaxed_face'] == F(435388099, 2701125000), 'Exact old fifth-hinge face range')
    return result


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('k_hinge_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/endpoint-bounds/endpoint_k_face_linear.json'))
    for path, pin in previous['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited pin')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
        used[path] = pin
    pre, raw, w, descendant = source_tables(2)
    for first in (2, 3, 4):
        other = source_tables(first)
        require(encode(other[0]) == previous['first_beta_slot_tables'][first-2]['pre_coefficients'], 'Exact72 first-beta table')
        perm = list(range(5))
        perm[2], perm[first] = perm[first], perm[2]
        for canonical, moved in zip((pre, raw, w, descendant), other):
            require(all(canonical[c] == moved[perm[c]] for c in range(5)), 'All source and tail tables transported by the first-beta cell swap')
        require(all(ROOT[c] == ROOT[perm[c]] for c in range(5)), 'Cell swap preserves root groups and independent head choices')
    require(sum(GROUP_MASSES) == F(1, 4), 'The complete source mass is retained')
    require(sum(sum(raw[c]) for c in range(2, 5))-GROUP_MASSES[2] == F(1, 180), 'The complete residual beta budget is retained as one source mass constraint')
    caps = [integer(MASS_SCALE*v) for row in raw for v in row]
    budgets = [integer(MASS_SCALE*v) for v in GROUP_MASSES]
    p = [[integer(20*v) for v in row] for row in pre]
    q = [[integer(18*v) for v in row] for row in descendant]
    wi = [integer(5*v) for row in w for v in row]
    costs = {}
    for threshold, weight, extra in product((4, 5), sorted(set(wi)), range(3)):
        values = [F(weight, 5)*max(v-threshold, 0)+seven_increment(threshold, v, extra) for v in range(1, 12)]
        inc = [b-a for a, b in zip(values, values[1:])]
        require(min(inc) >= 0 and all(a <= b for a, b in zip(inc, inc[1:])), 'Integer-convex complete bridge cost')
        require(all(x == F(weight, 5) for x in inc[threshold-1:]), 'Exact affine tail')
        costs[threshold, weight, extra] = [0]+[integer(COST_SCALE*v) for v in values]

    def tail_scaled(coefficients, a, b):
        require(min(coefficients) >= 0, 'Nonnegative tail coefficient')
        if b == 0:
            require(a in (3, 4), 'Selected pure3 depths')
            value = max(sum(p[c][s]*coefficients[5*c+s] for s in range(5)) for c in range(5))
            return integer(F(16200, 20*3**a))*value
        require(b == 2 and a in (0, 1, 2), 'Complete descendant-five category')
        if a == 0:
            value = max(sum(q[c][s]*coefficients[5*c+s] for c in range(5)) for s in range(5))
        elif a == 1:
            value = max(sum(q[c][s]*coefficients[5*c+s] for c in range(5) if ROOT[c] == r)
                        for r, s in product(range(2), range(5)))
        else:
            value = max(q[c][s]*coefficients[5*c+s] for c, s in product(range(5), repeat=2))
        return integer(F(16200, 18*25))*value

    weighted = [integer(COST_SCALE*F(v, 5)) for v in wi]
    categories = {'pure3': F(3, 2)*F(tail_scaled(weighted, 3, 0), TOTAL_SCALE),
                  **{name: F(5, 4)*F(tail_scaled(weighted, a, 2), TOTAL_SCALE)
                     for a, name in enumerate(('pure5', '3_times5', '9_times5'))}, 'deep35': F(1, 72)}
    complete_tail = sum(categories.values())
    tail_remainder = complete_tail-sum(F(tail_scaled(weighted, a, b), TOTAL_SCALE) for a, b in ORDER)
    seven_remainder = F(37, 360)-F(6, 35)*(F(5, 36)+F(1, 10))
    constant = integer(TOTAL_SCALE*(tail_remainder+seven_remainder))
    require(complete_tail == F(11, 120), 'Complete w-weighted old-tail sum')
    best = {t: None for t in (4, 5)}
    controls = {t: [] for t in (4, 5)}
    witnesses = {}
    count = 0
    digest = sha256()
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        B = head_load(layout)
        for root, slot in product(range(2), range(5)):
            m = [int(ROOT[c] == root)+int(s == slot) for c, s in product(range(5), repeat=2)]
            for threshold in (4, 5):
                arrays = [costs[threshold, weight, extra] for weight, extra in zip(wi, m)]
                coefficients = [array[v] for array, v in zip(arrays, B)]
                head_value, dual = lp_bound(coefficients, caps, budgets)
                increments = [[array[v+i]-array[v+i-1] for array, v in zip(arrays, B)] for i in range(1, 5)]
                selected = sum(tail_scaled(increments[j], a, b) for j, (a, b) in enumerate(ORDER))
                value = constant+45*head_value+selected
                digest.update(json.dumps([layout, root, slot, threshold, head_value, selected, value, dual], separators=(',', ':')).encode())
                count += 1
                if best[threshold] is None or value > best[threshold]:
                    best[threshold], controls[threshold] = value, [(layout, root, slot)]
                    witnesses[threshold] = {'layout': layout, 'extra_root3': root, 'extra_slot5': slot,
                        'source_head_lp': F(head_value, MASS_SCALE*COST_SCALE),
                        'selected_old_tail': F(selected, TOTAL_SCALE), 'head_dual': dual}
                elif value == best[threshold]:
                    controls[threshold].append((layout, root, slot))
    require(count == 250000, 'All12500 old heads,10 extra projections and two thresholds')
    uppers = {str(t): F(best[t], TOTAL_SCALE) for t in (4, 5)}
    old = old_face_caps(base)
    gains = {str(t): old[str(t)]['minimum_on_full_relaxed_face']-uppers[str(t)] for t in (4, 5)}
    require(min(gains.values()) > 0, 'Both actual-face hinges improve uniformly over the old53 expression')
    return encode({'schema': 'erdos7-k-face-common-seven-hinges-v1', 'source_sha256': used,
        'face_vertices': [398, 410, 422], 'carrier': [1, 1], 'symmetric_face_vertices': [616, 628, 640],
        'symmetric_carrier': [1, 0], 'surviving_mass': F(53, 360), 'source_mass': F(1, 4),
        'first_beta_cells': [2, 3, 4], 'beta_mass': F(1, 4), 'first_beta_minimum': F(1, 5),
        'canonical_first_beta': 2, 'source_upper_table': raw, 'source_group_masses': GROUP_MASSES,
        'source_group_indices': GROUPS, 'retained_density': w, 'raw_descendant5_coefficients': descendant,
        'old_head_moduli': [1, 3, 9, 5, 15, 45], 'additional_positive7_moduli': [21, 35],
        'selected_old_tail_exponents': ORDER, 'complete_old_tail_categories': categories,
        'complete_old_tail': complete_tail, 'remaining_old_tail': tail_remainder,
        'remaining_positive7': seven_remainder, 'integer_cost_scale': COST_SCALE,
        'integer_mass_scale': MASS_SCALE, 'integer_total_scale': TOTAL_SCALE,
        'joint_layout_checks': count, 'all_layout_and_dual_sha256': digest.hexdigest(),
        'maximizing_layouts': controls, 'maximizing_witnesses': witnesses, 'uniform_hinge_uppers': uppers,
        'old53_face_hinge_ranges': old, 'uniform_improvements_over53': gains,
        'uniform_three_hinge_denominator_gain': gains['4']/6+F(4, 33)*gains['5'],
        'scope': 'Ordinary uniform endpoint theorem on both complete actual K-control beta faces. Distributed beta and every original test residue remain arbitrary. The source LP keeps the full beta budget, with no interpolation of fixed-beta LP values. All exponent tails are complete. No finite neighborhood, global K replacement, unrestricted Erdos7 or Lean claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('k_hinge_writer', args.base/'certificate_io.py')
    rendered = json.dumps(result, indent=2)+'\n'
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical common beta-face hinge certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, rendered)
    elif args.output is not None:
        args.output.write_text(rendered)
    else:
        print(rendered)
    print('PASS:250000 exact common layouts and LP duals; uniform H4/H5='+str(result['uniform_hinge_uppers']))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
