#!/usr/bin/env python3
"""Complete saturated-J heads with one late split and exact affine crossings."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product, permutations
import importlib.util
import json
from math import gcd, lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_coupled_seven_heads.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/j-geometry/j_face_alignment.py': '188bd133ac91906fce843d481162a261972ed0f475d708141b3a3046ff467cff', 'certificates/source_norms/j-geometry/j_face_alignment.json': 'e2cb661d80b10f76d4a40c482d233e26b0979c3a116602d81e97a95532247485', 'profile-notes/129-192/130-the-whole-j-face-forces-source-anti-alignment.md': 'c9c11d0250836f7abc67eed901716f867b7a916a9797afcaa14b3f70584e33a8', 'frontier/endpoint-bounds/k_face_common_seven_hinges.py': '3128cab9f43ad9c89a5f129b7c7d0115a6f73684f613111a07a56f0bd71ddcdd', 'profile-notes/193-256/201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md': 'bfe4561a41e7d35ce0a9e1410bcdd92e3f732b2cfb7c86bc798ab4cd7cc0ab10'}
ROOT = (0, 0, 1, 1, 1)
ETA = (F(1, 18),)+(F(1, 9),)*4
LO, HI = F(1, 135), F(1, 90)
SCALE, MASS = 5*7**7, 16200
TOTAL = SCALE*MASS
QSLOTS = tuple(map(F, ('0', '1/5', '1/5', '3/20', '1/5')))
SUPPORT = (13, 14, 17, 18, 19, 22, 23, 24)
REMAINDERS = tuple(map(F, ('53/600', '71/1000', '1367/27000', '1007/27000', '2471/81000')))
Z2, Z4 = F(43, 700), F(1, 28)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original proof provider')
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


def integer(value):
    value = F(value)
    require(value.denominator == 1, 'Exact integral scaling')
    return value.numerator


def layouts():
    return product(range(2), range(5), range(5), range(2), range(5), range(5), range(5))


def source_tables(theta):
    """Absolute raw caps and separate normalized deep-ternary coefficients."""
    theta = F(theta)
    require(LO <= theta <= HI, 'Actual mandatory late-split interval')
    normalized = [list(QSLOTS) if c < 2 else
                  list(map(F, ('0', '0', '0' if c == 2 else '1/5', '1/10', '1/5')))
                  for c in range(5)]
    absolute = [[ETA[c]*normalized[c][s] for s in range(5)] for c in range(5)]
    absolute[3][2] -= theta
    absolute[4][2] -= F(1, 90)-theta
    descendant = [[F(0) if s == 0 or (c >= 2 and s == 1) or (c == 2 and s == 2)
                   else ETA[c] for s in range(5)] for c in range(5)]
    density = [[1-F(int(c < 2)+int(c == 1)+int(s == 4)+int(c >= 2 and s == 4), 5)
                for s in range(5)] for c in range(5)]
    return normalized, absolute, descendant, density


def raw_source_lp(coefficients, theta):
    """Exact value for the relaxed cap LP, not an actual-attainment assertion."""
    require(len(coefficients) == 25 and min(coefficients) >= 0, 'Nonnegative complete rectangle objective')
    caps = [v for row in source_tables(theta)[1] for v in row]
    return sum(c*z for c, z in zip(caps, coefficients))-min(coefficients[i] for i in SUPPORT)/120


def deletion_correction(head):
    require(len(head) == 25 and min(head) >= 0, 'Nonnegative actual survivor head')
    pure3 = sum(QSLOTS[s]*min(head[s], head[5+s])/90 for s in range(5))
    deep5 = sum(ETA[c]*(1+int(c >= 2))*min(head[5*c:5*c+5])/100 for c in range(5))
    return pure3, deep5


def max_min_affines(left, right):
    """Maximize min of two lines in normalized late coordinate x in[0,1]."""
    a0, a1 = left
    b0, b1 = right
    best = max(min(a0, b0), min(a1, b1))
    at = F(0) if min(a0, b0) >= min(a1, b1) else F(1)
    crossed = (a0-b0)*(a1-b1) < 0
    if crossed:
        x = F(a0-b0, a0-b0-a1+b1)
        value = a0+(a1-a0)*x
        require(0 < x < 1 and value == b0+(b1-b0)*x, 'Exact common-late intersection')
        if value > best:
            best, at = value, x
    return best, at, crossed


class SaturatedJCoupledSevenHead:
    """Complete positive hinge interface, excluding a separate constant mass term."""
    def __init__(self, base):
        self.base = base
        self.bridge = module('j_seven_common', base/'frontier/endpoint-bounds/k_face_common_seven_hinges.py')
        require(self.bridge.ROOT == ROOT and self.bridge.ETA == ETA, 'Same coordinate grammar only')
        normalized, raw, descendant, density = source_tables(LO)
        self.p = [[integer(20*x) for x in row] for row in normalized]
        self.e = [[integer(18*x) for x in row] for row in descendant]
        self.w = tuple(integer(5*x) for row in density for x in row)
        self.caps = [tuple(integer(MASS*x) for row in source_tables(theta)[1] for x in row)
                     for theta in (LO, HI)]
        self.raw_cost = {}
        for t, w, m in product(range(1, 9), sorted(set(self.w)), range(5)):
            values = [F(w, 5)*max(v-t, 0)+self.bridge.seven_increment(t, v, m) for v in range(1, 12)]
            increments = [b-a for a, b in zip(values, values[1:])]
            require(min(increments) >= 0 and all(a <= b for a, b in zip(increments, increments[1:]))
                    and all(x == F(w, 5) for x in increments[t-1:]),
                    'All J bridge transitions and the exact infinite affine continuation')
            self.raw_cost[t, w, m] = [0]+[integer(SCALE*v) for v in values]
        self.extras = [(r, s, tuple(int(ROOT[c] == r)+int(j == s) for c, j in product(range(5), repeat=2)))
                       for r, s in product(range(2), range(5))]
        self.added = [(c63, r105, s105,
                       tuple(int(c == c63)+int(ROOT[c] == r105 and s == s105)
                             for c, s in product(range(5), repeat=2)))
                      for c63, r105, s105 in product(range(5), range(2), range(5))]
        self.evaluations = 0

    def selected(self, coefficients, step):
        if step in (2, 4):
            value = max(sum(self.p[c][s]*coefficients[5*c+s] for s in range(5)) for c in range(5))
            return (MASS//(20*(27 if step == 2 else 81)))*value
        if step == 1:
            value = max(sum(self.e[c][s]*coefficients[5*c+s] for c in range(5)) for s in range(5))
        else:
            require(step == 3, 'Only the four independent selected labels')
            value = max(sum(self.e[c][s]*coefficients[5*c+s] for c in range(5) if ROOT[c] == r)
                        for r, s in product(range(2), range(5)))
        return (MASS//(18*25))*value

    def prepare(self, coefficients):
        coefficients = {int(t): F(v) for t, v in coefficients.items() if F(v)}
        require(coefficients and all(1 <= t <= 8 and v > 0 for t, v in coefficients.items()),
                'Nonzero nonnegative combination of original thresholds1 through8')
        denominator = lcm(*(v.denominator for v in coefficients.values()))
        numerators = {t: integer(v*denominator) for t, v in coefficients.items()}
        divisor = gcd(*numerators.values())
        ints = {t: v//divisor for t, v in numerators.items()}
        factor = F(divisor, denominator)
        prefix = {t: min(t-1, 4) for t in ints}
        highest = max(prefix.values())
        head = {(w, m): [0]+[sum(a*self.raw_cost[t, w, m][v] for t, a in ints.items()) for v in range(1, 7)]
                for w, m in product(sorted(set(self.w)), range(5))}
        increments = {(i, k): {(w, m): [0]+[sum(a*(self.raw_cost[t, w, m][v+k+1]
                                    -self.raw_cost[t, w, m][v+k]) for t, a in ints.items() if prefix[t] >= i)
                                    for v in range(1, 7)]
                              for w, m in product(sorted(set(self.w)), range(5))}
                      for i in range(1, highest+1) for k in range(i)}
        for i, w, m, v in product(range(1, highest+1), sorted(set(self.w)), range(5), range(1, 7)):
            values = [increments[i, k][w, m][v] for k in range(i)]
            require(min(values) >= 0 and all(a <= b for a, b in zip(values, values[1:])),
                    'Ordered prefix-conditioned increments on the same original test')
        constants = tuple(integer(TOTAL*sum(a*(REMAINDERS[prefix[t]]+z) for t, a in ints.items()))
                          for z in (Z2, Z4))
        return {'coefficients': coefficients, 'primitive_coefficients': ints, 'factor': factor,
                'highest_selected_label': highest, 'head': head, 'increments': increments,
                'constants': constants}

    def correction(self, record, B):
        H = [sum(a*max(v-t, 0) for t, a in record['primitive_coefficients'].items()) for v in B]
        return integer(TOTAL*sum(deletion_correction(H)))

    def objective(self, record, B, extra, correction, expanded):
        z = [record['head'][w, m][v] for w, m, v in zip(self.w, extra, B)]
        raw = [sum(c*a for c, a in zip(cap, z))-(MASS//120)*min(z[i] for i in SUPPORT)
               for cap in self.caps]
        terms = []
        for step in range(1, record['highest_selected_label']+1):
            def array(k):
                table = record['increments'][step, k]
                return [table[w, m][v] for w, m, v in zip(self.w, extra, B)]
            hi = array(step-1)
            value = self.selected(hi, step)
            if step in (2, 3):
                lo = array(step-2)
                value = min(value, self.selected(lo, step)+24*max(h-l for h, l in zip(hi, lo)))
            if step == 4:
                lo, mid = array(1), array(2)
                value = min(value, self.selected(lo, step)+8*max(max(2*(m-l), h-l) for l, m, h in zip(lo, mid, hi)),
                            self.selected(mid, step)+8*max(h-m for h, m in zip(hi, mid)))
            terms.append(value)
        shift = record['constants'][int(expanded)]-correction+sum(terms)
        values = tuple(a+shift for a in raw)
        require(min(values) >= 0, 'Both complete corrected endpoint bounds are nonnegative')
        self.evaluations += 1
        return values

    def rational_objective(self, coefficients, layout, projection, theta):
        """Independent unscaled fractional evaluation, including selected intersections."""
        a = {int(t): F(v) for t, v in coefficients.items() if F(v)}
        B = self.bridge.head_load(layout)
        r, s, c63, r105, s105 = projection
        extras = [int(ROOT[c] == r)+int(j == s)
                  +(int(c == c63)+int(ROOT[c] == r105 and j == s105) if c63 is not None else 0)
                  for c, j in product(range(5), repeat=2)]
        normalized, caps, descendant, density = source_tables(theta)
        w = [v for row in density for v in row]
        fn = lambda t, i, v: w[i]*max(v-t, 0)+self.bridge.seven_increment(t, v, extras[i])
        z = [sum(v*fn(t, i, B[i]) for t, v in a.items()) for i in range(25)]
        value = raw_source_lp(z, theta)
        capden = lcm(24, 12, 8, *(c.denominator for row in caps for c in row))
        capints = [integer(capden*c) for row in caps for c in row]
        zden = lcm(*(v.denominator for v in z))
        lp, dual = self.bridge.lp_bound([integer(v*zden) for v in z], capints,
                                      [capden//24, capden//12, capden//8])
        require(F(lp, capden*zden) == value and sum(row['value'] for row in dual) == lp,
                'Closed J source formula equals an independent feasible primal/dual LP')
        def P(arr, step):
            if step in (2, 4):
                return max(sum(normalized[c][s]*arr[5*c+s] for s in range(5)) for c in range(5))/(27 if step == 2 else 81)
            if step == 1:
                return max(sum(descendant[c][s]*arr[5*c+s] for c in range(5)) for s in range(5))/25
            return max(sum(descendant[c][s]*arr[5*c+s] for c in range(5) if ROOT[c] == r)
                       for r, s in product(range(2), range(5)))/25
        for step in range(1, max(min(t-1, 4) for t in a)+1):
            levels = [[sum(v*(fn(t, i, B[i]+k+1)-fn(t, i, B[i]+k)) for t, v in a.items()
                           if min(t-1, 4) >= step) for i in range(25)] for k in range(step)]
            hi = levels[-1]
            choices = [P(hi, step)]
            if step in (2, 3):
                lo = levels[-2]
                choices.append(P(lo, step)+max(h-l for h, l in zip(hi, lo))/675)
            if step == 4:
                lo, mid = levels[1:3]
                choices += [P(lo, step)+max(max(2*(m-l), h-l) for l, m, h in zip(lo, mid, hi))/2025,
                            P(mid, step)+max(h-m for h, m in zip(hi, mid))/2025]
            value += min(choices)
        H = [sum(v*max(b-t, 0) for t, v in a.items()) for b in B]
        value -= sum(deletion_correction(H))
        value += sum(v*(REMAINDERS[min(t-1, 4)]+(Z2 if c63 is None else Z4)) for t, v in a.items())
        return value

    def check_compiler(self, record):
        count = 0
        for layout in ((0, 1, 2, 0, 2, 1, 2), (1, 3, 2, 1, 2, 3, 2)):
            B = self.bridge.head_load(layout)
            cor = self.correction(record, B)
            for r, s, c, rr, ss in ((0, 2, None, None, None), (1, 2, 3, 1, 2)):
                ex = tuple(int(ROOT[k] == r)+int(j == s)
                           +(int(k == c)+int(ROOT[k] == rr and j == ss) if c is not None else 0)
                           for k, j in product(range(5), repeat=2))
                values = self.objective(record, B, ex, cor, c is not None)
                for theta, v in zip((LO, HI), values):
                    require(record['factor']*F(v, TOTAL) == self.rational_objective(
                        record['coefficients'], layout, (r, s, c, rr, ss), theta),
                        'Independent fractional and compiled complete J branch agree')
                    count += 1
        return count

    def scan(self, coefficients):
        record = self.prepare(coefficients)
        rational_checks = self.check_compiler(record)
        best, witness, digest = F(-1), None, sha256()
        original = expanded = pruned = checked = crossings = 0
        max_pruned = -1
        started = self.evaluations
        seed = (1, 3, 2, 1, 2, 3, 2)

        def consider(layout, B, cor, r, s, oldextra, old, seed_step):
            nonlocal best, witness, checked, crossings
            for c, rr, ss, add in self.added:
                ex = tuple(a+b for a, b in zip(oldextra, add))
                new = self.objective(record, B, ex, cor, True)
                value, x, crossed = max_min_affines(old, new)
                checked += 1
                crossings += int(crossed)
                digest.update(repr(('seed' if seed_step else 'expanded', layout, r, s, c, rr, ss, old, new)).encode())
                if value > best:
                    best = value
                    witness = {'layout': layout, 'seven21_root': r, 'seven35_slot': s,
                               'seven63_cell': c, 'seven105_root': rr, 'seven105_slot': ss,
                               'normalized_late_coordinate': x, 'theta': LO+(HI-LO)*x,
                               'two_projection_endpoints': old, 'four_projection_endpoints': new,
                               'primitive_scaled_upper': value}
        B = self.bridge.head_load(seed)
        cor = self.correction(record, B)
        for r, s, ex in self.extras:
            old = self.objective(record, B, ex, cor, False)
            consider(seed, B, cor, r, s, ex, old, True)
        for layout in layouts():
            B = self.bridge.head_load(layout)
            cor = self.correction(record, B)
            for r, s, ex in self.extras:
                old = self.objective(record, B, ex, cor, False)
                upper = max(old)
                original += 1
                if upper <= best:
                    pruned += 1
                    max_pruned = max(max_pruned, upper)
                    digest.update(repr(('bounded', layout, r, s, old)).encode())
                else:
                    expanded += 1
                    consider(layout, B, cor, r, s, ex, old, False)
        require(original == 125000 and expanded+pruned == original and checked == 500+50*expanded
                and witness is not None and max_pruned <= best,
                'Every original head and all6250000 containing projections covered with safe uniform pruning')
        w = witness
        lay = tuple(w['layout'])
        oldp = (w['seven21_root'], w['seven35_slot'], None, None, None)
        newp = (w['seven21_root'], w['seven35_slot'], w['seven63_cell'], w['seven105_root'], w['seven105_slot'])
        values = [self.rational_objective(record['coefficients'], lay, p, w['theta']) for p in (oldp, newp)]
        require(min(values) == record['factor']*F(best, TOTAL), 'Independent exact maximizing-branch reconstruction')
        w['complete_bounds_at_theta'] = values
        return {'coefficients': record['coefficients'], 'primitive_coefficients': record['primitive_coefficients'],
                'factor': record['factor'], 'common_scale': TOTAL,
                'complete_hinge_upper': record['factor']*F(best, TOTAL),
                'original_head_projection_branches': original, 'expanded_branches': expanded,
                'bounded_without_extra_projections': pruned, 'expanded_objective_count_including_seed': checked,
                'strict_crossing_branches_including_seed': crossings,
                'complete_affine_branch_evaluations': self.evaluations-started,
                'independent_rational_checks': rational_checks+2,
                'maximum_unexpanded_upper': record['factor']*F(max_pruned, TOTAL) if pruned else None,
                'all_branch_decisions_sha256': digest.hexdigest(), 'maximizing_witness': w,
                'old_complete_tail_constant': record['factor']*F(record['constants'][0], TOTAL),
                'new_complete_tail_constant': record['factor']*F(record['constants'][1], TOTAL)}


def geometry_checks(problem, face):
    require(F(face['linear_upper']) == F(16, 25)
            and all(tuple(map(F, row['data'][3:])) == (F(1, 4), F(3, 20))
                    for row in face['affine_product_face_checks']),
            'Exactly the whole saturated J source and survivor masses')
    positive = list(SUPPORT)
    data = []
    for theta in (LO, HI):
        normalized, absolute, descendant, density = source_tables(theta)
        raw = [v for row in absolute for v in row]
        require(sum(raw[:5]) == F(1, 24) and sum(raw[5:10]) == F(1, 12)
                and sum(raw[10:]) == F(2, 15) and F(2, 15)-F(1, 8) == F(1, 120)
                and [i for i in range(10, 25) if raw[i] > 0] == positive
                and min(raw[i] for i in positive) >= F(1, 90) > F(1, 120),
                'Exact root budgets, common LP deficit and every admissible deficit-bearing coordinate')
        require(sum(QSLOTS) == F(3, 4) and min(v for row in density for v in row) == F(2, 5) > F(6, 35),
                'Complete pure3 projection and convex J bridge density')
        data.append({'theta': theta, 'absolute_caps': absolute})
    normalized, absolute, descendant, density = source_tables(LO)
    require([F(problem.selected([1]*25, i), MASS) for i in range(1, 5)]
            == [F(1, 50), F(1, 36), F(1, 75), F(1, 108)],
            'Normalized deep-ternary operators are distinct from absolute source caps')
    zero = [F(11, 360), F(13, 600), F(1, 60), F(1, 180), F(1, 72)]
    selected = [F(13, 750), F(11, 540), F(1, 75), F(11, 1620)]
    require(sum(zero) == REMAINDERS[0]
            and all(REMAINDERS[k+1] == REMAINDERS[k]-selected[k] for k in range(4))
            and F(1, 36)-F(1, 45) == F(1, 180), 'Every selected zero-seven label peeled exactly once')
    rawcofactor = [F(1, 8), F(1, 12), F(1, 24), F(1, 10), F(1, 40),
                   F(1, 15), F(1, 60), F(1, 45), F(1, 180), F(1, 72)]
    require(sum(rawcofactor) == F(1, 2) and sum(rawcofactor)/5 == F(1, 10)
            and F(1, 10)-F(6, 35)*(F(1, 8)+F(1, 10)) == Z2
            and Z2-F(6, 35)*(F(1, 12)+F(1, 15)) == Z4,
            'Complete nonnegative positive-seven cap series with assigned depth-one terms removed')
    inventory = set(layouts())
    perms = [(0, 1)+p for p in permutations((2, 3, 4))]+[(1, 0, 2, 3, 4)]
    for perm in perms:
        moved = {(r, perm[c], s, rr, ss, perm[cc], sss) for r, c, s, rr, ss, cc, sss in inventory}
        require(moved == inventory and all(ROOT[c] == ROOT[perm[c]] for c in range(5)),
                'Full test inventory transports every ordered root1 source pair and both J faces')
    require(max_min_affines((0, 2), (2, 0))[:2] == (F(1), F(1, 2))
            and max_min_affines((3, 5), (2, 4))[:2] == (4, F(1)),
            'Strict interior and parallel affine cases prevent endpoint-only max-min substitution')
    return {'source_mass': F(1, 4), 'survivor_mass': F(3, 20), 'root_group_budgets': [F(1, 24), F(1, 12), F(1, 8)],
            'late_split_interval': [LO, HI], 'canonical_beta_late_cells': [2, 3, 4],
            'endpoint_source_tables': data, 'normalized_deep_ternary_coefficients': normalized,
            'absolute_descendant_five_coefficients': descendant, 'retained_survivor_density': density,
            'root1_cap_surplus': F(1, 120), 'root1_positive_support': SUPPORT,
            'complete_zero7_categories_after_head': zero, 'selected_caps': selected,
            'complete_zero7_remainders': REMAINDERS, 'complete_raw_cofactor_caps': rawcofactor,
            'positive7_two_projection_remainder': Z2, 'positive7_four_projection_remainder': Z4,
            'deep3_deletion_slot_marginal': [q/90 for q in QSLOTS],
            'deep5_deletion_cell_marginal': [e*(1+int(c >= 2))/100 for c, e in enumerate(ETA)],
            'mixed_intersection_caps': [F(1, 675), F(1, 2025)],
            'transported_layout_permutations': perms}


def calculate(base):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical reader and mathematical inputs')
    io = module('j_seven_io', base/'certificate_io.py')
    face = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j-geometry/j_face_alignment.json'))
    pins = dict(PINS)
    for path, pin in face['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent original J source '+path)
        pins[path] = pin
    engine = module('j_seven_inventory', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    for path, pin in engine.pins.items():
        require(path not in pins or pins[path] == pin, 'Consistent original cost input '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    require(all(pins.get(path) == pin for path, pin in engine.pins.items()), 'Original independent cost inventory')
    problem = SaturatedJCoupledSevenHead(base)
    geometry = geometry_checks(problem, face)
    rows = []
    jobs = [('AP13', {4: F(1)}, F(0))]
    for i in (0, 16):
        tag = engine.specs[i]['tag']
        f = lambda n: engine.source.zero5_cost(tag, n)
        a = {1: f(2)-f(1)} | {t: f(t+1)-2*f(t)+f(t-1) for t in range(2, 9)}
        degree, leading, constant, cutoff = engine.source.zero5_cost_metadata(tag)
        require(degree == 1 and cutoff == 8 and min(a.values()) >= 0
                and all(f(1)+sum(c*max(n-t, 0) for t, c in a.items()) == f(n) for n in range(1, 10))
                and sum(a.values()) == leading and f(1)-sum(t*c for t, c in a.items()) == constant,
                'Every finite heavy transition and its complete original affine continuation')
        jobs.append((i, a, f(1)))
    for index, a, at_one in jobs:
        scan = problem.scan(a)
        raw = at_one*F(3, 20)+scan['complete_hinge_upper']
        mean = at_one*F(3, 20)+sum(a.values())*F(49, 100)
        upper = min(raw, mean)
        rows.append({'index': index, 'at_one': at_one, 'scan': scan,
                     'complete_head_upper': raw, 'complete_mean_only_upper': mean,
                     'adopted_upper': upper, 'improvement_over_mean_only': mean-upper})
        print('Complete saturated J '+str(index)+': '+str(float(upper))+'; raw head='+str(float(raw))
              +'; expanded='+str(scan['expanded_branches'])+'; crossings='
              +str(scan['strict_crossing_branches_including_seed']), flush=True)
    return encode({'schema': 'erdos7-j-face-coupled-seven-heads-v1', 'source_sha256': pins,
        'geometry': geometry, 'complete_mean_upper': F(16, 25), 'hinge1_upper': F(49, 100),
        'results': rows,
        'scope': 'Ordinary complete AP13 and original heavy0/heavy16 bounds on both saturated actual J faces. Each scan covers all6250000 containing head/projection branches and the entire common late-split interval using both endpoints and any exact crossing of the two complete affine bounds. Absolute raw caps and normalized deep-ternary operators are distinct. Every original independent label, complete cap-series tail, one actual source and survivor and both J-specific deletion families remain. No K forced27 assumption, actual-attainment assertion, off-face transport, complete52-cost/global comparison, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j_seven_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete saturated-J certificate')
    print('PASS: three complete saturated-J scans, every infinite tail and exact shared-theta crossings.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
