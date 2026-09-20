#!/usr/bin/env python3
"""Retain the independent135 test inside the complete raw/survivor bridge."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import groupby, product
import json
from math import lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/retained135_heavy_comparison.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/retained-transport/selected_deletion_mask_heavy_comparison.py': '7292f7ea3b0b8494c729436e31ec2badae119bf71ce1c3a9d37dd818d17f3711',
    'certificates/source_norms/retained-transport/selected_deletion_mask_heavy_comparison.json': 'f41035f5bf87afa18a9bd6f815ea1d082f693f266244f2b16ecd076aafe10e85',
    'profile-notes/193-256/222-deep-five-deletion-retains-the-selected-observation-masks.md': '75f2e13689ba09637307ef2eea60d055d8bd4312dd2ebe7062d6fef8664f123c',
}
BRANCHES = ('nested', 'disjoint')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original source')
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


def encode_dual_bank(bank, inequality_count=4726, equality_count=55):
    """Losslessly intern rationals and encode runs of the complete dual vectors."""
    values = sorted({'0'} | {v for record in bank.values()
        for v in list(record['nonzero_inequality_duals'].values())
        +record['equality_duals']+[record['raw_objective_upper']]})
    indices = {value: str(i) for i, value in enumerate(values)}
    buckets = {}
    for key, record in sorted(bank.items()):
        vector = [indices[record['nonzero_inequality_duals'].get(str(i), '0')]
                  for i in range(inequality_count)]
        vector += [indices[v] for v in record['equality_duals']+[record['raw_objective_upper']]]
        require(len(vector) == inequality_count+equality_count+1, 'Every exact dual entry is encoded')
        runs = []
        for value, group in groupby(vector):
            count = sum(1 for _ in group)
            runs.append(value if count == 1 else value+'*'+str(count))
        buckets.setdefault(key[0], {}).setdefault(key[1], {})[key] = ','.join(runs)
    return {'codec': 'exact-rational-table-rle-duals-v1',
            'inequality_count': inequality_count, 'equality_count': equality_count,
            'rational_table': [' '.join(values[i:i+128]) for i in range(0, len(values), 128)],
            'dual_buckets': buckets}


def decode_dual_bank(encoded, inequality_count=4726, equality_count=55):
    """Restore all prices before the independent exact-column feasibility check."""
    require(isinstance(encoded, dict) and set(encoded) == {'codec', 'inequality_count',
        'equality_count', 'rational_table', 'dual_buckets'}, 'Exact dual codec fields')
    require(encoded['codec'] == 'exact-rational-table-rle-duals-v1'
            and type(encoded['inequality_count']) is int and encoded['inequality_count'] == inequality_count
            and type(encoded['equality_count']) is int and encoded['equality_count'] == equality_count,
            'Exact dual codec and complete dimensions')
    table = encoded['rational_table']
    require(isinstance(table, list) and table and all(isinstance(row, str) for row in table),
            'Nonempty exact rational table')
    pieces = [row.split(' ') for row in table]
    require(all(len(row) == 128 for row in pieces[:-1]) and 1 <= len(pieces[-1]) <= 128,
            'Canonical rational-table blocks')
    values = [value for row in pieces for value in row]
    require(values == sorted(set(values)) and '0' in values
            and all(value == str(F(value)) for value in values), 'Unique sorted canonical rationals')
    length = inequality_count+equality_count+1
    result = {}
    for prefix, records in encoded['dual_buckets'].items():
        require(len(prefix) == 1 and prefix in '0123456789abcdef' and records, 'Canonical nonempty hash bucket')
        for second, entries in records.items():
            require(len(second) == 1 and second in '0123456789abcdef' and entries,
                    'Canonical nonempty second hash bucket')
            for key, row in entries.items():
                require(len(key) == 64 and all(c in '0123456789abcdef' for c in key)
                        and key.startswith(prefix+second) and key not in result,
                        'Unique canonical branch hash')
                require(isinstance(row, str) and row, 'Nonempty complete exact dual vector')
                vector, previous = [], None
                for token in row.split(','):
                    parts = token.split('*')
                    require(len(parts) in (1, 2) and all(p and p.isascii() and p.isdecimal()
                        and str(int(p)) == p for p in parts), 'Canonical integer run tokens')
                    index = int(parts[0])
                    count = 1 if len(parts) == 1 else int(parts[1])
                    require(index < len(values) and index != previous
                            and (len(parts) == 1 or count >= 2) and len(vector)+count <= length,
                            'In-range maximal runs with no excess dual entries')
                    vector.extend([values[index]]*count)
                    previous = index
                require(len(vector) == length, 'No missing inequality, equality or signed-value entry')
                result[key] = {'nonzero_inequality_duals': {str(i): value
                    for i, value in enumerate(vector[:inequality_count]) if value != '0'},
                    'equality_duals': vector[inequality_count:-1], 'raw_objective_upper': vector[-1]}
    return result


class IntegerDualChecker:
    """Check every rational column using positive common denominators."""
    def __init__(self, lp):
        self.nvars, self.nrows, self.neq = lp.nvars, len(lp.rows), len(lp.equalities)
        values = [a for row in lp.rows+lp.equalities for a in row.values()]+lp.rhs+lp.erhs
        self.matrix_scale = lcm(*(a.denominator for a in values))
        integer = lambda a: a.numerator*(self.matrix_scale//a.denominator)
        self.columns = [[(i, integer(a)) for i, a in column] for column in lp.columns]
        self.eqcolumns = [[(i, integer(a)) for i, a in column] for column in lp.eqcolumns]
        self.rhs, self.erhs = [list(map(integer, v)) for v in (lp.rhs, lp.erhs)]
        require(self.matrix_scale > 0 and len(self.columns) == len(self.eqcolumns) == self.nvars
                and len(self.rhs) == self.nrows and len(self.erhs) == self.neq,
                'Every source row and objective column has an exact positive scaling')

    def check(self, objective, record):
        require(len(objective) == self.nvars and set(record) == {
            'nonzero_inequality_duals', 'equality_duals', 'raw_objective_upper'},
            'Complete objective and exact rational dual fields')
        prices = [F(0)]*self.nrows
        for key, value in record['nonzero_inequality_duals'].items():
            i = int(key)
            require(str(i) == str(key) and 0 <= i < self.nrows, 'Canonical inequality row')
            prices[i] = F(value)
        equalities = list(map(F, record['equality_duals']))
        require(len(equalities) == self.neq and min(prices) >= 0,
                'Nonnegative inequality prices and all unrestricted equality prices')
        scale = lcm(*{a.denominator for a in prices+equalities+objective})
        require(scale > 0, 'Positive objective and dual denominator')
        integer = lambda a: a.numerator*(scale//a.denominator)
        y, z, target = [list(map(integer, v)) for v in (prices, equalities, objective)]
        for k in range(self.nvars):
            lhs = sum(a*y[i] for i, a in self.columns[k])+sum(a*z[i] for i, a in self.eqcolumns[k])
            require(lhs >= self.matrix_scale*target[k], 'Exact retained135 dual column '+str(k))
        value = F(sum(a*v for a, v in zip(self.rhs, y))+sum(a*v for a, v in zip(self.erhs, z)),
                  self.matrix_scale*scale)
        require(value == F(record['raw_objective_upper']), 'Complete signed rational dual value')
        return value


def lp_class(base):
    parent = module('retained135_mask_lp', base/'frontier/retained-transport/selected_deletion_mask_heavy_comparison.py')

    class Retained135LP(parent.MaskDeletionLP):
        """Containing submeasures of one independent original135 cylinder."""
        def __init__(self, original, wi, pre, branch):
            super().__init__(original, wi, branch)
            self.original222_spec = super().specification()
            self.nvars = 2100
            self.lambda135 = list(range(2075, 2100))
            self.equalities.append({k: F(1) for k in self.lambda135})
            self.erhs.append(F(1))
            self.raw135_caps, self.submeasure_links = [], []
            for cell, w in enumerate(wi):
                c, s = divmod(cell, 5)
                self.raw135_caps.append(len(self.rows))
                self.rows.append({2075+cell: -pre[c][s]/27,
                    **{1275+16*cell+mask: F(1) for mask in range(16)}})
                self.rhs.append(F(0))
                for mask in range(16):
                    k = 16*cell+mask
                    raw, surviving = 1275+k, 1675+k
                    for row in ({raw: F(1), k: F(-1)},
                                {surviving: F(1), 425+k: F(-1)},
                                {surviving: F(1), raw: -F(w, 5)},
                                {425+k: F(1), surviving: F(-1), k: -F(w, 5), raw: F(w, 5)}):
                        self.submeasure_links.append(len(self.rows))
                        self.rows.append(row)
                        self.rhs.append(F(0))
            self.rows.append({1675+k: F(1) for k in range(400)})
            self.rhs.append(F(1, 135))
            self.intersection_caps = [(bit, modulus, F(1, lcm(135, modulus)))
                                      for bit, modulus in ((0, 25), (2, 75), (3, 81))]
            require([cap for _, _, cap in self.intersection_caps] == [F(1, 675), F(1, 675), F(1, 405)],
                    'The three original raw intersection denominators are their exact lcms')
            for bit, _, cap in self.intersection_caps:
                self.rows.append({1275+16*cell+mask: F(1) for cell in range(25)
                                  for mask in range(16) if mask & (1 << bit)})
                self.rhs.append(cap)
            # All measures have total at most1, and all profiles lie in simplexes.
            self.unit_rows = []
            for k in range(self.nvars):
                self.unit_rows.append(len(self.rows))
                self.rows.append({k: F(1)})
                self.rhs.append(F(1))
            self.columns, self.eqcolumns = ([[] for _ in range(self.nvars)] for _ in range(2))
            for i, row in enumerate(self.rows):
                for k, a in row.items():
                    self.columns[k].append((i, a))
            for i, row in enumerate(self.equalities):
                for k, a in row.items():
                    self.eqcolumns[k].append((i, a))
            require(len(self.rows) == 4726 and len(self.equalities) == 55,
                    'Complete2100-variable system with4726 inequalities and55 equalities')
            self.checker = IntegerDualChecker(self)
            self.check_dual = self.checker.check

        def specification(self):
            return encode({'branch': self.branch, 'variables': self.nvars,
                'original222_lp': self.original222_spec, 'raw135_variables': 400,
                'surviving135_variables': 400, 'independent135_projection_variables': 25,
                'normalized_raw135_projection_caps': 25, 'submeasure_links': 1600,
                'surviving135_cap': F(1, 135), 'raw_intersection_caps': self.intersection_caps,
                'unit_repair_rows': 2100, 'inequalities': len(self.rows), 'equalities': len(self.equalities),
                'rows_sha256': sha256(json.dumps(encode([self.rows, self.rhs, self.equalities, self.erhs]),
                    sort_keys=True, separators=(',', ':')).encode()).hexdigest()})

    return Retained135LP


def retained135_head_class(base):
    parent = module('retained135_head_parent', base/'frontier/retained-transport/retained_deletion_heavy_comparison.py')
    extended = lp_class(base)

    class Retained135Head(parent.RetainedDeletionHead):
        R4 = F(71, 3240)

        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            pre, raw, _, _ = self.bridge.source_tables(2)
            require(all(raw[c][s] == self.bridge.ETA[c]*pre[c][s] for c, s in product(range(5), repeat=2))
                    and F(19, 648)-F(1, 135) == self.R4,
                    'Normalized source table and removal of exactly one assigned135 tail summand')
            self.branch_lps = {branch: extended(self.lp, self.common.wi, pre, branch) for branch in BRANCHES}
            self.objective_branches = {}
            for t, w, m, ell, v in product(range(1, 9), sorted(set(self.common.wi)),
                                            range(5), range(3), range(1, 12)):
                require(F(self.depth.raw[t, w, (m, ell)][v], self.depth.scale)
                        ==F(w, 5)*max(v-t, 0)+self.increment(t, v, m, ell),
                        'Complete raw/survivor separation through the new maximum load11')

        def dual_upper(self, integers, factor):
            require(len(integers) == 2100, 'Every original and independent135 objective column')
            group = sha256(json.dumps([str(factor), integers], separators=(',', ':')).encode()).hexdigest()
            keys, values = {}, []
            objective = [factor*x for x in integers]
            for branch, lp in self.branch_lps.items():
                key = sha256(json.dumps([group, branch], separators=(',', ':')).encode()).hexdigest()
                if key not in self.verified:
                    if key not in self.bank:
                        require(self.proposer is not None, 'Missing retained135 rational branch dual '+key)
                        self.bank[key] = self.proposer(lp, objective)
                    self.verified[key] = lp.check_dual(objective, self.bank[key])
                self.used.add(key)
                keys[branch] = key
                values.append(self.verified[key])
            self.objective_branches[group] = keys
            return max(values), group

        def scan(self, coefficients):
            result = whole_hinge_scan(self, coefficients)
            witness = result['maximizing_witness']
            witness['nested_disjoint_dual_keys'] = self.objective_branches[witness['dual_key']]
            result['branch_rule'] = 'max(nested,disjoint), each a complete rational dual upper'
            return result

    return Retained135Head


def whole_hinge_scan(self, coefficients):
    depth, p, cc, b = self.depth, self.parent, self.common, self.bridge
    old, new = depth.prepare(coefficients)
    ints = old['primitive_coefficients']
    policy = {t: (0 if t == 1 else 5) for t in ints}
    policy_constant = b.integer(depth.total*sum(c*(self.R0 if t == 1 else self.R4)
                                              +c*self.Z for t, c in ints.items()))
    scale = old['factor']/depth.total
    raw_scale = old['factor']/depth.scale
    lookup = {(w, m, ell, v): (
        [sum(ct*(depth.raw[t, w, (m, ell)][v+(mask.bit_count() if t>=2 else 0)]
            -b.integer(depth.scale*F(w,5))*max(v+(mask.bit_count() if t>=2 else 0)-t,0))
            for t,ct in ints.items()) for mask in range(16)],
        [depth.scale*sum(ct*max(v+(mask.bit_count() if t>=2 else 0)-t,0)
            for t,ct in ints.items()) for mask in range(16)])
        for w, m, ell, v in product(sorted(set(cc.wi)), range(5), range(3), range(1, 7))}
    def added(w,m,ell,v):
        raw=[];surv=[]
        for mask in range(16):
            k=v+mask.bit_count()
            raw.append(sum(ct*(depth.raw[t,w,(m,ell)][k+1]-depth.raw[t,w,(m,ell)][k]
                -b.integer(depth.scale*F(w,5))*int(k>=t))for t,ct in ints.items()if t>=2))
            surv.append(depth.scale*sum(ct*int(k>=t)for t,ct in ints.items()if t>=2))
        return raw,surv
    extra_lookup={key:added(*key)for key in lookup}
    best, witness, digest = F(-1), None, sha256()
    counts = {'two': 0, 'two_bounded': 0, 'four': 0, 'four_bounded': 0,
              'six': 0, 'six_bounded': 0, 'joint': 0, 'prefix_available': 0, 'prefix_bounded': 0}
    maxima = {k: F(-1) for k in ('two', 'four', 'six', 'prefix')}
    lp_start, dual_start = p.lp_count, len(self.used)
    def record_decision(value):
        digest.update(json.dumps(encode(value), separators=(',', ':')).encode())
    def joint(layout, B, cor, projections, first, second, two, four, six, seed=False):
        nonlocal best, witness
        integers = [value for w, m, ell, v in zip(cc.wi, first, second, B)
                    for value in lookup[w, m, ell, v][0]]+[0]*25+[
                    value for w,m,ell,v in zip(cc.wi,first,second,B)
                    for value in lookup[w,m,ell,v][1]]+[0]*450+[
                    value for w,m,ell,v in zip(cc.wi,first,second,B)
                    for value in extra_lookup[w,m,ell,v][0]]+[
                    value for w,m,ell,v in zip(cc.wi,first,second,B)
                    for value in extra_lookup[w,m,ell,v][1]]+[0]*25
        original_integers = [sum(ct*depth.raw[t, w, (m, ell)][
            v+(mask & ((1 << cc.prefix[t])-1)).bit_count()] for t, ct in ints.items())
            for w, m, ell, v in zip(cc.wi, first, second, B) for mask in range(16)]
        prefix_raw, prefix_key = self.prior_prefix_upper(original_integers, raw_scale)
        prefix_upper = None if prefix_raw is None else prefix_raw+scale*(new['constant']-cor)
        if prefix_upper is not None:
            counts['prefix_available'] += 1
            if not seed and min(scale*two, scale*four, scale*six, prefix_upper) <= best:
                bounded = min(scale*two, scale*four, scale*six, prefix_upper)
                counts['prefix_bounded'] += 1
                maxima['prefix'] = max(maxima['prefix'], bounded)
                record_decision(['prefix', layout, projections, prefix_key, prefix_upper])
                return
        raw_upper, key = self.dual_upper(integers, raw_scale)
        upper = raw_upper+scale*policy_constant
        accepted = min(scale*two, scale*four, scale*six, upper)
        if prefix_upper is not None:
            accepted = min(accepted, prefix_upper)
        counts['joint'] += 1
        record_decision(['seed' if seed else 'joint', layout, projections, two, four, six, key, upper])
        if accepted > best:
            best = accepted
            witness = {'layout': layout, 'projections21_35_63_105_147_245': projections,
                'two_projection_upper': scale*two, 'four_projection_upper': scale*four,
                'six_projection_upper': scale*six, 'joint_raw_upper': raw_upper,
                'complete_tail_constant': scale*policy_constant, 'prior_prefix_upper': prefix_upper, 'mean_credit_outside_lp': F(0), 'whole_hinge_deletion_credit_in_pruning': scale*cor,
                'joint_complete_upper': upper, 'accepted_upper': accepted, 'dual_key': key}
    seed = (1, 3, 2, 1, 2, 3, 2)
    B = b.head_load(seed)
    def correction(layout):
        values = [sum(a*max(v-t, 0) for t, a in ints.items()) for v in b.head_load(layout)]
        q = (F(0), F(1,5), F(1,5), F(3,20), F(1,5))
        eta = (F(1,18), F(1,9), F(1,9), F(1,9), F(1,9))
        pure3 = sum(q[s]/135*values[5+s]+(q[s]/90-q[s]/135)*min(values[s], values[5+s])
                    for s in range(5))
        pure5 = sum(eta[c]*(1+int(c>=2))/100*min(values[5*c:5*c+5]) for c in range(5))
        credit = pure3+pure5
        require(credit >= ints.get(1, 0)*p.mean.correction(layout),
                'Whole-hinge deletion dominates the old first-hinge correction')
        return b.integer(depth.total*credit)
    cor = correction(seed)
    rt, st, extra = next(v for v in p.extras if v[:2] == (1, 2))
    c63, r105, s105, added = next(v for v in p.added if v[:3] == (3, 1, 2))
    first = [a+d for a, d in zip(extra, added)]
    r147, s245, second = rt, st, extra
    two, _ = p.objective(old, B, extra, cor, False)
    four, _ = p.objective(old, B, first, cor, True)
    six, _ = p.objective(new, B, list(zip(first, second)), cor, True)
    joint(seed, B, cor, (rt, st, c63, r105, s105, r147, s245), first, second, two, four, six, True)
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        B, cor = b.head_load(layout), correction(layout)
        for rt, st, extra in p.extras:
            two, _ = p.objective(old, B, extra, cor, False)
            counts['two'] += 1
            if scale*two <= best:
                counts['two_bounded'] += 1
                maxima['two'] = max(maxima['two'], scale*two)
                record_decision(['two', layout, rt, st, two])
                continue
            for c63, r105, s105, added in p.added:
                first = [a+d for a, d in zip(extra, added)]
                four, _ = p.objective(old, B, first, cor, True)
                counts['four'] += 1
                if scale*min(two, four) <= best:
                    counts['four_bounded'] += 1
                    maxima['four'] = max(maxima['four'], scale*min(two, four))
                    record_decision(['four', layout, rt, st, c63, r105, s105, two, four])
                    continue
                for r147, s245, second in p.extras:
                    six, _ = p.objective(new, B, list(zip(first, second)), cor, True)
                    counts['six'] += 1
                    projections = (rt, st, c63, r105, s105, r147, s245)
                    if scale*min(two, four, six) <= best:
                        counts['six_bounded'] += 1
                        maxima['six'] = max(maxima['six'], scale*min(two, four, six))
                        record_decision(['six', layout, projections, two, four, six])
                        continue
                    joint(layout, B, cor, projections, first, second, two, four, six)
    require(counts['two'] == 125000
            and counts['four'] == 50*(counts['two']-counts['two_bounded'])
            and counts['six'] == 10*(counts['four']-counts['four_bounded'])
            and counts['joint']-1+counts['prefix_bounded'] == counts['six']-counts['six_bounded'],
            'Every containing branch is evaluated or has a complete certified upper')
    require(500*counts['two_bounded']+10*counts['four_bounded']
            +counts['six_bounded']+counts['prefix_bounded']+counts['joint']-1 == 62500000,
            'All62,500,000 original containing choices per independent cost')
    require(witness is not None and all(maxima[k] <= best for k in maxima),
            'Every pruned upper remains below the final maximum of accepted candidates')
    require(p.lp_count-lp_start == 3+counts['two']+counts['four']+counts['six'],
            'All old rational capacity LP evaluations accounted for')
    return {'pruning_credit': 'whole-hinge-deletion', 'coefficients': coefficients, 'selected_prefix_lengths': policy, 'complete_hinge_upper': best, 'counts': counts,
        'unique_dual_certificates': len(self.used)-dual_start, 'covered_containing_choices': 62500000,
        'source_capacity_lp_count': p.lp_count-lp_start, 'maximum_pruned_uppers': maxima,
        'maximizing_witness': witness, 'branch_decisions_sha256': digest.hexdigest()}


def calculate(base, bank=None, proposer=None):
    io = module('retained135_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/retained-transport/selected_deletion_mask_heavy_comparison.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent inherited source '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    load = lambda name: module('retained135_'+name, io.named_artifact(base/'frontier', name+'.py'))
    original = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in original.pins.items()), 'Complete original52-cost inventory')
    old_costs, weights = [list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights')]
    D, L, Q = [F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper')]
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(8201, 1800))
            and prior['r'] == prior['rho'] == '0', 'Same two complete actual saturated K faces')
    problem = retained135_head_class(base)(base, bank, proposer)
    direct, records = list(old_costs), []
    for index in (0, 16):
        tag = original.specs[index]['tag']
        f = lambda n: original.source.zero5_cost(tag, n)
        coefficients = {1: f(2)-f(1)} | {t: f(t+1)-2*f(t)+f(t-1) for t in range(2, 9)}
        degree, leading, constant, cutoff = original.source.zero5_cost_metadata(tag)
        expansion = lambda n: f(1)+sum(a*max(n-t, 0) for t, a in coefficients.items())
        require(degree == 1 and cutoff == 8 and min(coefficients.values()) >= 0
                and all(expansion(n) == f(n) for n in range(1, 10))
                and sum(coefficients.values()) == leading
                and f(1)-sum(t*a for t, a in coefficients.items()) == constant,
                'Original heavy function on every positive integer, including its entire affine tail')
        print('Scanning complete retained135 heavy'+str(index)+' over62,500,000 original choices.', flush=True)
        scan = problem.scan(coefficients)
        bound = scan['complete_hinge_upper']+f(1)*D
        require(0 < bound < old_costs[index], 'Strict complete original heavy improvement')
        direct[index] = bound
        records.append({'index': index, 'tag': tag, 'at_one': f(1), 'previous_cost_upper': old_costs[index],
                        'cost_upper': bound, 'scan': scan})
        print('Checked complete retained135 heavy'+str(index)+': '+str(float(bound))+', '
              +str(scan['counts']['joint'])+' two-branch dual uses; '
              +str(scan['source_capacity_lp_count'])+' exact capacity LPs.', flush=True)
    if proposer is None:
        require(set(problem.bank) == problem.used, 'Every stored branch dual is used and checked')
    retained = {key: problem.bank[key] for key in sorted(problem.used)}
    encoded_bank = encode_dual_bank(retained)
    require(decode_dual_bank(encoded_bank) == retained, 'Exact lossless recovery of every retained dual entry')
    tags = [s['tag'] for s in original.specs+original.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    require(encode(tags) == prior['original_cost_tags'] and len(tags) == len(old_costs) == len(weights) == 52
            and prior['all_original_indices'] == list(range(52)) and min(weights) > 0,
            'All222 original independent labels and positive weights retained')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda n, tag=tag: original.source.zero5_cost(tag, n) for tag in all_tags]
    metadata = [original.source.zero5_cost_metadata(tag) for tag in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = [F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight')]
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    require(signed < 0 < square_weight and oldN == F(prior['numerator_upper']) > N > 0
            and all(0 <= b <= a for a, b in zip(old_costs, costs)), 'One complete stronger signed52-cost numerator')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(sum(F(r['joint_mean_upper'])
        for r in prior['AP11_block_results'])+F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) > 0
            and F(prior['uniform_hinge4_upper']) == 6*F(prior['standalone_hinge4_penalty'])
            == F(prior['AP13_result']['hinge_upper']), 'Every independent survival test and full count tail retained')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper'])
            and comparison < F(prior['comparison_upper']), 'Complete improved face comparison')
    return encode({'schema': 'erdos7-retained135-heavy-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L, 'complete_square_upper': Q,
        'branch_lps': {branch: lp.specification() for branch, lp in problem.branch_lps.items()},
        'encoded_rational_duals': encoded_bank,
        'selected_policy': {1: [], **{t: [25, 27, 75, 81, 135] for t in range(2, 9)}},
        'assigned135_surviving_cap': F(1, 135), 'remaining_old_tail_t_ge2': problem.R4,
        'previous_prefix_duals_used': sorted(problem.prior_used), 'heavy_results': records,
        'all_original_indices': list(range(52)), 'original_cost_tags': tags, 'cost_weights': weights,
        'previous_cost_bounds': old_costs, 'direct_cost_bounds': direct, 'improved_cost_bounds': costs,
        'majorants': majorants, 'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'previous_numerator_upper': oldN, 'numerator_upper': N, 'numerator_improvement': oldN-N,
        'AP11_block_results': prior['AP11_block_results'], 'AP13_result': prior['AP13_result'],
        'uniform_hinge4_upper': prior['uniform_hinge4_upper'], 'full_count_tail': prior['full_count_tail'],
        'standalone_hinge4_penalty': prior['standalone_hinge4_penalty'],
        'uniform_denominator_lower': denominator, 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'scope': 'Both complete actual saturated K faces. One independent original135 residue is retained as raw and surviving submeasures of the four original selected masks. Both nested and disjoint27/81 branches remain. Every62,500,000 original head/seven-projection choice is evaluated or has a complete certified alternative for each heavy cost. All2100 rational dual columns, all52 independent original costs, signed actual mass, the complete square, independent222 survival tests and all infinite tails remain. No common optimizer across costs, actual-family attainment, off-face/global extension, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = module('retained135_reader', args.base/'certificate_io.py')
    expected = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))
    result = calculate(args.base, decode_dual_bank(expected['encoded_rational_duals']))
    require(result == expected, 'Exact complete retained135 certificate')
    print('PASS: both complete heavy scans, all2100 dual columns and52-cost face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
