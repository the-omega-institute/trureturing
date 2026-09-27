#!/usr/bin/env python3
"""Common raw source, actual survivor and two complete extra deleted measures."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/retained_deletion_heavy_comparison.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/moments-survival/all_selected_survival_comparison.py': '87c2e1de36092d35e0b7778cfdef2c1029b7e27e9c4a6b1b3558b7870792b835', 'certificates/source_norms/moments-survival/all_selected_survival_comparison.json': 'd22dd6fd914cb4e8238e3c5e7b0e50b25c9602e98f20b9fea9ce146238f1ce99'}


def require(condition,message):
    if not condition:
        raise ValueError(message)


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(v):
    if isinstance(v,F): return str(v)
    if isinstance(v,dict): return {str(k):encode(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)): return [encode(x) for x in v]
    return v


class RetainedDeletionLP:
    """Every actual configuration embeds; relaxed measures need not be realizable."""
    def __init__(self,raw,wi):
        self.nvars=875
        self.rows,self.rhs=[dict(r) for r in raw.rows],list(raw.rhs)
        self.equalities=[dict(r) for r in raw.equalities]
        self.erhs=[F(1)]*4
        self.lambda_groups=raw.lambda_groups
        self.y_link=[]
        def add(row,rhs):
            self.rows.append(row);self.rhs.append(rhs)
            return len(self.rows)-1
        for cell,w in enumerate(wi):
            for mask in range(16):
                k=16*cell+mask
                self.y_link.append(add({425+k:F(1),k:-F(w,5)},F(0)))
        self.equalities += [{425+k:F(1) for k in range(400)}, {k:F(1) for k in range(400)}]
        self.erhs += [F(53,360), F(1,4)]
        self.selected_caps=(F(2,125),F(7,270),F(4,375),F(7,810))
        for bit,cap in enumerate(self.selected_caps):
            add({425+16*cell+mask:F(1) for cell in range(25) for mask in range(16)
                if mask>>bit&1},cap)
        self.e3_zero={}
        for cell,w in enumerate(wi):
            row={825+cell:F(1),850+cell:F(1)}
            for mask in range(16):
                row[16*cell+mask]=-F(w,5);row[425+16*cell+mask]=F(1)
            add(row,F(0))
            if cell//5>=2:
                self.e3_zero[825+cell]=add({825+cell:F(1)},F(0))
        q=(F(0),F(1,5),F(1,5),F(3,20),F(1,5))
        eta=(F(1,18),F(1,9),F(1,9),F(1,9),F(1,9))
        for s in range(5):
            self.equalities.append({825+s:F(1),830+s:F(1)});self.erhs.append(q[s]/90)
            add({830+s:-F(1)},-q[s]/135)
        for c in range(5):
            self.equalities.append({850+5*c+s:F(1) for s in range(5)})
            self.erhs.append(eta[c]*(1+int(c>=2))/100)
        self.columns=[[] for _ in range(self.nvars)]
        self.eqcolumns=[[] for _ in range(self.nvars)]
        for i,row in enumerate(self.rows):
            for k,a in row.items():self.columns[k].append((i,a))
        for i,row in enumerate(self.equalities):
            for k,a in row.items():self.eqcolumns[k].append((i,a))
        require(len(self.rows)==581 and len(self.equalities)==16,'Complete875-variable source/survivor/deletion system')
        self.raw_spec=raw.specification()

    def check_dual(self,objective,record):
        require(len(objective)==self.nvars,'Every original and added objective column')
        y=[F(0)]*len(self.rows)
        for k,v in record['nonzero_inequality_duals'].items():
            i=int(k);require(str(i)==str(k) and 0<=i<len(y),'Canonical dual row')
            y[i]=F(v)
        z=list(map(F,record['equality_duals']))
        require(len(z)==len(self.equalities) and min(y)>=0,'Nonnegative inequalities; free equality prices')
        for k in range(self.nvars):
            lhs=sum((a*y[i] for i,a in self.columns[k]),F(0))+sum((a*z[i] for i,a in self.eqcolumns[k]),F(0))
            require(lhs>=objective[k],'Feasible rational dual column '+str(k))
        val=sum((a*v for a,v in zip(self.rhs,y)),F(0))+sum((a*v for a,v in zip(self.erhs,z)),F(0))
        require(val==F(record['raw_objective_upper']),'Exact common-measure objective bound')
        return val

    def specification(self):
        return encode({'variables':self.nvars,'raw_mass_variables':400,'survivor_variables':400,
            'projection_mixture_variables':25,'extra_deletion_variables':50,
            'inequalities':len(self.rows),'equalities':len(self.equalities),'original_raw_lp':self.raw_spec,
            'selected_survivor_caps':self.selected_caps,
            'rows_sha256':sha256(json.dumps(encode([self.rows,self.rhs,self.equalities,self.erhs]),sort_keys=True,separators=(',',':')).encode()).hexdigest()})


class RetainedDeletionHead:
    R0,R4,Z=F(163,1800),F(19,648),F(2669,88200)
    def __init__(self,base,bank=None,proposer=None):
        old=module('retained_allselected',base/'frontier/source-budgets/all_selected_heavy_comparison.py').AllSelectedHead(base)
        self.depth,self.parent,self.bridge,self.common=old.depth,old.parent,old.bridge,old.common
        self.rawlp=old.lp
        self.lp=RetainedDeletionLP(self.rawlp,self.common.wi)
        self.prior_bank,self.prior_verified,self.prior_used=old.prior_bank,{},set()
        self.bank={} if bank is None else bank
        self.proposer,self.used,self.verified=proposer,set(),{}
        self.increment=module('retained_increment',base/'frontier/comparison-bounds/second_depth_seven_comparison.py').seven_increment
        # Verify the integer compiler really separates the survivor hinge from the raw increment.
        for t,w,m,ell,v in product(range(1,9),sorted(set(self.common.wi)),range(5),range(3),range(1,11)):
            require(F(self.depth.raw[t,w,(m,ell)][v],self.depth.scale)
                    ==F(w,5)*max(v-t,0)+self.increment(t,v,m,ell),
                    'Exact raw/survivor separation at every retained integer load')

    def prior_prefix_upper(self,integers,factor):
        key=sha256(json.dumps([str(factor),integers],separators=(',',':')).encode()).hexdigest()
        if key not in self.prior_bank:return None,None
        if key not in self.prior_verified:
            self.prior_verified[key]=self.rawlp.check_dual([factor*x for x in integers]+[F(0)]*25,self.prior_bank[key])
        self.prior_used.add(key)
        return self.prior_verified[key],key

    def dual_upper(self,integers,factor):
        key=sha256(json.dumps([str(factor),integers],separators=(',',':')).encode()).hexdigest()
        if key not in self.verified:
            objective=[factor*x for x in integers]
            if key not in self.bank:
                require(self.proposer is not None,'Missing rational deletion dual '+key)
                self.bank[key]=self.proposer(self.lp,objective)
            self.verified[key]=self.lp.check_dual(objective,self.bank[key])
        self.used.add(key)
        return self.verified[key],key

    def scan(self, coefficients):
        depth, p, cc, b = self.depth, self.parent, self.common, self.bridge
        old, new = depth.prepare(coefficients)
        ints = old['primitive_coefficients']
        policy = {t: (0 if t == 1 else 4) for t in ints}
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
                        for value in lookup[w,m,ell,v][1]]+[0]*50
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
                    'complete_tail_constant': scale*policy_constant, 'prior_prefix_upper': prefix_upper, 'mean_credit_outside_lp': F(0), 'original_mean_credit_in_pruning': scale*cor,
                    'joint_complete_upper': upper, 'accepted_upper': accepted, 'dual_key': key}
        seed = (1, 3, 2, 1, 2, 3, 2)
        B = b.head_load(seed)
        correction = lambda layout: ints.get(1, 0)*b.integer(depth.total*p.mean.correction(layout))
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
        return {'coefficients': coefficients, 'selected_prefix_lengths': policy, 'complete_hinge_upper': best, 'counts': counts,
            'unique_dual_certificates': len(self.used)-dual_start, 'covered_containing_choices': 62500000,
            'source_capacity_lp_count': p.lp_count-lp_start, 'maximum_pruned_uppers': maxima,
            'maximizing_witness': witness, 'branch_decisions_sha256': digest.hexdigest()}



def bucket_duals(bank):
    buckets={}
    for key,record in sorted(bank.items()):buckets.setdefault(key[0],{}).setdefault(key[1],{})[key]=record
    return buckets


def flatten_duals(buckets):
    result={}
    for a,sub in buckets.items():
        require(len(a)==1 and a in '0123456789abcdef','First dual bucket')
        for b,records in sub.items():
            require(len(b)==1 and b in '0123456789abcdef','Second dual bucket')
            for key,value in records.items():
                require(key.startswith(a+b) and key not in result,'Unique matching dual key')
                result[key]=value
    return result


def calculate(base, bank=None, proposer=None):
    io = module('joint_selected_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/moments-survival/all_selected_survival_comparison.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent complete inherited source '+path)
        pins[path] = pin
    # The second-depth source is already inherited; require its actual presence.
    require('frontier/comparison-bounds/second_depth_seven_comparison.py' in pins, 'Pinned complete two-depth bridge')
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('joint_selected_'+name, io.named_artifact(base/'frontier', name+'.py'))
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in engine.pins.items()), 'All original independent52 costs')
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require(D == F(53, 360) and Q == F(8201, 1800) and prior['r'] == prior['rho'] == '0',
            'Same complete saturated actual faces and actual mass')
    problem = RetainedDeletionHead(base, bank, proposer)
    direct, records = list(old_costs), []
    for i in (0, 16):
        tag = engine.specs[i]['tag']
        f = lambda n: engine.source.zero5_cost(tag, n)
        co = {1: f(2)-f(1)} | {t: f(t+1)-2*f(t)+f(t-1) for t in range(2, 9)}
        degree, leading, constant, cutoff = engine.source.zero5_cost_metadata(tag)
        expand = lambda n: f(1)+sum(c*max(n-t, 0) for t, c in co.items())
        require(degree == 1 and cutoff == 8 and min(co.values()) >= 0
                and all(expand(n) == f(n) for n in range(1, 10))
                and sum(co.values()) == leading and f(1)-sum(t*c for t, c in co.items()) == constant,
                'Original heavy cost on every integer load, including its complete affine tail')
        scan = problem.scan(co)
        bound = scan['complete_hinge_upper']+f(1)*D
        require(0 < bound < old_costs[i], 'Strict complete original heavy-cost improvement')
        direct[i] = bound
        records.append({'index': i, 'tag': tag, 'at_one': f(1), 'previous_cost_upper': old_costs[i],
                        'cost_upper': bound, 'scan': scan})
        print('Checked heavy'+str(i)+': '+str(float(bound))+', '
              +str(scan['counts']['joint'])+' rational joint dual uses.', flush=True)
    require(set(problem.bank) == problem.used, 'Every stored dual is used; no unverified or unused proposal records')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    require(encode(tags) == prior['original_cost_tags'] and len(tags) == len(old_costs) == len(weights) == 52
            and prior['all_original_indices'] == list(range(52)), 'Every original214 test label retained')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda n, tag=t: engine.source.zero5_cost(tag, n) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    require(oldN == F(prior['numerator_upper']) and all(0 <= b <= a for a, b in zip(old_costs, costs))
            and 0 < N < oldN, 'Complete signed52-cost numerator retains every214 improvement')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) > 0,
            'All214 AP11/AP13 denominator terms and complete count tail retained')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper'])
            and 403 < comparison < F(prior['comparison_upper']), 'Strict face improvement, still above403')
    return encode({'schema': 'erdos7-retained-deletion-heavy-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L, 'complete_square_upper': Q,
        'raw_lp': problem.lp.specification(), 'selected_policy': {1: [], **{t: [25,27,75,81] for t in range(2,9)}},
        'assigned_selected_survivor_caps': problem.lp.selected_caps, 'complete_old_remainder_for_t_ge2': problem.R4,
        'previous_prefix_duals_used': sorted(problem.prior_used), 'rational_dual_buckets': bucket_duals(problem.bank),
        'heavy_results': records, 'all_original_indices': list(range(52)), 'original_cost_tags': tags,
        'cost_weights': weights, 'previous_cost_bounds': old_costs, 'direct_cost_bounds': direct,
        'improved_cost_bounds': costs, 'majorants': majorants,
        'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'numerator_upper': N, 'numerator_improvement': oldN-N, 'AP11_block_results': prior['AP11_block_results'],
        'AP13_result': prior['AP13_result'], 'uniform_hinge4_upper': prior['uniform_hinge4_upper'],
        'full_count_tail': prior['full_count_tail'], 'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
        'uniform_denominator_lower': denominator, 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'scope': 'Ordinary complete heavy-cost theorem with one raw source, one actual survivor and two distinct complete extra deletion measures. No mean credit is subtracted outside the common LP. The domain is both whole actual saturated K faces. Every threshold above one retains all four original selected labels in one raw-source LP; threshold one keeps its empty prefix; its deletion credit is inside the LP. Earlier original-prefix bounds remain valid pruning options. Every62,500,000 containing choices per cost is checked or safely bounded. Rational feasible duals suffice; numerical optimality and actual attainment are not claimed. All52 costs and infinite tails remain. No off-face/global, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = module('joint_selected_reader', args.base/'certificate_io.py')
    expected = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))
    result = calculate(args.base, flatten_duals(expected['rational_dual_buckets']))
    require(result == expected, 'Exact canonical joint-source certificate')
    print('PASS: both complete heavy costs, all rational duals and52-cost face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
