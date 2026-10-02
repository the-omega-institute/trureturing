"""Small exact controls for extending the common-5 union across 5 depths.

Uses the fixed FC36 profile and the original 85 pure/star phase source.
No solver, full-period enumeration, or claim of a complete mixed realization.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import prod
from pathlib import Path
import json

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input', required=True)
ap.add_argument('--output', required=True)
args = ap.parse_args()
raw = Path(args.input).read_bytes()
x = json.loads(raw)
Q = x['primes']
h = dict(zip(Q, x['heights']))
selected = dict(x['selected_witness'])
c = {q: F((q-1)*q**h[q], (q-2)*q**h[q]+1) for q in Q}
checks = 0

def need(ok, message):
    global checks
    checks += 1
    if not ok:
        raise ValueError(message)

need(Q == [5,7,11,13,17,19,23,29,31,37,41], 'Fixed prime support')
need(x['heights'] == [5,5,4,4,4,4,4,3,3,3,3], 'Fixed heights')
need(all(t == (1 if q == 5 else 2) for q,e,t in x['star_roots']), 'Fixed star roots')
records = []
full = F(0)
shallow = F(0)
deep = F(0)
counts = {'shallow_free': 0, 'shallow_selected': 0, 'deep_free': 0, 'deep_selected': 0}
for q in Q:
    if q == 5:
        continue
    raw_lift = F(0)
    weighted_average = F(0)
    depths = []
    for a in range(1,h[5]+1):
        es = [e for e in range(1,h[q]+1) if selected.get(5**a*q**e)==1]
        budget = c[q]*(sum((F(1,q**e) for e in range(1,h[q]+1)),F(0))
                       +sum((F(1,q**e) for e in es),F(0)))
        charge = c[5]/5**a*budget
        raw_lift += budget
        weighted_average += budget/5**(a-1)
        full += charge
        tag = 'shallow' if a == 1 else 'deep'
        counts[tag+'_free'] += h[q]
        counts[tag+'_selected'] += len(es)
        if a == 1:
            shallow += charge
        else:
            deep += charge
        depths.append({'five_depth':a,'selected_q_depths':es,
                       'q_budget':str(budget),'independent_charge':str(charge)})
    records.append({'q':q,'depths':depths,'raw_first_root_lift':str(raw_lift),
                    'weighted_first_root_average':str(weighted_average)})
need(counts == {'shallow_free':37,'shallow_selected':28,'deep_free':148,'deep_selected':20},
     'Full support-pair original inventory split')
raw_product = prod(1-min(F(1),F(r['raw_first_root_lift'])) for r in records)
need(raw_product == 0, 'Unweighted ancestor lifting loses the product improvement')
old_shallow_upper = F(1175,4688)
baseline = old_shallow_upper + deep
carrier = 2-c[5]
need(full == shallow+deep and baseline < full < carrier, 'Group comparison and remaining carrier')

def overlap(q,e,a,f,b):
    return F(1,q**max(e,f)) if (a-b)%q**min(e,f)==0 else F(0)

def holes(q):
    pure = [(e,0 if e==1 else 1+q**(e-1)) for e in range(1,h[q]+1)]
    # Original separated-hole FC36 source, not the concentrated FC44 one.
    star = [(e,2 if e==1 else 3+q**(e-1)) for e in range(1,h[q]+1)] if q==5 else []
    return pure+star

for q in (5,7,11):
    for (e,a),(f,b) in combinations(holes(q),2):
        need(overlap(q,e,a,f,b)==0,'One actual source has disjoint coordinate holes')

def available(q,e,a):
    return c[q]*(F(1,q**e)-sum((overlap(q,e,a,f,b) for f,b in holes(q)),F(0)))

def crt(spec):
    a,m = 0,1
    for n,b in spec:
        a += m*((b-a)*pow(m,-1,n)%n)
        m *= n
    return {'modulus':m,'residue':a}

w = available(5,2,4)
alpha = available(7,1,4)
beta = available(11,1,4)
need(w == available(5,2,9) == available(5,2,16) == c[5]/25,
     'Three literal full-cap depth-two 5 prefixes in the same old source')
need(available(5,1,4)==c[5]/5 and alpha==c[7]/7 and beta==c[11]/11,
     'Actual common source gives exact coordinate caps')
need(selected[25*7]==selected[25*11]==1, 'Both deep labels belong to the declared root1 palette')
A = crt([(3,1),(25,4),(7,4)])
B_same = crt([(3,1),(25,4),(11,4)])
B_separate = crt([(3,1),(25,9),(11,4)])
same = w*(alpha+beta-alpha*beta)
separate = w*(alpha+beta)
collapsed = c[5]/5*(alpha/5+beta/5-alpha*beta/25)
need(same < collapsed < separate, 'Product of first-root averages is not a valid union upper bound')
gap = separate-collapsed
need(gap == F(79893275,432601753328), 'Exact averaging counterexample gap')

parent = crt([(5,4),(11,4)])
D_nested = A
D_separate = crt([(3,1),(25,16),(7,4)])
epsilon = w*alpha*beta
need(epsilon == F(399466375,432601753328), 'Conditional additional intersection credit')
need(D_nested['residue']%5==parent['residue']%5 and
     D_separate['residue']%5!=parent['residue']%5,
     'The same deep label can be nested or separated while keeping its cap')
need(available(5,2,16)==w, 'Separated descendant keeps the same actual marginal mass')

result = {
 'contract':'Fixed FC36 source/profile and numerical inventory diagnostics; exact common-prefix '
            'interface and counterexamples. No source-uniform full-pair gain beyond the prior '
            'shallow credit is asserted. New overlap credit is conditional on a certified '
            'actual ancestor relation and source masses.',
 'input':args.input,'input_sha256':sha256(raw).hexdigest(),'counts':counts,'q_records':records,
 'full_pair_independent_charge':str(full),'shallow_independent_charge':str(shallow),
 'deep_independent_charge':str(deep),'existing_shallow_union_upper':str(old_shallow_upper),
 'existing_full_pair_upper':str(baseline),'carrier':str(carrier),'unused_carrier':str(carrier-baseline),
 'raw_first_root_clipped_product':str(raw_product),
 'first_root_average_counterexample':{
   'A':A,'B_same_child':B_same,'B_separate_child':B_separate,
   'source':'Original FC36 85-class pure/star source, conditioned on ternary root1.',
   'same_child_union':str(same),'separate_child_union':str(separate),
   'product_of_averages':str(collapsed),'underestimate_in_separated_case':str(gap),
   'scope':'These add two literal odd classes to the same pure/star source; '
           'not a full divisor-closed mixed inventory or a globally minimal cover.'},
 'cross_depth_condition':{
   'shallow_parent':parent,'deep_nested':D_nested,'deep_separate':D_separate,
   'nested_overlap':str(epsilon),'separated_overlap':'0',
   'overlap_pair':'The specified shallow_parent A0 with the indicated deep original; separated_overlap is not the overlap with the whole shallow union A.',
   'new_full_pair_upper_if_condition_certified':str(baseline-epsilon),
   'rule':'Union(shallow,deep) <= U_shallow + sum(deep caps) - epsilon '
          'if one deep event has actual overlap at least epsilon with the shallow union.'},
 'decimals':{k:float(v) for k,v in [('full_pair_charge',full),('deep_charge',deep),
               ('existing_upper',baseline),('conditional_new_upper',baseline-epsilon),
               ('conditional_credit',epsilon),('averaging_underestimate',gap)]},
 'checks':checks,
}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'counts':counts,'decimals':result['decimals']},sort_keys=True))
