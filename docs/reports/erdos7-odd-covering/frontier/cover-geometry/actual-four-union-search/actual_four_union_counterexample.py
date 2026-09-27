#!/usr/bin/env python3
"""Exact replay of a finite actual family crossing Report568's four fixed limits.

The input is one fixed table of nonzero current roots, indexed by numerical
old exponent tuples in lexicographic order. No optimization is performed.
All prefix masses, unions, CRT residues and comparisons use rational arithmetic.
This refutes only the universal disjunction of the four fixed limits.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import math

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input',type=Path,default=Path(__file__).with_suffix('.input.json'))
parser.add_argument('--reference',type=Path,default=Path(__file__).with_name('actual_root_union_consumers.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
data=json.loads(args.input.read_text())
reference=json.loads(args.reference.read_text())
checks={}
def ck(name,condition):
    if not condition or name in checks:
        raise ValueError(name)
    checks[name]=True

ck('input_contract',data['format']=='actual-four-union-colors-v1'
   and data['height']==2 and data['seed_old_roots']=={'11':[1,1],'13':[2,2]})
H=data['height']
caps={11:F(5,3),13:F(3,2),17:F(2),19:F(9,5)}
limits={11:5,13:6,17:9,19:10}
originals=[]
def original(primes,exponents,residues):
    factors=[p**e for p,e in zip(primes,exponents) if e]
    values=[r for e,r in zip(exponents,residues) if e]
    modulus=math.prod(factors)
    residue=sum(r*(modulus//m)*pow(modulus//m,-1,m)
                for m,r in zip(factors,values))%modulus
    if not all(residue%m==r for m,r in zip(factors,values)):
        raise ValueError('original CRT')
    entry={'modulus':modulus,'residue':residue,
           'prime_exponents':{str(p):e for p,e in zip(primes,exponents) if e}}
    originals.append(entry)
    return entry

for q in (11,13):
    old=data['seed_old_roots'][str(q)]
    for i,(a,b) in enumerate(((0,0),(1,0),(0,1),(1,1))):
        for j in (1,2):original((5,7,q),(a,b,1),(*old,2*i+j))

def initial_cells(p):
    # The two seed rows distinguish roots1 and2. All later old tests are zero.
    return ([(0,1,F(1,p)),(0,2,F(1,p)),(0,-1,F(p-3,p))]
            +[(v,0,F(p-1,p**(v+1))) for v in range(1,H)]
            +[(H,0,F(1,p**H))])

def allowed_valuation_cells(p,forbidden):
    # All forbidden cylinders are nonzero first roots, so the zero root and
    # its complete higher-digit tails remain available at every history.
    return ([(0,F(p-1-forbidden,p))]
            +[(v,F(p-1,p**(v+1))) for v in range(1,H)]
            +[(H,F(1,p**H))])

weights=defaultdict(F)
J11=F();J13=F();mass11=F();mass13=F()
for (v5,r5,w5),(v7,r7,w7) in product(initial_cells(5),initial_cells(7)):
    weight=w5*w7
    u11=2*(1+int(r5==1))*(1+int(r7==1))
    u13=2*(1+int(r5==2))*(1+int(r7==2))
    d11=min(caps[11],F(11,11-u11));d13=min(caps[13],F(13,13-u13))
    s11=d11*F(11-u11,11);s13=d13*F(13-u13,13)
    J11+=weight*max(u11-limits[11],0)
    J13+=weight*s11*max(u13-limits[13],0)
    mass11+=weight*s11;mass13+=weight*s11*s13
    for (v11,w11),(v13,w13) in product(allowed_valuation_cells(11,u11),
                                     allowed_valuation_cells(13,u13)):
        weights[v5,v7,v11,v13]+=weight*d11*w11*d13*w13
ck('initial_full_Haar_cells',all(sum((w for v,r,w in initial_cells(p)),F())==1 for p in (5,7)))
ck('seed_J11',J11==F(3,35))
ck('seed_J13',J13==F(2,35))
ck('seed_mass11',mass11==F(379,385))
ck('seed_mass13',mass13==F(9733,10010))
ck('seed_joint_partition',sum(weights.values(),F())==mass13)
rows={11:{'J_union':J11,'mass_after':mass11},13:{'J_union':J13,'mass_after':mass13}}

for q,old in ((17,(5,7,11,13)),(19,(5,7,11,13,17))):
    exponents=list(product(range(H+1),repeat=len(old)))
    roots=data['roots'][str(q)]
    ck('literal_root_table_'+str(q),len(roots)==len(exponents)
       and all(len(pair)==2 and len(set(pair))==2
               and all(type(r) is int and 1<=r<q for r in pair) for pair in roots))
    for exps,pair in zip(exponents,roots):
        for r in pair:original((*old,q),(*exps,1),(*([0]*len(old)),r))
    masks=[sum(1<<r for r in pair) for pair in roots]
    histogram=defaultdict(F);after=defaultdict(F);J=F();mass=F()
    for vals,weight in weights.items():
        mask=0
        for exps,rootmask in zip(exponents,masks):
            if all(a<=v for a,v in zip(exps,vals)):mask|=rootmask
        u=mask.bit_count()
        if mask&1 or u>=q:raise ValueError('retained zero root')
        density=min(caps[q],F(q,q-u))
        histogram[u]+=weight
        J+=weight*max(u-limits[q],0)
        mass+=weight*density*F(q-u,q)
        for v,w in allowed_valuation_cells(q,u):
            if w:after[(*vals,v)]+=weight*density*w
    ck('prefix_histogram_'+str(q),sum(histogram.values(),F())==sum(weights.values(),F()))
    ck('actual_mass_transport_'+str(q),sum(after.values(),F())==mass)
    ck('positive_subprobability_'+str(q),0<mass<=sum(weights.values(),F())<=1)
    rows[q]={'J_union':J,'mass_before':sum(weights.values(),F()),'mass_after':mass,
             'actual_union_root_histogram':dict(sorted(histogram.items()))}
    weights=after

counts=Counter(x['modulus'] for x in originals)
ck('all664_originals',len(originals)==664)
ck('all332_distinct_labels',len(counts)==332 and all(n==2 for n in counts.values()))
ck('different_residues_at_each_label',len({(x['modulus'],x['residue']) for x in originals})==664)
ck('odd_nonunit_moduli',all(m>1 and m%2 for m in counts))
ck('correct_numerical_factorization',all(x['modulus']==math.prod(int(p)**e for p,e in x['prime_exponents'].items()) for x in originals))
ck('exact_J17',rows[17]['J_union']==F(7996598579,62494802370))
ck('exact_J19',rows[19]['J_union']==F(350316280698322,3418309452633075))
finalmass=rows[19]['mass_after']
ck('exact_final_mass',finalmass==F(305834805525730823,324739398000142125))

corner=next(c for c in reference['PA_corners'] if F(c['x'])==F(c['y'])==1)
phi=F(corner['Phi']);target=F(257,51)
ck('complete_hinge_at_actual_parameters',phi==F(413209846699493,764619061606400))
for entry in reference['root_consumers']:
    q=entry['q']
    actual=next(c for c in entry['corners'] if F(c['x'])==F(c['y'])==1)
    fixed=F(entry['strict_root_excess_integral_threshold'])
    parameter=F(q)/caps[q]*(F(actual['alpha'])-phi/(target-2))
    rows[q].update({'fixed_threshold':fixed,'parameter_threshold':parameter,
                    'fixed_margin':rows[q]['J_union']-fixed,
                    'parameter_margin':rows[q]['J_union']-parameter})
    ck('crosses_fixed_limit_'+str(q),rows[q]['J_union']>fixed)
    ck('does_not_cross_parameter_limit_'+str(q),rows[q]['J_union']<parameter)
querybound=2+phi/finalmass
ck('complete_query_bound_still_below_target',querybound<target)
result={'statement':'A finite actual family refuting universal adequacy of the four fixed union-excess limits.',
        'source':{'x':'1','y':'1','lambda0':'1'},'rows':rows,'Phi':phi,
        'final_mass':finalmass,'complete_query_bound':querybound,
        'complete_query_bound_decimal':float(querybound),'target':target,
        'original_count':len(originals),'distinct_modulus_count':len(counts),'originals':originals,
        'input_sha256':hashlib.sha256(args.input.read_bytes()).hexdigest(),
        'reference_sha256':hashlib.sha256(args.reference.read_bytes()).hexdigest(),
        'checks':checks,'check_count':len(checks),
        'scope':'Every row uses the same fixed originals and the preceding actual unnormalized PA output. All later old exponent tests are retained. The actual law satisfies the target: this is not a PA failure, an all-laws lower witness, or a distinct-odd-modulus cover. Ordinary exact computation; no Lean.'}
args.output.write_text(json.dumps(result,default=lambda x:str(x),indent=2)+'\n')
for q,row in rows.items():print('q',q,'J',row['J_union'],'fixed_margin',row['fixed_margin'])
print('query_bound',querybound,float(querybound),'checks',len(checks))
