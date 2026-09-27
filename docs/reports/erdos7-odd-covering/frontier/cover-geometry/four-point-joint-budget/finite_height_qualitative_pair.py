"""Finite-height qualitative pair type(21,26,35), on the complete fixed chart.
Checks retained finite-budget witnesses and literal full-chart occurrences.
Standard library only. Ordinary proofs carry the all-height qualitative claim.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, permutations
from math import prod
from collections import Counter
import argparse, hashlib, json

ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir', type=Path, default=ROOT)
parser.add_argument('--certificate', type=Path)
parser.add_argument('--output', type=Path)
args=parser.parse_args()
cert_path=args.certificate or ROOT/'finite_height_qualitative_pair_certificate.json'
c=json.loads(cert_path.read_text())
def need(condition,message):
    if not condition: raise ValueError(message)
inputs={}
for name,digest in c['inputs'].items():
    raw=(args.input_dir/name).read_bytes()
    need(hashlib.sha256(raw).hexdigest()==digest,'pinned input '+name)
    inputs[name]=json.loads(raw)
r500=inputs['mixed_split_binary_support_barrier.json']
c500=inputs['mixed_split_binary_support_certificate.json']
r501=inputs['mixed_split_complete_weighted_boundary.json']
expected=c['expected_counts']
need(c['boundary_capacity']==[21,26,35], 'one named qualitative capacity type')
need(c500['reference']==[2,7,3,4] and c500['split_later_primes']==[7]
     and c500['common_later_primes']==[11,13,17,19], 'same old chart')
need(r500['certificate_sha256']==c['inputs']['mixed_split_binary_support_certificate.json'], '500 support input binding')
need(r501['base_result_sha256']==c['inputs']['mixed_split_binary_support_barrier.json'], '501 base result binding')

# Every one of500's190 retained representative capacity triples is covered.
base_rows=r500['pair_capacity_certificates']
base={(r['q'],r['r']):r['certified_capacity_lower'] for r in base_rows}
need(len(base_rows)==len(base)==expected['retained_capacity_classes']==190,'190 distinct retained representatives')
need(set(base)=={(q,r) for q in range(20,39) for r in range(q,39)},'complete retained load-class pairs')
H=c['finite_witness_height']
need(type(H) is int and H==3,'declared finite-budget witness height')
a=1-F(1,23**H);b=1-F(1,29**H)
zero_keys=set()
for witness in c['finite_zero_witnesses']:
    q,r,N=witness['q'],witness['r'],witness['N']
    key=(q,r)
    need(key in base and base[key]==N and key not in zero_keys,'finite witness representative identity')
    t=tuple(map(F,witness['axis23']));u=tuple(map(F,witness['axis29']))
    need(len(t)==len(u)==2,'two witness coordinates')
    need(all(0<=x<=min(F(22),a*Q) for x,Q in zip(t,(q,r))) and sum(t)<=a*N,'finite23 axis budgets')
    need(all(0<=x<=min(F(28),b*Q) for x,Q in zip(u,(q,r))) and sum(u)<=b*N,'finite29 axis budgets')
    residual=tuple((22-x)*(28-y) for x,y in zip(t,u))
    need(all(0<=x<=a*b*Q for x,Q in zip(residual,(q,r))) and sum(residual)<=a*b*N,'finite mixed individual and joint budgets')
    zero_keys.add(key)
need(len(zero_keys)==expected['finite_zero_witnesses']==189 and set(base)-zero_keys=={(21,26)} and base[(21,26)]==35,'unique exceptional retained type')
# The closed total-only and max-clipping minima at this exception are both0.
corner=[]
for t in (13,21):
    for u in (9,21):
        residual=((22-t)*(28-u),(t-13)*(u-7))
        corner.append({'axis23_first':t,'axis29_first':u,'total_deficit':sum(residual)-35})
need([x['total_deficit'] for x in corner]==[136,28,0,84],'closed bilinear four-corner certificate')
need((22-21)*(28-9)==19 and (21-13)*(9-7)==16 and 19<=21 and 16<=26 and 19+16==35,'closed zero also meets mixed singleton caps')
finite_margin=35*(1-a*b)/616
need(finite_margin>0,'strict finite-height qualitative margin')

# Reconstruct500's entire chart and index order, without importing its producer.
def load(s):
    return (prod(max(1,x) for x in s[:3])+prod(max(1,-x) for x in s[:3])-1)*prod(s[3:])
allrows=[]
def complete(s):
    if len(s)==7:
        allrows.append(s);return
    for f in range(1,39):
        child=s+(f,)
        if load(child)>38:break
        complete(child)
third=list(range(2,39))+list(range(-2,-39,-1))
for s3 in third:
    for s5 in third+[0]:
        for s7 in [0]+third:
            s=(s3,s5,s7)
            if load(s)<=38:complete(s)
need(len(allrows)==expected['full_profiles']==23408 and len(set(allrows))==len(allrows),'full finite profile domain')
rows=[s for s in allrows if load(s)>=20]
need(len(rows)==expected['middle_profiles']==r500['profile_count']==20076,'middle index order')
index={s:i for i,s in enumerate(rows)}
X=[(i,s) for i,s in enumerate(rows) if load(s)==21]
Y=[(i,s) for i,s in enumerate(rows) if load(s)==26]
need(len(X)==expected['load21_profiles'] and len(Y)==expected['load26_profiles'],'complete two load classes')
need(len(X)*len(Y)==expected['pair_domain'],'complete class cross-product')
def factors(s):
    return tuple(max(1,x) for x in s[:3])+s[3:], tuple(max(1,-x) for x in s[:3])+s[3:]
def pair_capacity(s,t):
    aa,ab=factors(s);ba,bb=factors(t)
    cross=prod(min(x,y) for x,y in zip(aa[:3],bb[:3]))+prod(min(x,y) for x,y in zip(ab[:3],ba[:3]))-2
    need(cross>=0,'opposite-box correction sign')
    common=prod(min(x,y) for x,y in zip(s[3:],t[3:]))
    return load(s)+load(t)-common*cross
# All16 one-label Boolean patterns certify the formula used for enumeration.
for a0,b0,a1,b1 in product((0,1),repeat=4):
    expansion=(a0+b0-a0*b0)+(a1+b1-a1*b1)-a0*b1-b0*a1+a0*b0*a1+a0*b0*b1+a0*a1*b1+b0*a1*b1-2*a0*b0*a1*b1
    need(expansion==max(a0+a1,b0+b1),'literal pair Boolean expansion')
hist=Counter();edges=[]
for i,s in X:
    for j,t in Y:
        N=pair_capacity(s,t);hist[N]+=1
        if N==35:edges.append(tuple(sorted((i,j))))
need(len(edges)==len(set(edges))==expected['capacity35_edges']==7874,'full same-type edge census')
need(sum(hist.values())==expected['pair_domain'],'all class pairs accounted for')
edges.sort()
# Independently recompute every target capacity from literal exponent labels.
def literal(s):
    return tuple(set(product(*(range(v) for v in f))) for f in factors(s))
literal_cache={i:literal(rows[i]) for edge in edges for i in edge}
for i,j in edges:
    pair=(literal_cache[i],literal_cache[j])
    need([len(a0|b0) for a0,b0 in pair]==[load(rows[i]),load(rows[j])],'literal individual inventories')
    labels=set().union(*(a0|b0 for a0,b0 in pair))
    N=sum(max(sum(d in a0 for a0,b0 in pair),sum(d in b0 for a0,b0 in pair)) for d in labels)
    need(N==35,'literal full-label shared-selector capacity')

excluded=c500['excluded_middle_indices']
need(excluded==sorted(set(excluded)) and len(excluded)==r500['excluded_middle_vertices'],'500 excluded list')
support500=set(range(len(rows)))-set(excluded)
repair=r501['orbit_and_subset_repair'];removed=repair['remove_indices']
need(removed==[4405,4407] and set(removed)<=support500,'501 declared subset repair')
support501=support500-set(removed)
need(len(support500)==r500['support_vertices'] and len(support501)==repair['repaired_support_vertices'],'retained support sizes')
occ500=[e for e in edges if set(e)<=support500]
occ501=[e for e in edges if set(e)<=support501]
expected_occ=[tuple(e) for e in c['expected_baseline_occurrences']]
need(occ500==occ501==expected_occ and len(occ501)==expected['repaired501_occurrences']==9,'the nine literal retained occurrences')
# Compare the full same-capacity class with the actual symmetry orbit of those9.
orbit=set();eligible=0
for edge in occ501:
    for sp in permutations(range(3)):
        for co in permutations(range(3,7)):
            for sign in (1,-1):
                images=[tuple(sign*rows[i][j] for j in sp)+tuple(rows[i][j] for j in co) for i in edge]
                if any(s[0]==0 for s in images):continue
                need(all(s in index for s in images),'orbit chart membership')
                eligible+=1;orbit.add(tuple(sorted(index[s] for s in images)))
need(len(orbit)==expected['nine_seed_orbit_edges']==144 and eligible==expected['nine_seed_eligible_transformations']==2592,'complete nine-seed orbit')
need(orbit<=set(edges),'symmetry transport preserves the named capacity type')

out={'certificate_sha256':hashlib.sha256(cert_path.read_bytes()).hexdigest(),'source_inputs':c['inputs'],
     'retained_capacity_classes':len(base),'finite_zero_representatives':len(zero_keys),'finite_zero_height':H,
     'axis_factors':[str(a),str(b)],'unique_boundary_capacity':[21,26,35],
     'closed_corners':corner,'closed_zero_witness':{'axis23':[21,14],'axis29':[9,26],'mixed':[19,16]},
     'height3_qualitative_lower':str(finite_margin),
     'full_profile_count':len(allrows),'middle_profile_count':len(rows),'load_class_counts':[len(X),len(Y)],
     'class_pair_count':len(X)*len(Y),'capacity_histogram':[[N,count] for N,count in sorted(hist.items())],
     'full_capacity35_edges':[list(e) for e in edges],
     'baseline500_occurrences':[list(e) for e in occ500],'repaired501_occurrences':[list(e) for e in occ501],
     'nine_seed_orbit_edges':[list(e) for e in sorted(orbit)],'nine_seed_eligible_transformations':eligible,
     'full_class_beyond_nine_seed_orbit':len(edges)-len(orbit),
     'profiles_at_edges':{str(i):list(rows[i]) for i in sorted({i for edge in edges for i in edge})},
     'boundary':c['boundary']}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(out==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained exact result mismatch')
print(json.dumps({'retained_classes':len(base),'height3_zero_witnesses':len(zero_keys),'qualitative_capacity':[21,26,35],'full_same_type_edges':len(edges),'retained_occurrences':len(occ501),'nine_seed_orbit':len(orbit),'checks':'passed'},indent=2))
