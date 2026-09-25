#!/usr/bin/env python3
"""Bounded prefix and Haar-averaging checks for Report626 head transport.

The universal result uses the ordinary digit-injection proof. These finite
checks do not establish a common-source Gamma theorem, a network theorem,
or new Lean verification. No source producer or large scan is run.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product, combinations
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-dir', type=Path, default=HERE,
                    help='Directory containing the canonical Report626 certificate')
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
SOURCE_DIR = args.source_dir.resolve()
CHECKS={}
def ck(n,v):
    if not v: raise ArithmeticError(n)
    CHECKS[n]=True

def image(x,p,r,shift):
    return (x%p+shift[0])%r + r*((x//p+shift[1])%r)

results=[]
for p,r in [(3,3),(3,5),(5,7),(7,11)]:
    prefix_checks=0
    marginal=[[0]*(r*r) for _ in range(p*p)]
    for shift in product(range(r),repeat=2):
        images=[image(x,p,r,shift) for x in range(p*p)]
        ck(f'injective_{p}_{r}_{shift}',len(set(images))==p*p)
        for x,y in enumerate(images): marginal[x][y]+=1
        for e in (1,2):
            for a in range(r**e):
                pull=[x for x,y in enumerate(images) if y%(r**e)==a]
                if pull:
                    source_a=pull[0]%(p**e)
                    expected=[x for x in range(p*p) if x%(p**e)==source_a]
                    if pull!=expected: raise ArithmeticError(('prefix',p,r,shift,e,a,pull))
                prefix_checks+=1
        # All nonempty second-level lifts at a common target root have
        # the same unique source first root. Missing lifts are permitted.
        for target_root in range(r):
            source_roots={x%p for x,y in enumerate(images) if y%r==target_root}
            if len(source_roots)>1: raise ArithmeticError(('shared root',p,r,shift,target_root))
    ck(f'prefix_pulls_{p}_{r}',prefix_checks==r*r*(r+r*r))
    ck(f'uniform_images_for_each_source_{p}_{r}',all(row==[1]*(r*r) for row in marginal))
    results.append({'source_prime':p,'target_prime':r,'height':2,'shifts':r*r,
                    'prefix_checks':prefix_checks,'uniform_target_count_per_source_point':1})

# A complete, same-map two-coordinate averaging identity for a fixed
# non-product target survivor. Includes mixed exponents and overlap.
ps=(3,5);rs=(5,7)
originals=[((1,1),(1,2)),((2,1),(6,2)),((1,2),(1,9)),((2,2),(12,17)),((1,0),(4,0))]
ck('toy_original_vectors_distinct',len({e for e,a in originals})==len(originals))
def survives(x):
    return all(not all(xi%(r**e)==a for xi,r,e,a in zip(x,rs,es,aa)) for es,aa in originals)
target_count=sum(survives(x) for x in product(range(25),range(49)))
source_total=0
for sq in product(range(5),repeat=2):
    qimage=[image(x,3,5,sq) for x in range(9)]
    for sr in product(range(7),repeat=2):
        rimage=[image(x,5,7,sr) for x in range(25)]
        source_total+=sum(survives((x,y)) for x,y in product(qimage,rimage))
ck('joint_haar_averaging',F(source_total,25*49*9*25)==F(target_count,25*49))

# Joint primary/secondary edge-root preservation in the same toy map.
# All first/second cylinder lifts are covered by the one-coordinate checks;
# this verifies the two-coordinate products, including empty pullbacks.
edge_checks=0
for sq in product(range(5),repeat=2):
    qimg={((x+sq[0])%5):x for x in range(3)}
    for sr in product(range(7),repeat=2):
        rimg={((x+sr[0])%7):x for x in range(5)}
        for aq,ar in product(range(5),range(7)):
            pair_roots=[]
            for eq,er in [(1,1),(2,1),(1,2)]:
                aqh=aq+(5 if eq==2 else 0)
                arh=ar+(14 if er==2 else 0)
                qpull=[x for x in range(9) if image(x,3,5,sq)%(5**eq)==aqh]
                rpull=[x for x in range(25) if image(x,5,7,sr)%(7**er)==arh]
                if qpull and rpull: pair_roots.append((qpull[0]%3,rpull[0]%5))
            if len(set(pair_roots))>1: raise ArithmeticError(('edge sharing',sq,sr,aq,ar))
            if pair_roots and pair_roots[0]!=(qimg[aq],rimg[ar]): raise ArithmeticError('edge root formula')
            edge_checks+=1
ck('shared_edge_roots_including_empty_slots',edge_checks==25*49*5*7)

sourceps=(3,5,7,11,13,17,19,23,29,31)
targetps=(5,7,11,13,17,19,23,29,31,37)
labels=[]
for i,j in combinations(range(2,7),2):
    for a,b in product(range(2),repeat=2):
        for ei,ej in [(1,1),(2,1),(1,2)]:
            es=tuple({0:a,1:b,i:ei,j:ej}.get(k,0) for k in range(10))
            n=m=1
            for p,r,e in zip(sourceps,targetps,es): n*=p**e;m*=r**e
            labels.append((n,m,es))
ck('one_twenty_pair_labels_distinct_both_sides',len(labels)==len({a for a,b,e in labels})==len({b for a,b,e in labels})==120)
# An arbitrary quotient injection need not preserve first-level cylinders.
whole_pull=[x for x in range(9) if x%5==0]
ck('nonprefix_injection_boundary',whole_pull==[0,5] and len({x%3 for x in whole_pull})==2)
certpath=SOURCE_DIR/'unanchored_square_source_certificate.json'
cert=json.loads(certpath.read_text())
sourcepaths=[certpath]
ck('626_complete_twenty_sources',cert['complete'] is True and cert['complete_cases']==list(range(20)))
for field,name in [('producer_sha256','unanchored_square_source_certificate.py'),
                   ('kernel_sha256','unanchored_square_source_certificate.cpp'),
                   ('conditional_kernel_sha256','unanchored_square_source_certificate_conditional.cpp')]:
    path=SOURCE_DIR/name
    ck('626_source_'+field,sha256(path.read_bytes()).hexdigest()==cert[field])
    sourcepaths.append(path)
h=F(cert['haar_lower'])
ck('626_h_exact',h==F(18854797422716739,778672375572358758400)>F(1,42000))
result={'schema':'head-digit-injection-transport-v1','verdict':'PASS',
 'scope':'Head Haar only, any ten ordered distinct odd primes, role-wise Report626 exponent inventory and within-edge endpoint sharing.',
 'checks':CHECKS,'check_count':len(CHECKS),'prefix_tests':results,'joint_edge_checks':edge_checks,
 'toy_averaging':{'target_survivors':target_count,'target_total':25*49,'source_survivor_total_over_shifts':source_total,'shift_count':25*49,'source_total_per_shift':9*25},
 'head_haar_lower':str(h),'head_strict_lower':'1/42000',
 'proof_obligations':'General prefix preimages, endpoint preservation, auxiliary padding, exponent inventory and Haar averaging are established by the accompanying ordinary proof, not finite tests.',
 'not_established':['transport of the actual reference source law or its coordinate caps','network theorem','new Lean verification'],
 'sources':{p.name:sha256(p.read_bytes()).hexdigest() for p in sourcepaths},
 'new_lean_verification':False,'universal_statement_verified_by_finite_tests':False,
 'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['verdict','check_count','prefix_tests','joint_edge_checks','toy_averaging','head_haar_lower']},indent=2))
