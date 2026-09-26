#!/usr/bin/env python3
"""Verify the complete-fee boundary for globally deleted outside-root sets."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,lcm
from hashlib import sha256
from collections import Counter
import argparse,json
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--source',type=Path,help='Explicit path to the pinned640 parent certificate')
ap.add_argument('--certificate',type=Path,default=Path(__file__).with_suffix('.json'))
ap.add_argument('--output',type=Path)
args=ap.parse_args();checks=Counter()
def ck(name,value):
 if not value:raise ArithmeticError(name)
 checks[name]+=1
certbytes=args.certificate.read_bytes();cert=json.loads(certbytes)
parent_path=args.source or args.source_dir/'remaining33_global_root_exclusion_certificate.json';parent_bytes=parent_path.read_bytes();parent=json.loads(parent_bytes)
ck('parent_sha256',sha256(parent_bytes).hexdigest()==cert['parent_sha256'])
ck('parent_schema',parent['schema']=='global-root-exclusion-complete-source-certificate-v1')
Q=(7,11,13,17,19);limits=tuple(q-2 for q in Q);ck('prime_and_budget_contract',cert['outside_primes']==list(Q)and cert['budget_upper_bounds']==list(limits))
g=F(parent['constants']['g']);alpha=F(parent['constants']['alpha']);fees=list(map(F,parent['combined512_coefficients']))
ck('complete512_nonnegative_fees',len(fees)==512 and min(fees)>=0)
ck('parent_inventory',len(parent['inventory']['root_stars55'])==55 and len(parent['inventory']['root_pairs40'])==40 and len(parent['inventory']['paid370'])==370 and parent['inventory']['paid_central3']==[45,75,225])
# The central mask is M(l,m)=1−1_(l<3,m<5). Literal selectors are
# summarized exactly by(total mass, mass in the masked first root).
def menu_features(n,width,z,w,strong,weak,deep):
 weights=[0 if i==z else weak if i==w else strong for i in range(n)]
 result=[[(sum(weights),sum(weights[:width]))]]
 result.append([(0,0)]+[(sum(weights[i:i+width]),sum(weights[i:i+width])if i==0 else 0)for i in range(0,n,width)])
 result.append([(0,0)]+[(weights[i],weights[i]if i<width else 0)for i in range(n)if weights[i]])
 result.append([(0,0)]+[(deep,deep if i<width else 0)for i in range(n)if weights[i]])
 return result
menus3={(z,w):menu_features(6,3,z,w,2,1,9)for z,w in product(range(6),repeat=2)if z!=w}
menus5={(z,w):menu_features(20,5,z,w,4,3,60)for z,w in product(range(20),repeat=2)if z!=w}
readings={}
for a,b in product(menus3,menus5):
 row=tuple(max(xt*yt-xm*ym for xt,xm in menus3[a][i]for yt,ym in menus5[b][j])for i,j in product(range(4),repeat=2))
 ck('nonnegative_menu_vector',min(row)>=0);readings.setdefault(row,[]).append(a+b)
ck('complete_source_corners',sum(map(len,readings.values()))==11400)
menu_classes=[dict(reading_numerators=list(row),corner_count=len(cs),first_corner=list(cs[0]))for row,cs in sorted(readings.items())]
ck('exact16_menu_classes',len(menu_classes)==16 and menu_classes==cert['menu_classes'])
# Readings have denominator675. Fold ALL32 supports for each of16 modes.
den=[prod(q-1 for i,q in enumerate(Q)if not T>>i&1)for T in range(32)]
scaled=[fees[j]/den[j%32]for j in range(512)];mass=g/den[0];cd=lcm(mass.denominator,*(v.denominator for v in scaled));ci=[int(v*cd)for v in scaled];mi=int(mass*cd)
positive=[];negative=[];computed=[]
for field,sign in(('maximal_positive',1),('minimal_negative',-1)):
 for rec in cert[field]:
  d=tuple(rec['budget']);ck('frontier_budget_legal',len(d)==5 and all(type(v)is int and 1<=v<=lim for v,lim in zip(d,limits)))
  roots=tuple(q-1-v for q,v in zip(Q,d));powers=[prod(roots[i]for i in range(5)if not T>>i&1)for T in range(32)]
  folded=[sum(ci[32*m+T]*powers[T]for T in range(32))for m in range(16)]
  scores={row:mi*powers[0]*row[0]-sum(c*v for c,v in zip(folded,row))for row in readings};best=min(scores.values());worst=min(corner for row,v in scores.items()if v==best for corner in readings[row]);ties=sum(len(readings[row])for row,v in scores.items()if v==best)
  gate=F(best,675*cd);ck('exact_frontier_gate',gate==F(rec['minimum_gate']));ck('strict_frontier_sign',sign*gate>0)
  ck('frontier_witness_and_multiplicity',list(worst)==rec['worst_corner']and ties==rec['tied_corner_count'])
  computed.append(gate)
  (positive if sign==1 else negative).append(d)
ck('frontier_sizes',len(positive)==18 and len(negative)==29)
def le(a,b):return all(x<=y for x,y in zip(a,b))
for frontier in(positive,negative):
 for a,b in combinations(frontier,2):ck('frontier_antichain',not le(a,b)and not le(b,a))
classified=Counter()
for d in product(*(range(1,lim+1)for lim in limits)):
 yes=any(le(d,p)for p in positive);no=any(le(n,d)for n in negative)
 ck('exhaustive_monotone_frontier_partition',yes!=no);classified['positive'if yes else'negative']+=1
ck('classified_counts',dict(classified)==cert['classified_counts']=={'positive':58,'negative':126167})
ck('domain_cardinality',sum(classified.values())==prod(limits)==126225)
minimum=min(computed[:len(positive)]);ck('positive_uniform_minimum',str(minimum)==cert['minimum_positive_gate']and minimum>F(1,2200))
ck('positive_haar_lower',alpha*minimum==F(cert['minimum_positive_haar'])and alpha*minimum>F(1,92000))
ck('second_seven_root_obstruction',next(F(r['minimum_gate'])for r in cert['minimal_negative']if r['budget']==[2,1,1,1,1])==F(-203208177531255678309923,20428636029505837056000000))
out=dict(schema='global-root-budget-verification-v1',status='PASS',scope=cert['scope'],direct_frontier_budget_evaluations=47,central_corners=11400,distinct_menu_vectors=16,classified_budget_vectors=126225,classified_counts=dict(classified),minimum_positive_gate=str(minimum),minimum_positive_haar=str(alpha*minimum),checks=dict(checks),check_count=sum(checks.values()),parent_sha256=sha256(parent_bytes).hexdigest(),certificate_sha256=sha256(certbytes).hexdigest(),producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),new_lean_verification=False)
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
