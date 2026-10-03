"""Rebuild the complete weighted query envelope and one positive29-height bridge.

The native enumerator performs exact integer arithmetic over every actual
old45 query pair; this consumer independently verifies actual315 support,
all numerical cylinder caps, maximizing numerical queries and rational
transport. The result is scoped to one fixed core phase family, not all
old sources, and is not Lean verification.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from hashlib import sha256
import argparse,json,subprocess,tempfile

def need(ok,msg):
 if not ok:raise RuntimeError(msg)

MODS=(3,5,9,15,45)
LABELS=(3,5,9,15,45,7,21,35,63,105,315)
K48=(0,12,24,12,42,8,8,22,36,22,57)

def calculate(literal,native,binary):
 need(sha256(literal.read_bytes()).hexdigest()=='65f1b68c347ff16db72c2fe3dde183b5a2c02458bf5ab0cfc769416d21559779','pinned actual source input')
 need(sha256(native.read_bytes()).hexdigest()=='3abbe8ce16f302e8f8fa424dcac0572e4641aad71022b3634129d61e615ca212','pinned complete native enumerator')
 raw=json.loads(literal.read_text());rules=raw['actual_core_originals'];X=raw['old45_points'];r=raw['remaining'];weights=raw['weights']
 need([d for d,a in rules]==list(LABELS),'all eleven distinct core original labels')
 need(all(type(a)is int and 0<=a<d for d,a in rules),'actual numerical phases')
 survivors=[z for z in range(315) if all(z%d!=a for d,a in rules)]
 fibres=[[z for z in survivors if z%45==x] for x in X]
 need(len(X)==len(r)==len(weights)==16 and len(set(X))==16,'sixteen source rows')
 need(sum(map(len,fibres))==len(survivors)==75 and [len(f) for f in fibres]==r,'actual same315 source')
 need(all(any(z%7==5 for z in f) for f in fibres),'common untouched row for convex concentration')
 need(all(type(v)is int and 0<=v<=1000000 for v in weights) and max(weights)>0,'bounded nonnegative integer source weights')
 D=sum(v*n for v,n in zip(weights,r));t=max(weights)
 mass={z:weights[i] for i,f in enumerate(fibres) for z in f}
 caps=[max(sum(mass[z] for z in survivors if z%d==a) for a in range(d)) for d in LABELS]
 M=sum(caps);K=sum(a*b for a,b in zip(caps,K48))

 command=['clang++','-std=c++17','-O3','-fsanitize=undefined','-fno-sanitize-recover=undefined',str(native),'-o',str(binary)]
 subprocess.run(command,check=True)
 replay=subprocess.run([str(binary)],input=' '.join(map(str,[len(X)]+X+r+weights))+'\n',text=True,capture_output=True,check=True)
 exact=json.loads(replay.stdout)
 need(exact['denominator']==D and exact['query_count']==4480 and exact['ordered_pairs']==4480**2,'complete exact weighted query replay')
 uniform_replay=subprocess.run([str(binary)],input=' '.join(map(str,[len(X)]+X+r+[1]*len(X)))+'\n',text=True,capture_output=True,check=True)
 uniform=json.loads(uniform_replay.stdout)
 need(uniform['denominator']==75 and uniform['query_count']==4480 and uniform['ordered_pairs']==4480**2 and (uniform['J4'],uniform['J6'])==(29,10),'same-source uniform hinge maxima for the conservative comparison')
 # Recover numerical phases for each maximizing old45 layout, then read
 # that complete numerical315 query directly on the actual75 cells.
 inventories=[]
 for d in MODS:
  masks={}
  for a in range(d):
   mask=tuple(int(x%d==a) for x in X)
   if any(mask):masks[mask]=a
  inventories.append(list(masks.values()))
 layouts={}
 for phases in product(*inventories):
  vector=tuple(1+sum(x%d==a for d,a in zip(MODS,phases)) for x in X)
  layouts[vector]=phases
 need(len(layouts)==4480,'independent complete old45 layout inventory')
 witnesses=[]
 for threshold in (4,6):
  A=layouts[tuple(exact['A'+str(threshold)])];B=layouts[tuple(exact['B'+str(threshold)])]
  query=[[1,0]]+[[d,a] for d,a in zip(MODS,A)]+[[7,5]]
  for d,a in zip(MODS,B):
   while a%7!=5:a+=d
   query.append([7*d,a])
  need([d for d,a in query]==[1]+list(LABELS) and all(0<=a<d for d,a in query),'complete numerical maximizing query')
  value=sum(mass[z]*max(sum(z%d==a for d,a in query)-threshold,0) for z in survivors)
  need(value==exact['J'+str(threshold)],'direct actual numerical witness attains reported maximum')
  witnesses.append(dict(threshold=threshold,numerical_query=query,weighted_numerator=value))

 P=raw['outside_primes'];flags=raw['full_height_flags'];thresholds=raw['thresholds']
 need(P==[13,17,19,23,29] and flags==[0,0,0,0,1] and thresholds==[4,4,4,6,6],'declared29-height scope and thresholds')
 rho=[F(1,p-a-e) for p,a,e in zip(P,thresholds,flags)];fac=prod(1+v for v in rho);B=fac-1-sum(rho)
 R4=sum(v for v,a in zip(rho,thresholds) if a==4);R6=sum(v for v,a in zip(rho,thresholds) if a==6)
 J4=exact['J4'];J6=exact['J6']
 cost=fac*F(K,48*D)+B*(1+F(M,D))+R4*F(J4,D)+R6*F(J6,D)
 coarse=fac*F(K,48*D)+B*(1+F(M,D))+R4*F(29*t,D)+R6*F(10*t,D)
 haar=F(315*t,D)*prod(F(p-e,p-a-e) for p,a,e in zip(P,thresholds,flags))
 density=(1-cost)/haar
 expected=raw['expected'];got=dict(D=D,M=M,K=K,t=t,caps=caps,J4=J4,J6=J6,cost=str(cost),conservative_cost=str(coarse),haar_cap=str(haar),haar_survivor=str(density))
 need(got==expected,'all retained rational source values rebuilt')
 need(cost<1<coarse and density>0,'sharp hinge restores the same-law positive reserve')
 return dict(scope=__doc__,actual_core_originals=rules,old45_points=X,remaining=r,weights=weights,
             query_count=exact['query_count'],ordered_pairs=exact['ordered_pairs'],uniform_query_ordered_pairs=uniform['ordered_pairs'],uniform_J4=uniform['J4'],uniform_J6=uniform['J6'],maximizing_queries=witnesses,
             actual315_cells=len(survivors),all_numerical_cylinder_count=sum(LABELS),
             outside_primes=P,full_height_flags=flags,thresholds=thresholds,
             rho=[str(v) for v in rho],outside_factor=str(fac),multioutside_factor=str(B),
             native_sha256=sha256(native.read_bytes()).hexdigest(),**got,
             same_source_all_caps_and_hinges=True,all_remaining_phases_arbitrary_and_global=True,
             all_core_heights_finite=True,all_multioutside_supports=True,
             uniform_over_all_old_sources=False,no_solver_or_optimality_premise=True,lean_verification=False)

if __name__=='__main__':
 base=Path(__file__).resolve().parent
 ap=argparse.ArgumentParser()
 ap.add_argument('--write-result',type=Path)
 args=ap.parse_args()
 with tempfile.TemporaryDirectory(prefix='e7_weighted_hinges_',dir='/tmp') as tmp:
  result=calculate(base/'fibre_credit_depth_two_sharp_last29_input.json',
                   base/'fibre_credit_depth_two_weighted_hinges.cpp',
                   Path(tmp)/'enumerator')
 result=json.loads(json.dumps(result))
 if args.write_result:
  args.write_result.write_text(json.dumps(result,indent=2)+'\n')
 else:
  expected=json.loads(Path(__file__).with_suffix('.json').read_text())
  need(result==expected,'retained result agrees with exact recomputation')
 print(json.dumps(result,indent=2))
