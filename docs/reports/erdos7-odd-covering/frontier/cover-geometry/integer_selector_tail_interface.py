"""Report503: discrete first selectors, capped gap and realizable axis limits.
Standard-library exact checks; quantified statements have ordinary proofs.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
import argparse,json

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--certificate',type=Path)
parser.add_argument('--output',type=Path)
args=parser.parse_args();R=Path(__file__).resolve().parent
cert=json.loads((args.certificate or R/'integer_selector_tail_interface_certificate.json').read_text())
def need(x,m):
 if not x:raise ValueError(m)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def crt(residues,moduli):
 x=0;M=1
 for a,m in zip(residues,moduli):
  x+=M*((a-x)*pow(M,-1,m)%m);M*=m
 return x%M

def capped_example():
 A=(1,0,0,1);B=(0,1,1,0);C=(1,0,1,0);D=(0,1,0,1)
 labels=[3**j for j in range(1,6)]+[5**j for j in range(1,8)]
 moduli=(3**5,5**7)
 points=tuple(crt(a,moduli) for a in ((0,0),(1,1),(1,0),(0,1)))
 for d in labels:
  need(tuple(tuple(int(x%d==a) for x in points) for a in (0,1))==((A,B) if d%3==0 else(C,D)),'literal capped-example masks')
 def count(a,b):return tuple(a*x+(5-a)*y+b*z+(7-b)*u for x,y,z,u in zip(A,B,C,D))
 def cap(w):return 5*max(dot(w,A),dot(w,B))+7*max(dot(w,C),dot(w,D))
 S={count(a,b) for a,b in product(range(6),range(8))}
 need(len(S)==48 and cap(A)==cap(B)==17,'capped example count and pair budgets')
 need(tuple(F(x+y,2) for x,y in zip(count(0,0),count(5,7)))==(F(6),)*4,'old capped target in convex selector set')
 branches=[]
 for a,b in product(range(6),range(8)):
  n=count(a,b);w=min((A,B),key=lambda w:dot(w,n));upper=F(6*dot(w,n)+cap(w),7)+12
  need(dot(w,n)<=11 and upper<=F(167,7),'every capped integer branch has a strict total bound')
  branches.append({'A_choices':[a,b],'activation':n,'deficient_pair':w,'total_upper':str(upper)})
 n=count(2,3);r=count(5,6);t=(F(41,7),F(6),F(6),F(6))
 need(n in S and r in S and all(0<=x<=6 for x in t),'sharp lifted point domain')
 need(all(7*x<=6*y+z for x,y,z in zip(t,n,r)) and sum(t)==F(167,7),'sharp lifted point')
 return {'prime':7,'old_labels':labels,'old_points':points,'old_modulus':prod(moduli),'old_total':'24','new_total':'167/7','gap':'1/7','branches':branches,'sharp_relaxed_witness':{'activation':n,'tail':r,'point':list(map(str,t))}}

PRIMES=tuple(cert['old_primes']);need(PRIMES==(3,5,7,11,13,17,19) and cert['split_coordinates']==3,'old coordinate model')
def boxes(profile):
 return tuple(set(product(*(range(x) for x in f))) for f in (tuple(max(1,x) for x in profile[:3])+tuple(profile[3:]),tuple(max(1,-x) for x in profile[:3])+tuple(profile[3:])))

def axes(case):
 profiles=case['profiles'];k=len(profiles);w=case['weight']
 need(k in (3,4) and len(w)==k and all(type(x) is int and x>=0 for x in w),'weighted tested points')
 need(all(len(s)==7 and all(type(x) is int for x in s) and all(x>=1 for x in s[3:]) and all(x==0 or abs(x)>=2 for x in s[:3]) for s in profiles),'literal profile schema')
 bb=list(map(boxes,profiles));labels=set().union(*(a|b for a,b in bb))
 patterns={d:(tuple(int(d in a) for a,b in bb),tuple(int(d in b) for a,b in bb)) for d in labels}
 N=sum(max(dot(w,a),dot(w,b)) for a,b in patterns.values())
 need(N==case['expected_capacity'],'literal weighted capacity')
 # One common old CRT realization, without a completed-source occupancy claim.
 E=tuple(max(max(1,abs(s[i])) for s in profiles) for i in range(7));mods=tuple(p**e for p,e in zip(PRIMES,E))
 A=0;B=crt([1,1,1,0,0,0,0],mods)
 points=[]
 for s in profiles:
  coords=[]
  for i,(p,f) in enumerate(zip(PRIMES,s)):
   coords.append((2 if f==0 else (0 if f>0 else 1)+p**(abs(f)-1)) if i<3 else p**(f-1))
  points.append(crt(coords,mods))
 oldlabels={d:prod(p**e for p,e in zip(PRIMES,d)) for d in labels}
 need(len(set(oldlabels.values()))==len(labels),'distinct old numerical labels')
 for d,m in oldlabels.items():
  actual=tuple(tuple(int((x-center)%m==0) for x in points) for center in (A,B))
  need(actual==patterns[d],'same old centres and tested points realize every mask')
 ax=[]
 need([e['prime'] for e in case['axes']]==[23,29],'separate original prime axes')
 for e in case['axes']:
  p=e['prime'];h=p-1;rows=e['labels'];ds=[tuple(row['exponents']) for row in rows]
  need(len(ds)==len(labels) and len(set(ds))==len(ds) and set(ds)==labels,'one selector and digit for every literal old label')
  chosen=[]
  for row,d in zip(rows,ds):
   need(row['selector'] in ('A','B') and type(row['digit']) is int and 1<=row['digit']<=h,'legal selector and nonzero digit')
   chosen.append(patterns[d][int(row['selector']=='B')])
  n=tuple(sum(mask[i] for mask in chosen) for i in range(k))
  need(list(n)==e['activation'] and all(x<=h for x in n),'retained integer activation')
  conflict_count=0
  for i in range(len(rows)):
   for j in range(i):
    if any(a and b for a,b in zip(chosen[i],chosen[j])):
     conflict_count+=1;need(rows[i]['digit']!=rows[j]['digit'],'shared old point requires distinct digits')
  digits=len({row['digit'] for row in rows})
  need(digits==e['phase_digits'] and digits<=h,'retained coloring size')
  # Explicit finite CRT residues and direct coverage at J=2.
  J=2;P=p**J;counts=[]
  for i,x in enumerate(points):
   covered=set()
   for d,row,mask in zip(ds,rows,chosen):
    m=oldlabels[d];center=A if row['selector']=='A' else B
    for j in range(1,J+1):
     pp=p**j;phase=row['digit']*p**(j-1);residue=crt((center%m,phase),(m,pp))
     need(residue%m==center%m and residue%pp==phase,'original full-label CRT residue')
     if mask[i]:
      cylinder={z for z in range(P) if z%pp==phase}
      need(not (covered&cylinder),'explicit finite-height disjointness')
      covered|=cylinder
   counts.append(len(covered))
   need(F(h*len(covered),P)==(1-F(1,P))*n[i],'finite axis exact normalized deletion')
  ax.append({'prime':p,'activation':n,'digits_used':digits,'conflicting_label_pairs':conflict_count,'checked_height':J,'finite_union_counts':counts,'finite_normalized_loss':[str((1-F(1,P))*v) for v in n]})
 t,u=[e['activation'] for e in ax];limit=sum(a*(22-b)*(28-c) for a,b,c in zip(w,t,u))-N
 need(limit==case['expected_limit'],'common-pair limiting objective')
 return {'profiles':profiles,'old_carrier':prod(mods),'old_centres':[A,B],'old_points':points,'literal_label_count':len(labels),'weight':w,'weighted_capacity':N,'axes':ax,'limiting_objective':limit}

need(len(cert['cases'])==2,'exactly two retained input systems')
out={'capped_example':capped_example(),'axis_realizations':[axes(case) for case in cert['cases']],
 'boundary':'Ordinary quantified proofs plus finite exact arithmetic. Axis limits are achieved in closure by finite literal families. No mixed-class simultaneous realization, completed-source occupancy, new mass bound or Lean verification.'}
out=json.loads(json.dumps(out))
if args.output:
 args.output.write_text(json.dumps(out,indent=2)+'\n')
else:
 need(out==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained result mismatch')
print(json.dumps({'capped_gap':out['capped_example']['gap'],'axis_limits':[e['limiting_objective'] for e in out['axis_realizations']],'checks':'passed'},indent=2))
