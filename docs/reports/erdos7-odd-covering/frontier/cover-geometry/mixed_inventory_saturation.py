from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from collections import Counter
from math import gcd
import json,hashlib,argparse

def need(x,m):
 if not x:raise ValueError(m)
parser=argparse.ArgumentParser(description='Exact mixed-inventory saturation over fixed report504 family F.')
parser.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path)
args=parser.parse_args();R=args.input_dir
raw=(R/'equal_axis_totals_distinct_mixed_responses.json').read_bytes()
need(hashlib.sha256(raw).hexdigest()=='df208046b6d4be92119dffd8b6fe403de708254d5cbe1ebb8a30bd3f3c7923e8','fixed report504 family input')
data=json.loads(raw)
M=data['old_carrier'];points=data['old_points'];centres=data['old_centres'];w=data['weight'];pure=data['families'][0]['literal_family']
need(w==[17,16,13] and len(pure)==102,'same fixed family F')
D=sorted({r['old_label'] for r in pure});need(len(D)==51,'old numerical labels')
need(len({r['modulus'] for r in pure})==102,'distinct pure labels')
records=[]
for d in D:
 masks=[tuple(i for i,x in enumerate(points) if (x-c)%d==0) for c in centres]
 selector=max(range(2),key=lambda s:sum(w[i] for i in masks[s]))
 records.append({'d':d,'selector':selector,'mask':masks[selector]})
n=tuple(sum(i in r['mask'] for r in records) for i in range(3))
need(n==(21,18,19) and sum(a*b for a,b in zip(w,n))==892,'full maximizing inventory')
# Actual first-phase survivors of the unchanged pure family.
P=[];Q=[]
for x in points:
 P.append({a for a in range(23) if all((x-r['residue'])%r['old_label'] or a!=r['residue']%23 for r in pure if r['prime']==23)})
 Q.append({b for b in range(29) if all((x-r['residue'])%r['old_label'] or b!=r['residue']%29 for r in pure if r['prime']==29)})
S=[set(product(a,b)) for a,b in zip(P,Q)];common=set.intersection(*S)
need(tuple(map(len,S))==(40,32,25),'literal pure counts')
need(common==set(product((0,22),(0,25,26,27,28))),'ten common surviving cells')
reserved=((22,26),(22,27),(22,28));multi=[r for r in records if len(r['mask'])>1]
need([r['d'] for r in multi]==[1,3,5,7,9,27],'six shared labels')
assigned=[set(reserved) for _ in range(3)]
for r,cell in zip(multi,sorted(common)[:6]):
 need(cell not in reserved and all(cell in S[i] for i in r['mask']),'common first cells')
 r['first_phase']=cell
 for i in r['mask']:assigned[i].add(cell)
for r in records:
 if len(r['mask'])==1:
  i=r['mask'][0];available=sorted(S[i]-assigned[i]);need(available,'singleton cell available')
  r['first_phase']=available[0];assigned[i].add(available[0])
# Greedy only after all nonsingletons: singleton groups have independent masks.
colored=[]
for r in multi+[r for r in records if len(r['mask'])==1]:
 used={q['color'] for q in colored if set(r['mask'])&set(q['mask'])}
 r['color']=next((c for c in range(1,22) if c not in used),None)
 need(r['color'] is not None,'21color assignment');colored.append(r)
for r,s in combinations(records,2):
 if set(r['mask'])&set(s['mask']):
  need(r['color']!=s['color'],'proper shared-mask colors')
  need(r['first_phase']!=s['first_phase'],'active first phases distinct')
def crt(residues,moduli):
 z=0;m=1
 for a,n in zip(residues,moduli):
  if n==1:continue
  z+=m*((a-z)*pow(m,-1,n)%n);m*=n
 return z%m,m

def family(J,K):
 mixed=[]
 for r in records:
  d=r['d'];c=r['color']
  for j,k in product(range(1,J+1),range(1,K+1)):
   if j==k==1:a,b=r['first_phase']
   elif k==1:a,b=22+c*23**(j-1),26
   elif j==1:a,b=22,27+c*29**(k-1)
   else:a,b=22+c*23**(j-1),28+29**(k-1)
   v,m=crt((centres[r['selector']]%d,a,b),(d,23**j,29**k))
   need(m==d*23**j*29**k and 0<=v<m and v%23**j==a and v%29**k==b,'original CRT phases')
   need(tuple(i for i,x in enumerate(points) if (x-v)%d==0)==r['mask'],'one shared old selector')
   mixed.append({'modulus':m,'residue':v,'old_label':d,'mask':r['mask'],'j':j,'k':k,'a':a,'b':b})
 need(len({r['modulus'] for r in pure+mixed})==102+51*J*K,'all complete moduli distinct')
 need(all(r['modulus']>1 and r['modulus']%2 for r in pure+mixed),'odd moduli greater than1')
 comparisons=0
 for r in mixed:
  for i in r['mask']:
   for q in pure:
    if (points[i]-q['residue'])%q['old_label']==0:
     need((r['residue']-q['residue'])%gcd(r['modulus'],q['modulus'])!=0,'mixed entirely inside pure survivors')
     comparisons+=1
 for r,s in combinations(mixed,2):
  if set(r['mask'])&set(s['mask']):
   need((r['residue']-s['residue'])%gcd(r['modulus'],s['modulus'])!=0,'simultaneously active mixed classes disjoint')
   comparisons+=1
 bypoint=[sum((F(1,23**r['j']*29**r['k']) for r in mixed if i in r['mask']),F()) for i in range(3)]
 weighted=sum(a*b for a,b in zip(w,bypoint));target=F(892,616)*(1-F(1,23**J))*(1-F(1,29**K))
 need(weighted==target,'full finite inventory attained')
 if J==K==1:
  survive=[]
  for i,x in enumerate(points):
   count=0
   for y in range(667):
    z,_=crt((x,y),(M,667))
    if all((z-r['residue'])%r['modulus'] for r in pure+mixed):count+=1
   survive.append(count)
  need(survive==[19,14,6],'direct complete CRT first-height survivors')
 return {'J':J,'K':K,'class_count':len(pure)+len(mixed),'mixed_classes':mixed,
         'exact_disjointness_comparisons':comparisons,'weighted_deletion':str(weighted),
         'fraction_of_closed_mixed_inventory':str(weighted/F(892,616)),
         'fibre_survival':[str(F(len(S[i]),667)-bypoint[i]) for i in range(3)]}
results=[family(1,1),family(2,2)]
need(F(results[1]['weighted_deletion'])>F(99,100)*F(892,616),'finite counterexample to1percent uniform rebate')
out={'source_sha256':hashlib.sha256(raw).hexdigest(),'old_labels':D,'old_carrier':M,'old_points':points,'old_centres':centres,'weight':w,'selected_mask_counts':n,'common_first_cells':sorted(common),'reserved_cells':reserved,'label_assignments':records,'finite_examples':results,'scope':'Fixed pure F; all-height result requires valuation proof. This check verifies exact finite examples and the fixed phase/color data. No actual source occupancy, axis-limit saturation, unrestricted covering result, or Lean verification.'}
out=json.loads(json.dumps(out))
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({'counts':n,'finite_examples':[{k:v for k,v in r.items() if k!='mixed_classes'} for r in results]},indent=2))
