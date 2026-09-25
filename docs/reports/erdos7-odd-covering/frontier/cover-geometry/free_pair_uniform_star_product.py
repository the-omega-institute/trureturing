#!/usr/bin/env python3
"""Complete raw-star-product gate for one fixed coherent central star layout.

All 120 pair labels have arbitrary globally fixed central phases and outside
endpoints. The central pure law and seven-star central roles are restricted
as stated in the accompanying ordinary proof. Uses exact standard-library
arithmetic and all 512 inherited costs; no Lean or large source scan.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import prod
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
QS=(7,11,13,17,19)
CORE=(3,5)+QS
EDGES=tuple(combinations(range(5),2))
STAR=(0,2,0,2,0,10)
PINS={
 'actual_pair_activation_certificate.json':'2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f',
 'unanchored_square_source_certificate.json':'b8c38f05cbcd65607e25bc138ecc5a20961cd5bb786b18ad41df5583986bb1a4',
}
W3=[F() if l==3 else F(1,5) for l in range(6)]
W5=[F() if m==5 else F(1,19) for m in range(20)]
CELLS=tuple((l,m) for l,m in product(range(6),range(20))
            if W3[l] and W5[m] and (l//3,m//5)!=(0,0))
CHECKS={}

def ck(name,condition):
 if not condition:raise ArithmeticError(name)
 CHECKS[name]=True

def quinary(h):
 out=[F()]*4
 for j in range(4):
  root=F()
  for k in range(5):
   m=5*j+k
   if not W5[m]:continue
   value=W5[m]*h[m]
   root+=value
   out[2]=max(out[2],value)
   out[3]=max(out[3],F(4,5)*h[m])
  out[0]+=root
  out[1]=max(out[1],root)
 return out

def screens(h):
 out=[F()]*16
 roots=[[F()]*20 for _ in range(2)]
 for l in range(6):
  if not W3[l]:continue
  q=quinary(h[l])
  for e in range(4):
   out[8+e]=max(out[8+e],W3[l]*q[e])
   out[12+e]=max(out[12+e],q[e])
  for m in range(20):roots[l//3][m]+=W3[l]*h[l][m]
 total=quinary([roots[0][m]+roots[1][m] for m in range(20)])
 left,right=quinary(roots[0]),quinary(roots[1])
 for e in range(4):
  out[e]=total[e]
  out[4+e]=max(F(),left[e],right[e])
 return out

def menu(n,block,weights,zero,deep,mode):
 if mode==0:return [weights]
 if mode==1:
  return [[weights[k] if k//block==j else F() for k in range(n)]
          for j in range(n//block)]+[[F()]*n]
 return [[(weights[k] if mode==2 else deep) if k==leaf else F()
          for k in range(n)] for leaf in range(n) if leaf!=zero]+[[F()]*n]

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--source-dir',type=Path,default=HERE)
 ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
 args=ap.parse_args()
 data={}
 for name,pin in PINS.items():
  raw=(args.source_dir/name).read_bytes()
  ck('source_pin_'+name,sha256(raw).hexdigest()==pin)
  data[name]=json.loads(raw)
 source=data['actual_pair_activation_certificate.json']
 inherited=data['unanchored_square_source_certificate.json']
 c=F(source['constants']['continuation_c']);g=1-c
 alpha=F(inherited['Haar_factor'])
 ck('constants',c==F(1084133,201247200) and alpha==F(2673,110656))
 loss=list(map(F,source['complete_coefficients']['loss']))
 query=list(map(F,source['complete_coefficients']['weighted_nonunit_query']))
 ck('complete_512_nonnegative_costs',len(loss)==len(query)==512 and min(loss+query)>=0)
 ck('unit_separated',loss[0]==query[0]==0)
 ck('actual_central_source',sum(W3)==sum(W5)==1 and max(W3)==F(1,5)<=F(2,9)
    and max(W5)==F(1,19)<=F(4,75))
 residues3=[(l%3)*3+l//3 for l in range(6) if W3[l]]
 residues5=[(m%5)*5+m//5 for m in range(20) if W5[m]]
 ck('central_pure_survivors',set(residues3)=={x for x in range(9) if x%3!=2 and x!=1}
    and set(residues5)=={x for x in range(25) if x%5!=4 and x!=1})
 ck('unmasked_cells',len(CELLS)==80 and sum((W3[l]*W5[m] for l,m in CELLS),F())==F(16,19))
 r=[F(1,q-1) for q in QS]
 square=[F(1,q*(q-2)) for q in QS]
 H=[[[F()]*20 for _ in range(6)] for T in range(32)]
 cells=[]
 for l,m in CELLS:
  Z=[1-(r[q]+square[q])*(int(l//3==STAR[0])+int(m//5==STAR[1]))
     -r[q]*(int((l//3,m//5)==STAR[2:4])+int(l==STAR[4])+int(m==STAR[5]))
     for q in range(5)]
  ck(f'positive_actual_star_lower_{l}_{m}',all(1-5*r[q]-2*square[q]<=Z[q]<=1 for q in range(5))
     and min(Z)>0)
  for T in range(32):H[T][l][m]=prod(Z[q] for q in range(5) if not T>>q&1)
  cells.append({'cell':[l,m],'central_mass':str(W3[l]*W5[m]),'Z':list(map(str,Z))})
 readings=[screens(h) for h in H]
 # Verify every optimized screen by a direct product of the original menus.
 menus3=[menu(6,3,W3,3,F(1),e) for e in range(4)]
 menus5=[menu(20,5,W5,5,F(4,5),e) for e in range(4)]
 for T in range(32):
  for e3,e5 in product(range(4),repeat=2):
   direct=max(sum((x[l]*y[m]*H[T][l][m] for l,m in CELLS),F())
              for x,y in product(menus3[e3],menus5[e5]))
   ck(f'direct_query_menu_{T}_{e3}_{e5}',direct==readings[T][4*e3+e5])
 pair=[F()]*512
 labels=[]
 for q,s in EDGES:
  T=(1<<q)+(1<<s)
  for eq,es in [(1,1),(2,1),(1,2)]:
   cap=(r[q] if eq==1 else square[q])*(r[s] if es==1 else square[s])
   for a,b in product(range(2),repeat=2):
    mode=4*a+b
    modulus=3**a*5**b*QS[q]**eq*QS[s]**es
    pair[32*mode+T]+=cap
    labels.append({'modulus':modulus,'edge':[QS[q],QS[s]],'outside_exponents':[eq,es],
      'central_exponents':[a,b],'support_mask':T,'outside_cap':str(cap),
      'central_maximum':str(readings[T][mode]),
      'raw_original_loss_upper':str(cap*readings[T][mode])})
 ck('one_twenty_numerical_pair_labels',len(labels)==len({row['modulus'] for row in labels})==120)
 for q,s in EDGES:
  T=(1<<q)+(1<<s)
  cap=r[q]*r[s]+square[q]*r[s]+r[q]*square[s]
  ck(f'pair_coefficient_sum_{q}_{s}',all(pair[32*(4*a+b)+T]==cap for a,b in product(range(2),repeat=2)))
 mass=readings[0][0]
 original_loss=sum((loss[32*mode+T]*readings[T][mode] for T in range(32) for mode in range(16)),F())
 pair_loss=sum((pair[32*mode+T]*readings[T][mode] for T in range(32) for mode in range(16)),F())
 nonunit=sum((query[32*mode+T]*readings[T][mode] for T in range(32) for mode in range(16)),F())
 gamma=g*mass-g*(original_loss+pair_loss)-c*nonunit
 ck('all_actual_pair_events_charged_once',pair_loss==sum((F(row['raw_original_loss_upper']) for row in labels),F()))
 ck('positive_complete_gate',gamma==F(165833464880934928533269023673,8577984268789500979814400000000)>F(1,52))
 ck('dominated_core_mass_positive',mass-original_loss-pair_loss>0)
 head=alpha*gamma
 ck('head_strict_lower',head>F(1,2200))
 result={
  'schema':'free-pair-uniform-star-product-complete-gate-v1','status':'PASS',
  'scope':{
   'central_pure':'2mod3,1mod9,4mod5,1mod25; any further central pure original absent or contained in these deletions. Uniform surviving mod9/mod25 leaf laws.',
   'central_mask':'0mod15, imposed if absent; no renormalization after this deletion.',
   'seven_star_central_roles':{'3q':'0mod3','5q':'2mod5','15q':'12mod15','9q':'0mod9','25q':'2mod25','3q^2':'0mod3','5q^2':'2mod5'},
   'star_outside':'All first roots and higher lifts arbitrary independently. Missing stars may be padded once with these central roles.',
   'pair_labels':'All120 retained pair labels, arbitrary independently and globally fixed central residues, first roots and higher lifts; no within-edge endpoint-sharing condition.',
   'other_originals':'All other Report626 mixed inventories and unrestricted23/29/31 continuation; literal reference head primes and distinct numerical originals remain.',
   'source':'One actual raw star-product source followed by all original deletions. No strict Shearer/good-cell condition for pair events.',
  },
  'dependencies':PINS,'constants':{'c':str(c),'g':str(g),'alpha':str(alpha)},
  'central_weights3':list(map(str,W3)),'central_weights5':list(map(str,W5)),
  'star_template':STAR,'cell_data':cells,'pair_originals':sorted(labels,key=lambda row:row['modulus']),
  'complete_pair_loss_coefficients':list(map(str,pair)),
  'complete_512_readings':[[str(x) for x in row] for row in readings],
  'bounds':{'raw_star_mass':str(mass),'remaining_original_loss':str(original_loss),
    'all_pair_original_loss':str(pair_loss),'nonunit_query_upper':str(nonunit),
    'core_mass_lower':str(mass-original_loss-pair_loss),'complete_gate_lower':str(gamma),
    'gate_strict_lower':'1/52','head_haar_lower':str(head),'head_strict_lower':'1/2200'},
  'checks':CHECKS,'check_count':len(CHECKS),
  'new_lean_verification':False,'large_source_scan_rerun':False,
  'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 }
 args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['status','check_count','bounds']},indent=2))

if __name__=='__main__':main()
