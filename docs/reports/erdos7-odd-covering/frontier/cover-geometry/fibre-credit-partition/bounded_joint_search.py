"""Bounded exact joint-comparison producer for a canonical first-layer input.

Usage: python3 -I -S -B bounded_joint_search.py --input first_layer_witness.json --output result.json
Only standard-library Python is required. Importing this module does not run the search.
The fixed search is six common-shift starts, at most four complete rounds each,
with 180 address neighbors and 18 ownership-bit neighbors per round, at gamma=1/2.
"""
import argparse
import json
import time
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import prod
from pathlib import Path

PRIVATE_PRIMES=(11,13,17,19,23,29,31,37,41)
HEADS=(5,7)

class Checks:
 def __init__(self):self.count=0
 def require(self,condition,message):
  self.count+=1
  if not condition:raise ValueError(message)

def owners(masks,n):
 return {h:[1 if (masks[t]>>j)&1 else 2 for j in range(n)] for t,h in enumerate(HEADS)}

def head_weights(data):
 return {r:{h:[F(x) for x in data['head_weights'][str(r)][str(h)]] for h in HEADS} for r in (1,2)}

def parameters(data):
 P=data['private_primes'];Q=list(HEADS)+P
 b={p:F(1,p-2) for p in Q};a={h:F(h-1,h*(h-2)) for h in HEADS}
 g={1:{p:1-b[p] if p==5 else F(1) for p in Q},2:{p:F(1) if p==5 else 1-b[p] for p in Q}}
 G={r:prod((g[r][q] for q in P),start=F(1)) for r in (1,2)}
 return P,Q,b,a,g,G

def validate_input(data,check):
 P,Q,b,a,g,G=parameters(data)
 check(tuple(P)==PRIVATE_PRIMES,'Declared private support')
 check(data['masks']==[510,0],'Declared starting selected split')
 head=head_weights(data)
 for h,root in ((5,1),(7,2)):
  lam=[F(x) for x in data['common_head_laws'][str(h)]]
  check(len(lam)==h and sum(lam)==1 and all(0<=x<=a[h] for x in lam),'Common head law and cap')
  for r in (1,2):
   check(len(head[r][h])==h,'Head row count')
   loss=[F(x) for x in data['head_star_losses'][str(r)][str(h)]]
   check(len(loss)==h and all(0<=loss[i]<=lam[i] and head[r][h][i]==lam[i]-loss[i] for i in range(h)),'Shared head law and declared star losses')
   check(sum(head[r][h])==g[r][h],'Required fixed head carrier mass')
  loss=[F(x) for x in data['head_star_losses'][str(root)][str(h)]]
  check(loss[0]==lam[0]==a[h] and loss[1]==b[h]-a[h] and all(loss[i]==0 for i in range(2,h)),'Whole first head row plus the shared deep tail in row one')
 for r in (1,2):
  check(all(F(int(x*15),15)==x for x in head[r][5]) and all(F(int(x*35),35)==x for x in head[r][7]),'Exact integer head scaling')
 arrays,_=validate_source(data,data['common_rows'],tuple(data['masks']),check)
 for r in (1,2):
  for h in HEADS:
   supplied=[[F(x) for x in row] for row in data['arrays'][str(r)][str(h)]]
   check(supplied==arrays[r][h],'Input raw arrays match common token addresses and ownership')
 return arrays

def build_evaluator(data):
 """Return the exact integer evaluator for the input's fixed head weights."""
 P=data['private_primes'];n=len(P);N=1<<n;head=head_weights(data)
 iw={r:[int(x*15) for x in head[r][5]] for r in (1,2)}
 iv={r:[int(x*35) for x in head[r][7]] for r in (1,2)}
 D={r:[q-2 if r==1 else q-3 for q in P] for r in (1,2)}
 den=525*prod(q-2 for q in P)
 cellweight={r:[iw[r][i]*iv[r][j] for i in range(5) for j in range(7)] for r in (1,2)}
 weightedcells={r:[(c,w) for c,w in enumerate(cellweight[r]) if w] for r in (1,2)}
 substep=[None]+[((m&-m).bit_length()-1,m^(m&-m)) for m in range(1,N)]
 private_count=[n-m.bit_count() for m in range(N)]
 def rawnums(rows,r,selected):
  X=[];Y=[]
  for t,(f5,s5,f7,s7) in enumerate(rows):
   X.append([int(i==f5)+int(selected[5][t]==r and i==s5) for i in range(5)])
   Y.append([int(j==f7)+int(selected[7][t]==r and j==s7) for j in range(7)])
  return X,Y

 def evaluate(rows,masks):
  selected=owners(masks,n)
  num,weightden=1,2
  other=weightden-num
  tab={};residual={}
  for r in (1,2):
   X,Y=rawnums(rows,r,selected)
   fac=[[D[r][t]-max(X[t][i],Y[t][j]) for i in range(5) for j in range(7)] for t in range(n)]
   table=[[1]*35]+[None]*(N-1)
   for m in range(1,N):
    t,old=substep[m];a=table[old];b=fac[t]
    table[m]=[a[c]*b[c] for c in range(35)]
   tab[r]=table
   residual[r]=sum(w*prod(D[r][t]-X[t][c//7]-Y[t][c%7] for t in range(n)) for c,w in weightedcells[r])
  free=0;sel=0
  for m,k in enumerate(private_count):
   z1=tab[1][m];z2=tab[2][m]
   if k>=2:
    a=num*sum(w*z1[c] for c,w in weightedcells[1]);b=other*sum(w*z2[c] for c,w in weightedcells[2])
    free+=a+b;sel+=max(a,b)
   if k>=1:
    # Head 5 fixed: coefficient 5, or 1 when precisely one private prime belongs to D.
    c5=1 if k==1 else 5
    a=[num*sum(iv[1][j]*z1[7*i+j] for j in range(7)) for i in range(5)]
    b=[other*sum(iv[2][j]*z2[7*i+j] for j in range(7)) for i in range(5)]
    free+=c5*max(a[i]+b[i] for i in range(5));sel+=c5*max(max(a),max(b))
    # Head 7 fixed: coefficient 7, or 1 for the same single-private exception.
    c7=1 if k==1 else 7
    a=[num*sum(iw[1][i]*z1[7*i+j] for i in range(5)) for j in range(7)]
    b=[other*sum(iw[2][i]*z2[7*i+j] for i in range(5)) for j in range(7)]
    free+=c7*max(a[j]+b[j] for j in range(7));sel+=c7*max(max(a),max(b))
   # Both heads fixed. Their ordinary cap product has numerator 5*7.
   free+=35*max(num*z1[c]+other*z2[c] for c in range(35))
   sel+=35*max(num*max(z1),other*max(z2))
  rr=num*residual[1]+other*residual[2]
  return {'residual':rr,'free':free,'selected':sel,'score':rr-free-sel,'denominator':weightden*den,'root_residual_numerators':residual}
 return evaluate

def bounded_search(evaluate,rows0,initial_masks,check,baseline=None):
 """Run the unchanged six-by-four search; retain aggregate counts and one winner."""
 n=len(rows0)
 if baseline is None:baseline=evaluate(rows0,initial_masks)
 start=time.perf_counter();starts_completed=0;rounds=0;neighbor_evaluations=0;accepted_moves=0
 best_e=baseline;best_rows=[x.copy() for x in rows0];best_masks=initial_masks;best_origin={'seed':0,'origin':'baseline'}
 found=baseline['score']<=0
 for seed in range(6):
  if found:break
  rows=[[(row[0]+seed)%5,(row[1]+seed)%5,(row[2]+seed)%7,(row[3]+seed)%7] for row in rows0]
  masks=initial_masks;e=evaluate(rows,masks)
  if e['score']<best_e['score']:
   best_e=e;best_rows=[x.copy() for x in rows];best_masks=masks;best_origin={'seed':seed,'origin':'starting_state'}
  if e['score']<=0:found=True;starts_completed+=1;break
  for round_index in range(4):
   round_e=e;round_rows=rows;round_masks=masks;local_count=0
   for q in range(n):
    for slot,limit in enumerate((5,5,7,7)):
     for target in range(limit):
      if target==rows[q][slot]:continue
      candidate=[x.copy() for x in rows];candidate[q][slot]=target
      candidate_e=evaluate(candidate,masks);local_count+=1
      if candidate_e['score']<round_e['score']:
       round_e=candidate_e;round_rows=candidate;round_masks=masks
   for which in range(2):
    for bit in range(n):
     candidate_masks=list(masks);candidate_masks[which]^=1<<bit;candidate_masks=tuple(candidate_masks)
     candidate_e=evaluate(rows,candidate_masks);local_count+=1
     if candidate_e['score']<round_e['score']:
      round_e=candidate_e;round_rows=rows;round_masks=candidate_masks
   check(local_count==198,'One entire 180-row plus 18-bit neighborhood')
   neighbor_evaluations+=local_count;rounds+=1
   if round_e['score']>=e['score']:break
   e=round_e;rows=[x.copy() for x in round_rows];masks=round_masks;accepted_moves+=1
   if e['score']<best_e['score']:
    best_e=e;best_rows=[x.copy() for x in rows];best_masks=masks;best_origin={'seed':seed,'origin':'accepted_neighbor'}
   if e['score']<=0:found=True;break
  starts_completed+=1
 search_seconds=time.perf_counter()-start
 check(starts_completed<=6 and rounds<=24 and neighbor_evaluations<=4752,'Declared finite search budget')
 check(evaluate(best_rows,best_masks)['score']==best_e['score'],'Final winning state reevaluation')
 return {'baseline':baseline,'best':best_e,'rows':best_rows,'masks':best_masks,
  'nonpositive_found':found,'origin':best_origin,
  'counts':{'starts_completed':starts_completed,'complete_rounds':rounds,'neighbor_evaluations':neighbor_evaluations,'accepted_moves':accepted_moves},
  'seconds':search_seconds}

def validate_source(data,rows,masks,check):
 """Reconstruct literal shared free/selected masses and verify the source caps."""
 P,Q,b,a,g,G=parameters(data);n=len(P);selected=owners(masks,n)
 check(len(rows)==n and all(len(row)==4 and all(type(x) is int and 0<=x<limit for x,limit in zip(row,(5,5,7,7))) for row in rows),'Valid physical token rows')
 check(len(masks)==2 and all(type(x) is int and 0<=x<(1<<n) for x in masks),'Valid selected-ownership bits')
 arr={r:{5:[],7:[]} for r in (1,2)};sources={}
 for t,q in enumerate(P):
  check(5*b[q]<=1,'Five disjoint q tokens fit the common private source')
  sources[str(q)]={}
  for h,slot in ((5,0),(7,2)):
   f=[b[q] if i==rows[t][slot] else F(0) for i in range(h)]
   s={r:[b[q] if selected[h][t]==r and i==rows[t][slot+1] else F(0) for i in range(h)] for r in (1,2)}
   check(sum(f)==b[q] and sum(s[1])+sum(s[2])==b[q],'Common free and shared selected budget')
   for r in (1,2):
    x=[(f[i]+s[r][i])/g[r][q] for i in range(h)];arr[r][h].append(x)
    check(sum(x)==(b[q]+(b[q] if selected[h][t]==r else 0))/g[r][q],'Exact final per-root raw budget')
    check(all(0<=f[i]+s[r][i]<=g[r][q] for i in range(h)),'Same-row private carrier capacity')
   check(all(g[2][q]*arr[2][h][t][i]-arr[1][h][t][i]==s[2][i]-s[1][i] for i in range(h)),'Exact common-source positive-part bridge')
   check(sum(max(F(0),g[2][q]*arr[2][h][t][i]-arr[1][h][t][i]) for i in range(h))<=sum(s[2]),'Final positive-part inequality')
   sources[str(q)][str(h)]={'free':[str(x) for x in f],'selected_increment':{str(r):[str(x) for x in s[r]] for r in (1,2)}}
 check(all(1-arr[r][5][t][i]-arr[r][7][t][j]>0 for r in (1,2) for t in range(n) for i in range(5) for j in range(7)),'Final residual guard')
 return arr,sources

def fraction_evaluate(data,arr):
 """Independent direct products and physical-address maxima, with Fractions."""
 P,Q,b,a,g,G=parameters(data);n=len(P);head=head_weights(data)
 omega={1:F(1,2),2:F(1,2)}
 slowres=sum((omega[r]*G[r]*sum((head[r][5][i]*head[r][7][j]*prod((1-arr[r][5][t][i]-arr[r][7][t][j] for t in range(n)),start=F(1)) for i in range(5) for j in range(7)),F(0)) for r in (1,2)),F(0))
 slowfree=F(0);slowsel=F(0);supports=0
 for size in range(2,len(Q)+1):
  for support in combinations(Q,size):
   supports+=1;R=prod((b[p] for p in support),start=F(1))
   if size==2 and support[0] in (5,7) and support[1]>7:R=(b[support[0]]-a[support[0]])*b[support[1]]
   fixed=tuple(h for h in (5,7) if h in support);addresses=list(product(*(range(h) for h in fixed)))
   table={r:{} for r in (1,2)}
   for r in (1,2):
    Gout=prod((g[r][q] for q in P if q not in support),start=F(1))
    M=[[prod((1-max(arr[r][5][t][i],arr[r][7][t][j]) for t,q in enumerate(P) if q not in support),start=F(1)) for j in range(7)] for i in range(5)]
    for address in addresses:
     ai=dict(zip(fixed,address));K=F(0)
     for i in ([ai[5]] if 5 in ai else range(5)):
      for j in ([ai[7]] if 7 in ai else range(7)):
       K+=(F(1) if 5 in ai else head[r][5][i])*(F(1) if 7 in ai else head[r][7][j])*M[i][j]
     table[r][address]=Gout*K
   slowfree+=R*max(sum((omega[r]*table[r][address] for r in (1,2)),F(0)) for address in addresses)
   slowsel+=R*max(omega[r]*table[r][address] for r in (1,2) for address in addresses)
 slow={'residual':slowres,'free':slowfree,'selected':slowsel,'score':slowres-slowfree-slowsel}
 return slow,supports

def fraction_record(e):
 return {'values':{k:str(F(e[k],e['denominator'])) for k in ('residual','free','selected','score')},
  'score_decimal':float(F(e['score'],e['denominator'])),
  'integer_numerators':{k:str(e[k]) for k in ('residual','free','selected','score')},
  'denominator':str(e['denominator'])}

def produce(data,input_hash):
 """Validate input, run the fixed search and independently certify its final array."""
 checks=Checks();check=checks.require
 validate_input(data,check)
 evaluate=build_evaluator(data)
 baseline=evaluate(data['common_rows'],tuple(data['masks']))
 # Existing paired objectives bind the initial rows to the source input when present.
 if 'objectives' in data:
  P,Q,b,a,g,G=parameters(data);unweighted_den=baseline['denominator']//2
  for r in (1,2):
   carrier=prod(g[r].values(),start=F(1))
   check(carrier-F(baseline['root_residual_numerators'][r],unweighted_den)==F(data['objectives'][str(r)]),'Input paired objective agrees with raw source')
 search=bounded_search(evaluate,data['common_rows'],tuple(data['masks']),check,baseline)
 arr,sources=validate_source(data,search['rows'],search['masks'],check)
 start=time.perf_counter();slow,supports=fraction_evaluate(data,arr)
 for k,value in slow.items():
  check(F(search['best'][k],search['best']['denominator'])==value,'Independent final Fraction '+k+' equality')
 check(supports==2036,'Complete independent support inventory')
 slow_seconds=time.perf_counter()-start
 return {
  'contract':'Bounded falsification attempt at gamma=1/2 with fixed first-layer heads and common private source. Six deterministic common-shift starts, at most four complete 198-neighbor rounds each, strict descent only. No global minimum, uniform positivity or AP realization is asserted.',
  'input_sha256':input_hash,
  'search_bound':{'starts':6,'maximum_rounds_per_start':4,'row_neighbors_per_round':180,'selected_split_neighbors_per_round':18,
   'start_rule':'Seed s=0,...,5: add s mod 5 to both head5 token rows and s mod 7 to both head7 token rows at every q. Initial masks are (510,0).',
   'acceptance':'Finish all 198 neighbors, accept a strictly lower best neighbor; ties do not move. Stop a start on no improvement, or stop globally at a nonpositive starting or accepted state.'},
  'actual_counts':search['counts'],'gamma':'1/2','private_primes':data['private_primes'],
  'baseline':fraction_record(search['baseline']),'minimum_found':fraction_record(search['best']),
  'nonpositive_found':search['nonpositive_found'],'minimum_origin':search['origin'],
  'final_masks':list(search['masks']),'final_rows':search['rows'],
  'head_weights':data['head_weights'],'common_head_laws':data['common_head_laws'],'head_star_losses':data['head_star_losses'],
  'private_sources':sources,'arrays':{str(r):{str(h):[[str(x) for x in row] for row in arr[r][h]] for h in HEADS} for r in (1,2)},
  'cost_seconds':{'bounded_search':search['seconds'],'mean_per_neighbor':search['seconds']/search['counts']['neighbor_evaluations'] if search['counts']['neighbor_evaluations'] else 0,'independent_fraction_final':slow_seconds},
  'checks':checks.count,
  'limits':['Only the fixed finite search was performed; a positive result is not a uniform lower bound or local minimum.',
   'Common abstract-source constraints are verified; full prime-adic/AP realizability is not claimed.',
   'No additional head profile, private-star profile, root weight or search budget, and no Lean verification.']}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--input',required=True,help='Canonical first_layer_witness.json with common heads, losses, token rows, ownership masks and raw arrays.')
 parser.add_argument('--output',required=True,help='Final exact arrays, bounded-search summary and input hash.')
 args=parser.parse_args();raw=Path(args.input).read_bytes();data=json.loads(raw)
 result=produce(data,sha256(raw).hexdigest())
 Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'checks':result['checks'],'counts':result['actual_counts'],'nonpositive_found':result['nonpositive_found'],
  'best_score':result['minimum_found']['values']['score'],'best_decimal':result['minimum_found']['score_decimal'],
  'final_masks':result['final_masks'],'timings':result['cost_seconds']},sort_keys=True))

if __name__=='__main__':
 main()
