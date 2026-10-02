"""Evaluate same-array residual/remainder bounds on stored witnesses.
No array search, root-weight optimization or uniform certificate is asserted.
"""
import argparse,json
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
from itertools import combinations,product
from math import prod
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--witness',action='append',required=True,
                help='Explicit witness JSON; repeat for distinct named witnesses')
ap.add_argument('--output',required=True)
args=ap.parse_args()
checks=0
def need(ok,msg):
 global checks
 checks+=1
 if not ok:raise ValueError(msg)
Q=[5,7,11,13,17,19,23,29,31,37,41];P=Q[2:]
b={p:F(1,p-2) for p in Q};a={h:F(h-1,h*(h-2)) for h in (5,7)}
g={1:{p:1-b[p] if p==5 else F(1) for p in Q},2:{p:F(1) if p==5 else 1-b[p] for p in Q}}
G={r:prod((g[r][q] for q in P),start=F(1)) for r in (1,2)}
W={r:prod(g[r].values(),start=F(1)) for r in (1,2)}
supports=[]
for n in range(2,len(Q)+1):
 for D in combinations(Q,n):
  R=prod((b[p] for p in D),start=F(1))
  if n==2 and D[0] in (5,7) and D[1]>7:R=(b[D[0]]-a[D[0]])*b[D[1]]
  H={r:prod((g[r][p] for p in Q if p not in D),start=F(1)) for r in (1,2)}
  supports.append((D,R,H))
need(len(supports)==2036,'Same complete non-group support inventory')
results={};source_hashes={}
for path in args.witness:
 tag=Path(path).stem
 need(tag not in results,'Each supplied witness has a unique filename stem')
 raw=Path(path).read_bytes();d=json.loads(raw);source_hashes[tag]=sha256(raw).hexdigest()
 need(d['private_primes']==P and d['masks']==[510,0],'Declared stored common-row witness')
 head={r:{h:[F(x) for x in d['head_weights'][str(r)][str(h)]] for h in (5,7)} for r in (1,2)}
 arr={r:{h:[[F(x) for x in row] for row in d['arrays'][str(r)][str(h)]] for h in (5,7)} for r in (1,2)}
 for r in (1,2):
  need(sum(head[r][5])==g[r][5] and sum(head[r][7])==g[r][7],'Head totals unchanged')
  need(all(F(0)<=arr[r][5][t][i]+arr[r][7][t][j]<1 for t in range(len(P)) for i in range(5) for j in range(7)),'Nonnegative exact residual guard')
 residual={r:G[r]*sum((head[r][5][i]*head[r][7][j]*prod((1-arr[r][5][t][i]-arr[r][7][t][j] for t in range(len(P))),start=F(1)) for i in range(5) for j in range(7)),F(0)) for r in (1,2)}
 need(all(residual[r]==W[r]-F(d['objectives'][str(r)]) for r in (1,2)),'Exact same-array group residual agrees with stored objective')
 # The K table is independent of root weight. Each support uses common addresses.
 tables=[]
 for D,R,H in supports:
  fixed=tuple(h for h in (5,7) if h in D)
  addresses=list(product(*(range(h) for h in fixed)))
  table={r:{} for r in (1,2)}
  for r in (1,2):
   M=[[prod((1-max(arr[r][5][t][i],arr[r][7][t][j]) for t,q in enumerate(P) if q not in D),start=F(1)) for j in range(7)] for i in range(5)]
   Gout=prod((g[r][q] for q in P if q not in D),start=F(1))
   for address in addresses:
    ai=dict(zip(fixed,address))
    K=F(0)
    for i in ([ai[5]] if 5 in ai else range(5)):
     for j in ([ai[7]] if 7 in ai else range(7)):
      weight=(F(1) if 5 in ai else head[r][5][i])*(F(1) if 7 in ai else head[r][7][j])
      K+=weight*M[i][j]
    value=Gout*K
    need(0<=value<=H[r],'Each conditioned address fee is dominated by old marginal support bound')
    table[r][address]=value
  tables.append((D,R,H,addresses,table))
 points=sorted({F(1,2),*(F(x) for x in d['maximizing_weights'])})
 point_results=[]
 for gamma in points:
  omega={1:gamma,2:1-gamma}
  free=F(0);selected=F(0);oldfree=F(0);oldselected=F(0)
  by_head_support={}
  for D,R,H,addresses,table in tables:
   f=R*max(sum((omega[r]*table[r][address] for r in (1,2)),F(0)) for address in addresses)
   s=R*max(omega[r]*table[r][address] for r in (1,2) for address in addresses)
   of=R*sum((omega[r]*H[r] for r in (1,2)),F(0))
   os=R*max(omega[r]*H[r] for r in (1,2))
   need(0<=f<=of and 0<=s<=os,'New free and selected same-array fees each dominated by old fee')
   free+=f;selected+=s;oldfree+=of;oldselected+=os
   key=','.join(str(h) for h in (5,7) if h in D) or 'none'
   bucket=by_head_support.setdefault(key,{'support_count':0,'free_fee':F(0),'selected_fee':F(0),'old_free_fee':F(0),'old_selected_fee':F(0)})
   bucket['support_count']+=1
   for name,value in (('free_fee',f),('selected_fee',s),('old_free_fee',of),('old_selected_fee',os)):bucket[name]+=value
  rr=sum((omega[r]*residual[r] for r in (1,2)),F(0))
  new=rr-free-selected;old=rr-oldfree-oldselected
  need(new>=old,'Joint-remainder score dominates old score on identical arrays')
  if str(gamma) in d['maximizing_weights']:
   need(old==F(d['best_certificate_upper_bound']),'Old-peak score matches independent stored all-weight result')
  point_results.append({'gamma':str(gamma),'gamma_decimal':float(gamma),'weighted_group_residual':str(rr),
    'joint_free_fee':str(free),'joint_selected_fee':str(selected),'old_free_fee':str(oldfree),'old_selected_fee':str(oldselected),
    'joint_score':str(new),'joint_score_decimal':float(new),'old_score':str(old),'old_score_decimal':float(old),
    'gain':str(new-old),'gain_decimal':float(new-old),'positive':new>0,
    'by_head_support':{key:{name:value if name=='support_count' else str(value) for name,value in bucket.items()} for key,bucket in by_head_support.items()}})
 results[tag]={'witness_path':path,'root_residuals':{str(r):str(residual[r]) for r in (1,2)},'points':point_results}
out={'contract':'Finite evaluation of explicitly supplied common-source arrays under the new same-array residual and joint remainder functional. Positive fixed-array values do not establish a uniform lower bound or an AP-family realization and do not prove Erdős #7.',
 'source_sha256':source_hashes,'support_count':len(supports),'results':results,'checks':checks,
 'limits':['Exactly two predeclared gamma values per stored array, not an optimization over gamma.','No new array search and no minimization over feasible sources.','Joint fee uses 1-max(x,y), an upper bound on true per-coordinate survivor even with overlap, while group residual uses 1-x-y.','No Lean verification or unrestricted E7 conclusion.']}
Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'results':{tag:[{k:p[k] for k in ('gamma','joint_score_decimal','old_score_decimal','gain_decimal','positive')} for p in result['points']] for tag,result in results.items()}},sort_keys=True))
