"""Bounded first-layer-compatible head witness and exact independent certification.
No AP realization, optimizer completeness or Lean verification is asserted.
"""
import argparse,json
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from itertools import combinations
from math import prod,lcm
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',required=True)
ap.add_argument('--shared-result',required=True)
ap.add_argument('--output',required=True)
ap.add_argument('--heads',required=True)
args=ap.parse_args()
raw=Path(args.input).read_bytes();data=json.loads(raw)
sraw=Path(args.shared_result).read_bytes();shared=json.loads(sraw)
hraw=Path(args.heads).read_bytes();profile=json.loads(hraw)
checks=0
def need(ok,msg):
 global checks
 checks+=1
 if not ok:raise ValueError(msg)
Q=data['primes'];P=[q for q in Q if q>7]
need(Q==[5,7,11,13,17,19,23,29,31,37,41],'Declared prime support')
need(shared['input_sha256']==sha256(raw).hexdigest(),'Same source input')
b={p:F(1,p-2) for p in Q};a={p:F(p-1,p*(p-2)) for p in (5,7)}
g={1:{p:1-b[p] if p==5 else F(1) for p in Q},2:{p:F(1) if p==5 else 1-b[p] for p in Q}}
W={r:prod(g[r].values(),start=F(1)) for r in (1,2)}
G={r:prod((g[r][q] for q in P),start=F(1)) for r in (1,2)}
w={r:[F(x) for x in profile['head_weights'][str(r)]['5']] for r in (1,2)}
v={r:[F(x) for x in profile['head_weights'][str(r)]['7']] for r in (1,2)}
masks=tuple(profile['masks']);target=F(311296,816493)
need(masks==(510,0),'Declared fixed split')
selected={h:[1 if (masks[t]>>j)&1 else 2 for j in range(len(P))] for t,h in enumerate((5,7))}
D={r:[q-2 if r==1 else q-3 for q in P] for r in (1,2)}
need(all((x*15).denominator==1 for r in (1,2) for x in w[r])
     and all((x*35).denominator==1 for r in (1,2) for x in v[r]),
     'Declared head profile admits exact integer weights at scales15 and35')
iw={r:[int(x*15) for x in w[r]] for r in (1,2)}
iv={r:[int(x*35) for x in v[r]] for r in (1,2)}
# Integer search cost is exactly minus the weighted FC77 objective plus a constant.
coeff={r:(target if r==1 else 1-target)*G[r]/(15*35*prod(D[r])) for r in (1,2)}
scale=lcm(*(x.denominator for x in coeff.values()))
C={r:int(coeff[r]*scale) for r in (1,2)}
# Four globally addressed rows per q: free5, selected5, free7, selected7.
def factor(r,j,i,k,rows):
 f5,s5,f7,s7=rows[j]
 return D[r][j]-(i==f5)-(selected[5][j]==r and i==s5)-(k==f7)-(selected[7][j]==r and k==s7)
def matrix(r,rows):
 return [[prod(factor(r,j,i,k,rows) for j in range(len(P))) for k in range(7)] for i in range(5)]
def cost(M):return sum(C[r]*sum(iw[r][i]*iv[r][k]*M[r][i][k] for i in range(5) for k in range(7)) for r in (1,2))
best=None
for seed in range(8):
 rows=[[0,0,0,0] if seed==0 else [(j*seed+seed)%5,(j+2*seed)%5,(j*(seed+1)+seed)%7,(j+3*seed)%7] for j in range(len(P))]
 M={r:matrix(r,rows) for r in (1,2)};initial=cost(M);moves=0
 for sweep in range(12):
  changed=False
  for j in (range(len(P)) if sweep%2==0 else range(len(P)-1,-1,-1)):
   N={r:[[M[r][i][k]//factor(r,j,i,k,rows) for k in range(7)] for i in range(5)] for r in (1,2)}
   need(all(N[r][i][k]*factor(r,j,i,k,rows)==M[r][i][k] for r in (1,2) for i in range(5) for k in range(7)),'Exact q factor removal')
   grad5={r:[C[r]*iw[r][i]*sum(iv[r][k]*N[r][i][k] for k in range(7)) for i in range(5)] for r in (1,2)}
   grad7={r:[C[r]*iv[r][k]*sum(iw[r][i]*N[r][i][k] for i in range(5)) for k in range(7)] for r in (1,2)}
   choices=([grad5[1][i]+grad5[2][i] for i in range(5)],grad5[selected[5][j]],
            [grad7[1][k]+grad7[2][k] for k in range(7)],grad7[selected[7][j]])
   old=rows[j].copy()
   for t,gradient in enumerate(choices):
    maximum=max(gradient)
    if gradient[rows[j][t]]!=maximum:rows[j][t]=gradient.index(maximum)
   if rows[j]!=old:changed=True;moves+=1
   M={r:[[N[r][i][k]*factor(r,j,i,k,rows) for k in range(7)] for i in range(5)] for r in (1,2)}
  if not changed:break
 final=cost(M)
 need(final<=initial and all(M[r]==matrix(r,rows) for r in (1,2)),'Monotone exact search and final matrices')
 if best is None or final<best[0]:best=(final,[x.copy() for x in rows])
rows=best[1]
# Exact independent witness validation on common physical rows.
lam={h:[F(x) for x in profile['common_head_laws'][str(h)]] for h in (5,7)};head={r:{5:w[r],7:v[r]} for r in (1,2)}
for h in (5,7):
 need(sum(lam[h])==1 and len(lam[h])==h,'Common original head law')
 need(all(0<=x<=a[h] for x in lam[h]),'Original head cap')
 for r in (1,2):
  loss=[lam[h][i]-head[r][h][i] for i in range(h)]
  need(all(x>=0 for x in loss) and sum(loss)==1-g[r][h],'Common-source head star loss')
  need(loss==[F(x) for x in profile['head_star_losses'][str(r)][str(h)]],'Declared head losses')
 spec=profile['first_layer_star'][str(h)];r=spec['root'];i=spec['row']
 loss=[lam[h][j]-head[r][h][j] for j in range(h)]
 need(loss[i]==lam[h][i]==a[h],'Whole depth-one row at cap')
 need(sum(loss[j] for j in range(h) if j!=i)==b[h]-a[h],'Exact full deeper-star cap outside depth-one row')
 need(all(loss[j]==0 for j in range(h) if j not in (i,spec['tail_row'])),'Deep tail in prescribed common physical row')
arrays={r:{h:[] for h in (5,7)} for r in (1,2)};sources={}
for j,q in enumerate(P):
 sources[str(q)]={}
 need(5*b[q]<=1,'One disjoint common q source can fit star and all four group tokens')
 for h,t in ((5,0),(7,2)):
  f=[b[q] if i==rows[j][t] else F(0) for i in range(h)]
  s={r:[b[q] if selected[h][j]==r and i==rows[j][t+1] else F(0) for i in range(h)] for r in (1,2)}
  need(sum(f)==b[q] and sum(s[1])+sum(s[2])==b[q],'Shared free and selected complete geometric budget')
  for r in (1,2):
   x=[(f[i]+s[r][i])/g[r][q] for i in range(h)]
   arrays[r][h].append(x)
   need(all(0<=f[i]+s[r][i]<=g[r][q] for i in range(h)),'Same-row private carrier capacity')
   need(sum(x)==(b[q]+(b[q] if selected[h][j]==r else 0))/g[r][q],'Original per-root group budget')
  need(sum(max(F(0),g[2][q]*arrays[2][h][j][i]-arrays[1][h][j][i]) for i in range(h))<=sum(s[2]),'Positive-part cross-root necessary inequality')
  need(all(g[2][q]*arrays[2][h][j][i]-arrays[1][h][j][i]==s[2][i]-s[1][i] for i in range(h)),'Exact common-free decomposition')
  sources[str(q)][str(h)]={'free':[str(x) for x in f],'selected_increment':{str(r):[str(x) for x in s[r]] for r in (1,2)}}
scores={}
for r in (1,2):
 need(all(1-arrays[r][5][j][i]-arrays[r][7][j][k]>0 for j in range(len(P)) for i in range(5) for k in range(7)),'Strict positive literal paired factors')
 scores[r]=G[r]*sum((w[r][i]*v[r][k]*(1-prod((1-arrays[r][5][j][i]-arrays[r][7][j][k] for j in range(len(P))),start=F(1))) for i in range(5) for k in range(7)),F(0))
 integer_value=W[r]-G[r]*F(sum(iw[r][i]*iv[r][k]*matrix(r,rows)[i][k] for i in range(5) for k in range(7)),15*35*prod(D[r]))
 need(scores[r]==integer_value,'Independent full Fraction objective matches search')
# Same free remainder and support maxima; no optimization of source group assignments is claimed.
supports=[];free={1:F(0),2:F(0)};events={};points={F(0),F(1)}
for size in range(2,len(Q)+1):
 for S in combinations(Q,size):
  K=prod((b[p] for p in S),start=F(1))
  if size==2 and S[0] in (5,7) and S[1]>7:K=(b[S[0]]-a[S[0]])*b[S[1]]
  H={r:prod((g[r][p] for p in Q if p not in S),start=F(1)) for r in (1,2)}
  supports.append((K,H[1],H[2]));t=H[2]/(H[1]+H[2]);points.add(t)
  ds,db=events.get(t,(F(0),F(0)));events[t]=(ds+K*(H[1]+H[2]),db-K*H[2])
  for r in (1,2):free[r]+=K*H[r]
need(all(free[r]==F(shared['root_free_remaining'][str(r)]) for r in (1,2)),'Unchanged marginal free remainder')
slope=-free[2];intercept=free[2];opt=None;weights=[]
for gamma in sorted(points):
 if gamma in events:
  ds,db=events[gamma];slope+=ds;intercept+=db
 fee=intercept+slope*gamma
 value=gamma*(W[1]-free[1]-scores[1])+(1-gamma)*(W[2]-free[2]-scores[2])-fee
 if opt is None or value>opt:opt=value;weights=[gamma]
 elif value==opt:weights.append(gamma)
gamma=weights[0]
fee=sum((K*max(gamma*H1,(1-gamma)*H2) for K,H1,H2 in supports),F(0))
need(opt==gamma*(W[1]-free[1]-scores[1])+(1-gamma)*(W[2]-free[2]-scores[2])-fee,'Independent fee reevaluation')
out={'contract':'Common physical head laws with measurable head star losses, shared free raw vectors, and selected increments. A bounded feasible witness with complete depth-one head rows and the exact deeper-star cap in a second row, in a stronger subclass of the positive-part cross-root relaxation. Abstract common probability source exists; no AP realization is claimed. All-weight obstruction uses unchanged marginal remainder fees.',
'input_sha256':sha256(raw).hexdigest(),'shared_result_sha256':sha256(sraw).hexdigest(),'head_input_sha256':sha256(hraw).hexdigest(),
'masks':list(masks),'private_primes':P,'search_weight':str(target),'search_bound':{'starts':8,'maximum_sweeps_per_start':12},
'first_layer_star':profile['first_layer_star'],'head_star_losses':profile['head_star_losses'],'common_rows':rows,'common_head_laws':{str(h):[str(x) for x in lam[h]] for h in (5,7)},
'head_weights':{str(r):{str(h):[str(x) for x in head[r][h]] for h in (5,7)} for r in (1,2)},
'private_sources':sources,'arrays':{str(r):{str(h):[[str(x) for x in a] for a in arrays[r][h]] for h in (5,7)} for r in (1,2)},
'objectives':{str(r):str(scores[r]) for r in (1,2)},'objective_decimals':{str(r):float(scores[r]) for r in (1,2)},
'weight_candidate_count':len(points),'maximizing_weights':[str(x) for x in weights],
'best_certificate_upper_bound':str(opt),'best_certificate_upper_bound_decimal':float(opt),
'rules_out_common_free_relaxation_with_same_remainder':opt<0,'checks':checks,
'limits':['Fixed star pattern, declared finite prime support, ternary height at most one and complete geometric nonternary budgets; full depth-one head rows and one-row deeper-tail caps retained.','No arithmetic progression realization, unrestricted E7 resolution or Lean verification.','Does not rule out a smaller actual-source feasible set or joint group/remainder payment.']}
Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'objectives':out['objective_decimals'],'best_gamma':str(gamma),'best_certificate_upper':float(opt),'negative':opt<0,'common_rows':rows},sort_keys=True))
