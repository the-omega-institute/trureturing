from fractions import Fraction as F
from itertools import combinations,product
from math import prod,ceil
from pathlib import Path
import json
P=(3,5,7,11,13,17,19);Q=P[1:]
E={(5,7),(5,11),(7,17),(7,19),(11,17),(11,19),(13,17),(13,19),(17,19),(11,13)}
H=tuple(S for n in (3,4) for S in combinations((11,13,17,19),n))
checks=[]
def need(n,v):
 if not v or n in checks:raise RuntimeError(n)
 checks.append(n)
def calc(x,tau=6,order=Q):
 T={5:F(0),7:F(1),11:F(3),13:F(x),17:F(5),19:F(7)}
 C={3:F(2),**{p:F(p-1)/(p-2-T[p]) for p in Q}}
 g={p:C[p]/(p-1) for p in P}
 def atom(p,k):return 1-C[p]/p if k==0 else C[p]*F(p-1,p**(k+1))
 rows={}
 for q in order:
  prev=order[:order.index(q)];nbr={p for p in prev if tuple(sorted((p,q))) in E};higher=tuple(tuple(p for p in S if p!=q) for S in H if q in S and all(order.index(p)<order.index(q) for p in S if p!=q))
  top=ceil(T[q])-1;low={m:F(0) for m in range(top+1)}
  for k in range(top+1):
   weights={p:k+int(p in nbr) for p in prev};active=tuple(p for p in prev if weights[p])
   if any(p not in active for S in higher for p in S):raise RuntimeError('unbounded low variable')
   for vals in product(*(range((top-k)//weights[p]+1) for p in active)):
    K=dict(zip(active,vals));m=k+sum(weights[p]*K[p] for p in active)+sum(prod(K[p] for p in S) for S in higher)
    if m<=top:low[m]+=atom(3,k)*prod((atom(p,K[p]) for p in active),start=F(1))
  mean=g[3]*(1+sum((g[p] for p in prev),F(0)))+sum((g[p] for p in nbr),F(0))+sum((prod((g[p] for p in S),start=F(1)) for S in higher),F(0))
  hinge=mean-T[q]+sum(((T[q]-m)*w for m,w in low.items()),F(0))
  rows[q]=hinge/(q-2-T[q])
 low={1:F(1)}
 for p in P:
  nxt={}
  for m,w in low.items():
   for k in range((tau-1)//m):nxt[m*(k+1)]=nxt.get(m*(k+1),F(0))+w*atom(p,k)
  low=nxt
 B=prod((1+g[p] for p in P),start=F(1))-tau+sum(((tau-m)*w for m,w in low.items()),F(0))
 s=1-sum(rows.values());gate=(566-49*(tau-1))*s-49*B
 return {'t13':x,'C13':C[13],'rows':rows,'s':s,'B':B,'gate':gate,'query_upper':tau-1+B/s if s>0 else None}
ends=[F(i) for i in range(11)]+[F(131,13)]
results=[calc(x) for x in ends]
for r in results:
 need('negative endpoint '+str(r['t13']),r['gate']<0)
 need('valid13 probability '+str(r['t13']),0<r['C13']<=13)
best=max(results,key=lambda r:r['gate'])
need('fixed certificate axis maximum at4',best['t13']==4)
need('exact baseline gap',best['gate']==-F(61130862008692144789840832309162232590105353,24767698132439755831791956763118299065625000))
need('exact baseline query',best['query_upper']==F(221294827808311479918971820535562561922234425,18834017626468526646042573691369397237489701))
# Check the affine-in-y statement at one interior rational of every cell.
# Its general proof is given in the companion note, not inferred from these.
for a,b in zip(ends,ends[1:]):
 m=(a+b)/2;r=calc(m);ra=next(z for z in results if z['t13']==a);rb=next(z for z in results if z['t13']==b)
 y=1/(11-m);ya=1/(11-a);yb=1/(11-b);l=(y-ya)/(yb-ya)
 need('fractional interpolation '+str(a),r['gate']==(1-l)*ra['gate']+l*rb['gate'])
# All useful complete-query hinge thresholds. For V>=1 and0<s<=1,
# tau<1 is no better than1, and tau>=13 has a negative target gate.
query_corners=[]
for a in ends:
 for tau in range(1,13):
  r=calc(a,tau);query_corners.append({'t13':a,'tau':tau,**r})
  need('negative joint threshold corner '+str(a)+' '+str(tau),r['gate']<0)
  need('positive source reserve corner '+str(a)+' '+str(tau),0<r['s']<=1)
joint_best=max(query_corners,key=lambda r:r['gate'])
need('joint threshold maximum remains4 six',joint_best['t13']==4 and joint_best['tau']==6)
for a,b in zip(ends,ends[1:]):
 m=(a+b)/2;y=1/(11-m);ya=1/(11-a);yb=1/(11-b);l=(y-ya)/(yb-ya)
 for tau in range(1,13):
  r=calc(m,tau);ra=next(z for z in query_corners if z['t13']==a and z['tau']==tau);rb=next(z for z in query_corners if z['t13']==b and z['tau']==tau)
  need('all query affine interpolation '+str(a)+' '+str(tau),r['gate']==(1-l)*ra['gate']+l*rb['gate'])
# One adjacent reorder specifically moves the new pair to the11 row.
# Other caps, the17/19 inventories and the query law comparison stay fixed.
swap=calc(F(4),6,(5,7,13,11,17,19))
need('adjacent swap same late rows',swap['rows'][17]==best['rows'][17] and swap['rows'][19]==best['rows'][19])
need('adjacent swap same query hinge',swap['B']==best['B'])
need('adjacent swap remains negative',swap['gate']<0)
need('adjacent swap weaker scalar gate',swap['gate']<best['gate'])
# Actual irredundant originals demonstrate that shared supports do not
# force positive union credit between the new pair and the higher supports.
primes=(11,13,17,19);period=prod(primes)
roots=[{11:0,13:0},{11:1,13:1,17:1},{11:1,13:2,19:1},{11:1,17:2,19:2},{13:1,17:2,19:1},{11:2,13:2,17:2,19:2}]
def crt(mapping):
 m=1;a=0
 for p,r in mapping.items():a=(a+m*((r-a)*pow(m,-1,p)%p))%(m*p);m*=p
 return a,m
originals=[crt(r) for r in roots]
need('six actual odd distinct numerical labels',len({m for a,m in originals})==6 and all(m>1 and m%2 for a,m in originals))
for i,r in enumerate(roots):
 full={p:r.get(p,0) for p in primes};w,_=crt(full)
 need('literal private point '+str(i),[j for j,(a,m) in enumerate(originals) if w%m==a]==[i])
for i in range(1,6):
 need('pair disjoint high event '+str(i),any(p in roots[i] and roots[0][p]!=roots[i][p] for p in roots[0]))
pair_count=0;joint_count=0
for n in range(period):
 hit_pair=n%originals[0][1]==originals[0][0]
 hit_high=any(n%m==a for a,m in originals[1:])
 pair_count+=hit_pair;joint_count+=hit_pair and hit_high
need('literal whole-period overlap zero',pair_count==323 and joint_count==0)
out={'scope':'Fixed576 schedule except the13 threshold and complete-query hinge threshold. Piecewise interpolation covers both continuous axes, not arbitrary schedules or sources.','endpoints':results,'query_corners':query_corners,'joint_best':joint_best,'best':best,'mass_improvement_needed':-best['gate']/321,'adjacent_swap':swap,'actual_zero_overlap':{'period':period,'originals':[{'a':a,'m':m} for a,m in originals],'pair_count':pair_count,'joint_count':joint_count},'checks':checks,'check_count':len(checks)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,default=str,indent=2)+'\n')
print('PASS',len(checks),'exact checks')
print('best t13',best['t13'],'query',float(best['query_upper']),'gate',float(best['gate']))
print('last admissible endpoint gate',float(results[-1]['gate']))
