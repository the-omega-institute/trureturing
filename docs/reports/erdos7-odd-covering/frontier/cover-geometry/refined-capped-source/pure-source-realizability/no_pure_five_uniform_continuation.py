"""One exact evaluation of two fixed tables under the no-pure5 source cap.
No solver, tuning or extra cuts. All source/head/hinge/moment caps changed together.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod,lcm,comb,factorial,isqrt
from pathlib import Path
import json,argparse
here=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--certificate',type=Path,default=here/'no_pure_five_uniform_continuation_certificate.json')
parser.add_argument('--result',type=Path,default=here/'no_pure_five_uniform_continuation.json')
parser.add_argument('--write-result',action='store_true')
args=parser.parse_args()
certificate=json.loads(args.certificate.read_text())
cs=[dict(certificate['source'],**t) for t in certificate['tables']]
Q=(5,7,11,13,17,19,23);leaves=(4,7,2,5,8)
C=(F(20,19),)+tuple(F(q-1,q-2) for q in Q[1:])
checks=0
def need(ok,msg):
 global checks
 checks+=1
 if not ok:raise ValueError(msg)
def a4(q):
 t=F(1,q-1);return 15*t+50*t*t+60*t**3+24*t**4

# All-height absent-prime cap and sharpness controls; general proof is in the
# companion note. These are finite same-union calculations, not a sampled proof.
for q in (3,5,7,11,13,17,19,23):
 B=F(1,q*(q-1));cap=1/(1-B)
 need(cap==F(q*(q-1),q*q-q-1),'absence cap identity')
 for E in (2,3,4):
  d=sum((F(1,q**j) for j in range(2,E+1)),F(0))
  need(d<B and 1/(1-d)<cap,'finite comb approaches strict all-height cap')
need(C[0]==1/(1-F(1,20)),'C5 absence cap20/19')
need(certificate['schema']=='e7-no-pure5-uniform-fixed-source-v1' and certificate['missing_pure_label']==5,'declared absence case')
need(len(cs)==2 and [c['name'] for c in cs]==['quarter','point812'],'declared fixed table order')
base=cs[0];family=dict(base['actual_family']);selected=base['selected_labels']
literal_family=[(3,0),(9,1),(15,10),(21,7),(45,11),(33,22),(35,0),(39,13),
 (63,49),(51,34),(57,19),(55,0),(105,70),(75,25),(69,46),(65,0),(99,22),
 (77,0),(85,0),(117,13),(95,0),(165,55),(91,0),(147,49),(225,175)]
need(base['primes']==list(Q) and base['leaves']==list(leaves) and base['threshold']==16,'literal source coordinates andh16')
need(len(family)==len(base['actual_family']) and all(type(m)is int and type(a)is int and m>1 and m%2 and 0<=a<m for m,a in base['actual_family']),'actual distinct odd nonunit originals')
parts=[[[0],[1],[2,3,4]]]+[[[0],list(range(1,q))] for q in Q[1:]]
patterns=list(product(range(3),*[range(2) for _ in range(6)]))
need(family==dict(literal_family) and len(set(selected))==len(selected)==23 and set(selected)==set(family)-{3,9},'same literal25 original source')
need(5 not in family and family[45]==11 and family[3]==0 and family[9]==1,'specified selected phases and no selected pure5')
beta=[prod((C[i]/(q-1) for i,q in enumerate(Q) if D>>i&1),start=F(1)) for D in range(128)]
need(beta[1]==F(5,19),'new five-axis complete inventory factor')
R=[[beta[D] if D and (h or D.bit_count()>1) else F(0) for D in range(128)] for h in range(3)]
forced=set()
for m in selected:
 a=family[m];n=m;h=0
 while n%3==0:n//=3;h+=1
 ids=[i for i,q in enumerate(Q) if n%q==0];D=sum(1<<i for i in ids)
 nrem=n
 for i in ids:
  while nrem%Q[i]==0:nrem//=Q[i]
 need(nrem==1 and n>1 and h<=2 and (h or len(ids)>1),'selected complete-inventory membership')
 R[h][D]-=prod((C[i] for i in ids),start=F(1))/n
 for sid,s in enumerate(patterns):
  if all(a%Q[i] in parts[i][s[i]] for i in ids):
   for l,leaf in enumerate(leaves):
    if leaf%3**h==a%3**h:forced.add((l,sid))
need(len(forced)==750 and min(x for row in R for x in row)>=0,'same K8 and new complete nonnegative residual inventory')
scale=lcm(*(F(x['u']).denominator for c in cs for x in c['nonzero_u']))
U=[[0]*10 for s in patterns];weights=[]
for ci,c in enumerate(cs):
 need(c['actual_family']==base['actual_family'] and c['selected_labels']==selected and c['partitions']==parts,'literal source/table interface unchanged')
 w=list(map(F,c['weights']));weights.append(w);need(len(w)==5 and sum(w)==1 and min(w)>=0,'fixed normalized weights')
 seen=set()
 for x in c['nonzero_u']:
  l,sid,v=x['leaf_index'],x['pattern_id'],F(x['u'])
  need(type(l)is int and type(sid)is int and 0<=l<5 and 0<=sid<192,'literal retained cell indices')
  need((l,sid) not in seen and (l,sid) not in forced and 0<v<=w[l],'fixed retained table valid literalcell')
  seen.add((l,sid));U[sid][ci*5+l]=int(v*scale)

need(weights[0]==[F(1,4),F(1,4),F(1,6),F(1,6),F(1,6)],'fixed quarter law')
for sid in range(192):
 for l in range(5):need(F(U[sid][l],scale)==(F(0) if (l,sid) in forced else weights[0][l]),'quarter retains exactly every permitted cell')

# Complete hinge with changed C5 at every depth, including the infinite mean.
@lru_cache(None)
def pmf(k,n):
 if k==0:return F(n==1)
 q=Q[k-1];cq=C[k-1]
 def tail(e):return F(1) if e==0 else cq/q**e
 return sum(((tail(d-1)-tail(d))*pmf(k-1,n//d) for d in range(1,n+1) if n%d==0),F(0))
mean=prod((1+C[i]/(q-1) for i,q in enumerate(Q)),start=F(1))
H0,Hr,Hv=mean-16,mean,3*mean/2
for n in range(1,16):
 p1=pmf(7,n);p2=pmf(7,n//2) if n%2==0 else F(0)
 pv=sum((F(2,3**(d-2))*pmf(7,n//d) for d in range(3,n+1) if n%d==0),F(0))
 H0+=(16-n)*p1;Hr+=(16-n)*(p2-p1);Hv+=(16-n)*(pv-p2)
need(min(H0,Hr,Hv)>=0,'complete nonnegative new hinge')
Kq=prod((1+C[i]*a4(q) for i,q in enumerate(Q)),start=F(1))*(1+F(28,27)*a4(29))
def complete_tail(t):
 need((t['lower'],t['upper'],t['ell'],t['growth'])==(1600,3000,7,21),'complete804 tail shape')
 delta=F(t['delta']);grid=t['scale']
 need(delta==F(2,7) and grid==10**30,'complete tail distortion/grid')
 constant=F(27,256)/(delta**3*(1-delta))
 need(constant==F(64827,10240),'analytic tail constant')
 need(all(F(x)/(1-delta)<=comb(21,i) for i,x in enumerate((15,50,60,24),1)),'complete quartic growth comparison')
 series=sum((F(factorial(21),factorial(21-j)*21**j) for j in range(22)),F(0))
 total=constant/3*F(99,97)**21*F(3000,2999**4)*series
 ps=[p for p in range(1601,3001) if all(p%d for d in range(2,isqrt(p)+1))]
 need(ps==t['primes'] and len(ps)==179,'all179 bridge primes')
 for p in reversed(ps):
  raw=constant/(p-1)**4+(1+F(7,5)*a4(p))*total
  total=F(-((-raw.numerator*grid)//raw.denominator),grid)
  need(0<=total-raw<F(1,grid),'upward tail grid rounding')
 need(total==F(t['expected_upper'])==F(4301685063112470380207,10**30),'unchanged completeT1600')
 return total
T=complete_tail(base['tail'])
need(all(F(c['tail']['expected_upper'])==T for c in cs),'unchanged complete prime tail')
tables=[]
for w in weights:
 r=max(sum(w[:2]),sum(w[2:]));v=max(w);H=H0+Hr*r+Hv*v;K=Kq*(1+15*r+216*v)
 tables.append({'weights':list(map(str,w)),'r':str(r),'v':str(v),'H16':str(H),'H16_decimal':float(H),'K29':str(K),'full_tail_debit':str(27*K*T),'full_tail_debit_decimal':float(27*K*T)})

# Simultaneous integer tensor elimination for two tables, exactly3*64 newpoints.
dims=(3,2,2,2,2,2,2)
axes={D:[i for i in range(7) if D>>i&1] for D in range(128)}
states={D:list(product(*(range(dims[i]) for i in axes[D]))) for D in range(128)}
indices={D:{s:k for k,s in enumerate(states[D])} for D in range(128)}
transforms={}
for D in range(127):
 i=next(i for i in range(7) if not D>>i&1);parent=D|(1<<i);mapping=[]
 for s in states[D]:
  label=dict(zip(axes[D],s));arr=[]
  for colour in range(dims[i]):
   label[i]=colour;arr.append(indices[parent][tuple(label[j] for j in axes[parent])])
  mapping.append(arr)
 transforms[D]=(i,parent,mapping)
denoms=[19]+[q*(q-2) for q in Q[1:]]
denominator={D:scale*prod(denoms[i] for i in range(7) if not D>>i&1) for D in range(128)}
v5=((3,4,12),(4,3,12),(4,4,11));rows=[];positive=[0,0];facepos=[[0]*3 for _ in cs]
for vi,c5 in enumerate(v5):
 need(sum(c5)==19 and all(F(a,19)<=F(k,5)*C[0] for a,k in zip(c5,(1,1,3))),'new5vertex in absence-cap simplex')
 for mask in range(64):
  nums=[c5]+[((q-1,denoms[i]-(q-1)) if mask>>(i-1)&1 else (0,denoms[i])) for i,q in enumerate(Q[1:],1)]
  avg={127:U}
  for D in range(126,-1,-1):
   i,parent,mapping=transforms[D];A=avg[parent];p=nums[i]
   avg[D]=[[sum(p[col]*A[at][l] for col,at in enumerate(ids)) for l in range(10)] for ids in mapping]
  Fs=[[None]*128 for _ in range(2)]
  for D in range(128):
   A=avg[D];den=denominator[D]
   for ci in range(2):
    j=ci*5
    Fs[ci][D]=(F(max(sum(x[j:j+5]) for x in A),den),F(max(max(sum(x[j:j+2]),sum(x[j+2:j+5])) for x in A),den),F(max(max(x[j:j+5]) for x in A),den))
  rr={'key':[vi,mask],'tables':[]}
  for ci in range(2):
   mass=Fs[ci][0][0];shallow=[sum((R[h][D]*Fs[ci][D][h] for D in range(128)),F(0)) for h in range(3)]
   high=sum((beta[D]*Fs[ci][D][2]/2 for D in range(128)),F(0));alpha=mass-sum(shallow)-high
   gate=12*alpha-F(tables[ci]['H16'])-F(tables[ci]['full_tail_debit'])
   need(0<=mass<=1 and min(shallow)>=0 and high>=0,'exact source accounting')
   rr['tables'].append({'mass':str(mass),'shallow_losses':list(map(str,shallow)),'high_loss':str(high),'L':str(alpha),'gate':str(gate)})
   if gate>0:positive[ci]+=1;facepos[ci][vi]+=1
  rows.append(rr)
for ci in range(2):
 worst=min(rows,key=lambda r:F(r['tables'][ci]['gate']));data=worst['tables'][ci]
 L=F(data['L']);G=F(data['gate'])
 tables[ci].update(positive_vertices=positive[ci],positive_counts_by_face=facepos[ci],worst_key=worst['key'],minimum_L=str(L),minimum_L_decimal=float(L),minimum_gate=str(G),minimum_gate_decimal=float(G),worst_complete_accounting=data)
 if L>0:tables[ci].update(reserve_at_minimum=str(G/(27*L)),reserve_at_minimum_decimal=float(G/(27*L)))
need(tables[0]['positive_vertices']==192 and tables[1]['positive_vertices']==192,'both fixed tables pass all192 specified vertices')
need(F(tables[0]['minimum_L'])==F(certificate['expected_quarter_L_floor']) and tables[0]['worst_key']==certificate['expected_quarter_worst_key'],'exact uniform quarter minimum')
need(F(certificate['strict_quarter_gate_floor'])==F(63,100) and F(tables[0]['minimum_gate'])>F(63,100),'strict quarter gate floor63/100')
need(F(certificate['strict_quarter_reserve_floor'])==F(29,100) and F(tables[0]['reserve_at_minimum'])>F(29,100),'strict quarter normalized reserve29/100')
out={'schema':'e7-no-pure5-uniform-fixed-source-result-v1','checks':checks,'scope':certificate['scope'],
 'normalization':'lambda_w restricted to complete old survivorU / lambda_w(U); retained table supplies its mass lower bound; all hinge/moment coefficients are full-source.',
 'table_order':['quarter','point812'],'source_caps':list(map(str,C)),'H0':str(H0),'Hr':str(Hr),'Hv':str(Hv),'Kq':str(Kq),'T1600':str(T),
 'triangle_vertices':[[str(F(a,19)) for a in p] for p in v5],'tables':tables,'rows':rows,
 'source_cell_count':192,'evaluations':384,'evidence':'Exact common-source inventory, infinite hinge/moment and179-prime tail reconstruction; all192 product vertices for each of two fixed kernels. No solver or tuning.'}
if args.write_result:args.result.write_text(json.dumps(out,indent=2)+'\n')
elif json.loads(args.result.read_text())!=out:raise ValueError('saved result differs from exact recomputation')
print(json.dumps({'checks':checks,'quarter_minimum_L':tables[0]['minimum_L_decimal'],'quarter_minimum_gate':tables[0]['minimum_gate_decimal'],'quarter_reserve':tables[0]['reserve_at_minimum_decimal'],'positive_counts':[t['positive_vertices'] for t in tables]},indent=2))
