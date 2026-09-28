"""Joint-liability prime absorption: finite even controls only.
No Lean result or distinct odd whole cover is claimed.
All control data are literal; all enumeration is over stated finite periods.
"""
from math import lcm,gcd
from collections import Counter
import json,argparse,hashlib

def req(x,msg):
 if not x:raise ValueError(msg)
def vp(n,p):
 e=0
 while n%p==0:e+=1;n//=p
 return e
def crt(a,m,b,n):
 req(gcd(m,n)==1,'noncoprime CRT')
 return (a+m*((b-a)*pow(m,-1,n)%n))%(m*n)
def event(C,x):return tuple((x-a)%m==0 for a,m in C)
def tree_layers(B,q,r,G):
 layers=[None]*(G+1);layers[G]={x:x not in B for x in range(q**G)}
 for e in range(G-1,-1,-1):
  layers[e]={x:sum(layers[e+1][x+j*q**e] for j in range(q))>=r for x in range(q**e)}
 return layers
def analysis(C,r=2,q=5):
 Q=lcm(*(m for a,m in C));H=vp(Q,r);G=vp(Q,q);R=r**H;T=q**G;M=Q//R//T
 req(len({m for a,m in C})==len(C),'labels not distinct')
 hits=[tuple(i for i,t in enumerate(event(C,x)) if t) for x in range(Q)]
 req(all(hits),'source not whole cover')
 private=[sum(h==(i,) for h in hits) for i in range(len(C))]
 keep=[i for i,(a,m) in enumerate(C) if m%q or vp(m,r)==H];low=[i for i in range(len(C)) if i not in keep]
 rows=[]
 for u in range(R):
  live=[v for v in range(M) if not any((u-a)%r**vp(m,r)==0 and (v-a)%(m//r**vp(m,r))==0 for a,m in C if m%q)]
  F=set();E=set();P=set();witness={};joint_only=[];essential=set()
  for i in low:
   a,m=C[i];e=vp(m,q);h=vp(m,r);s=m//r**h//q**e
   if (u-a)%r**h==0 and any((v-a)%s==0 for v in live):F.update(x for x in range(T) if (x-a)%q**e==0)
  for x in range(T):
   for v in range(M):
    y=crt(crt(u,R,x,T),R*T,v,M)
    if not any(i in keep for i in hits[y]):
     E.add(x);witness.setdefault(x,[]).append([v,y,list(hits[y])]);essential.update(hits[y])
     if len(hits[y])==1:P.add(x)
     else:joint_only.append(y)
  req(E<=F,'joint projection not in live-active projection')
  req(essential<=set(low),'retained owner in joint liability')
  rows.append(dict(u=u,live_M=live,active_projection=sorted(F),joint_projection=sorted(E),private_projection=sorted(P),joint_only_points=joint_only,essential_low_indices=sorted(essential),witnesses=witness,active_pass=tree_layers(F,q,r,G)[0][0],joint_pass=tree_layers(E,q,r,G)[0][0]))
 return dict(original=C,Q=Q,H=H,G=G,M=M,r=r,q=q,private_counts=private,rows=rows,keep=keep,low=low,active_pass=all(x['active_pass'] for x in rows),joint_pass=all(x['joint_pass'] for x in rows))
def transport(A,forbidden_field='joint_projection'):
 C=A['original'];Q=A['Q'];H=A['H'];G=A['G'];M=A['M'];r=A['r'];q=A['q'];R=r**H;T=q**G;N=r**(H+G)*M
 theta=[]
 for row in A['rows']:
  layers=tree_layers(set(row[forbidden_field]),q,r,G);req(layers[0][0],'no avoiding tree')
  maps=[{0:0}]
  for e in range(G):
   nxt={}
   for new,old in maps[-1].items():
    children=[old+j*q**e for j in range(q) if layers[e+1][old+j*q**e]][:r]
    req(len(children)==r,'insufficient children')
    for b,child in enumerate(children):nxt[new+b*r**e]=child
   maps.append(nxt)
  theta.append(maps)
 output=[];mapping={}
 for i,(a,m) in enumerate(C):
  e=vp(m,q);h=vp(m,r);s=m//r**h//q**e
  if not e:b,n=a,m
  elif h<H:continue
  else:
   inverse={old:new for new,old in theta[a%R][e].items()}
   if a%q**e not in inverse:continue
   n=r**(H+e)*s;b=crt(a%R+R*inverse[a%q**e],r**(H+e),a%s,s)
  mapping[i]=len(output);output.append((b%n,n))
 req(len(set(m for a,m in output))==len(output),'output collision')
 req((len(output),sum(m for a,m in output))<(len(C),sum(m for a,m in C)),'no lex descent')
 holes=[];live_low_hits=0;event_checks=0;images=set();uncovered_source=[]
 digest=hashlib.sha256()
 for z in range(N):
  u=z%R;b=(z//R)%r**G;xi=theta[u][G][b];v=z%M;y=crt(crt(u,R,xi,T),R*T,v,M)
  old=event(C,y);new=event(output,z);images.add(y)
  req(all(old[i]==(new[mapping[i]] if i in mapping else False) for i in A['keep']),'retained event mismatch')
  event_checks+=len(A['keep']);digest.update(bytes(old));digest.update(bytes(new))
  if v in A['rows'][u]['live_M']:live_low_hits+=sum(old[i] for i in A['low'])
  if not any(new):holes.append(z);uncovered_source.append(y)
  req((not any(new))==(not any(old[i] for i in A['keep'])),'joint exactness failed')
 req(len(images)==N,'source map not injective')
 predicted=any(x in A['rows'][u]['joint_projection'] for u,maps in enumerate(theta) for x in maps[G].values())
 req(predicted==bool(holes),'exact criterion mismatch')
 return dict(output=output,output_count=len(output),input_count=len(C),output_period=lcm(*(m for a,m in output)),transport_period=N,input_sum=sum(m for a,m in C),output_sum=sum(m for a,m in output),retained_event_checks=event_checks,holes=holes,uncovered_source=uncovered_source,live_discarded_hits=live_low_hits,theta=[[[maps[e][i] for i in range(r**e)] for e in range(G+1)] for maps in theta],event_digest=digest.hexdigest())
BASE=[(0,2),(1,4),(3,8),(23,40),(7,24),(119,200),(119,120),(399,600),(0,5),(1,10),(7,20),(4,25),(9,50),(39,100)]
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',required=True);args=p.parse_args()
 base=analysis(BASE);req(all(base['private_counts']),'base is redundant');base_t=transport(base);req(not base_t['holes'],'base transport hole')
 strict=analysis(BASE+[(3,15)]);req(not strict['active_pass'] and strict['joint_pass'],'strict condition failure');strict_t=transport(strict);req(not strict_t['holes'],'strict transport hole');req(strict_t['output']==base_t['output'],'redundant extension changes exact transport');req(strict_t['live_discarded_hits']>0,'does not separate live-active and liability')
 req([row['joint_projection'] for row in base['rows']]==[row['joint_projection'] for row in strict['rows']],'retained family residual changed')
 joint=analysis(BASE+[(0,15),(5,30)]);good=transport(joint);bad=transport(joint,'private_projection')
 req(not good['holes'] and bad['holes'],'private-union mutation not detected')
 req(any(set(row['joint_projection'])-set(row['private_projection']) for row in joint['rows']),'no genuine joint-only leaves')
 report=dict(base=dict(analysis=base,transport=base_t),strict=dict(analysis=strict,transport=strict_t),private_union_failure=dict(analysis=joint,valid_transport=good,invalid_transport=bad),scope='Finite EVEN whole-cover controls. Base14 is irredundant. Strict15 and negative16 deliberately contain redundant classes. No assertion of an irredundant strict separation, odd covering counterexample, unrestricted noncoverage, Lean verification, or literature priority.')
 with open(args.output,'w') as f:json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
 print(json.dumps({'strict_input':len(strict['original']),'strict_output':strict_t['output_count'],'strict_live_discarded_hits':strict_t['live_discarded_hits'],'private_union_false_output_holes':len(bad['holes']),'retained_event_checks':sum(t['retained_event_checks'] for t in [base_t,strict_t,good,bad])}))
if __name__=='__main__':main()
