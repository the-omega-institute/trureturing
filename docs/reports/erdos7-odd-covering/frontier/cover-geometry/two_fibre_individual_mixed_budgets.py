#!/usr/bin/env python3
"""Report481: exact two-fibre capacities and original numerical-label controls.

The general boundary reduction and actual-pair premise are ordinary mathematical
inputs. These checks do not certify Lean or existence of actual old survivors.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import argparse,json

def need(ok, message):
 if not ok:raise ValueError(message)

def envelope(qx,qy,N):
 need(min(qx,qy,N)>=0,'nonnegative paired budgets')
 Gamma=min(N,qx+qy)
 ax,ay=min(qx,22),min(qy,22);bx,by=min(qx,28),min(qy,28)
 A=min(N,ax+ay);B=min(N,bx+by)
 tr=(max(0,A-ay),min(ax,A));ur=(max(0,B-by),min(bx,B))
 def fs(t,u):
  rx=(22-t)*(28-u);ry=(22-A+t)*(28-B+u)
  return (F(0),F(rx-qx),F(ry-qy),F(rx+ry-Gamma))
 positions=set()
 for direction,k,low,high in [('t',tr[0],*ur),('t',tr[1],*ur),('u',ur[0],*tr),('u',ur[1],*tr)]:
  def point(z):return (F(k),F(z)) if direction=='t' else (F(z),F(k))
  lo,hi=F(low),F(high)
  positions.add(point(lo));positions.add(point(hi))
  flo=fs(*point(lo));fhi=fs(*point(hi))
  if lo==hi:continue
  for i in range(4):
   for j in range(i+1,4):
    dlo=flo[i]-flo[j];dhi=fhi[i]-fhi[j]
    if dlo==dhi:continue
    z=lo-dlo*(hi-lo)/(dhi-dlo)
    if lo<=z<=hi:positions.add(point(z))
 need(len(positions)<=28,'edge candidate upper bound')
 best=min((max(fs(t,u)),t,u) for t,u in positions)
 return best,(A,B,tr,ur),positions,fs

def old_bound(qx,qy,N):
 ax,ay=min(qx,22),min(qy,22);bx,by=min(qx,28),min(qy,28)
 A=min(N,ax+ay);B=min(N,bx+by)
 tr=(max(0,A-ay),min(ax,A));ur=(max(0,B-by),min(bx,B))
 return max(0,min((22-t)*(28-u)+(22-A+t)*(28-B+u)-N for t in tr for u in ur))

def mixed_formula(rx,ry,qx,qy,N):
 # Independent route: remove up to min(N,min(rx,qx)+min(ry,qy)).
 Gamma=min(N,qx+qy)
 flow=rx+ry-min(Gamma,min(rx,qx)+min(ry,qy))
 target=max(0,rx-qx,ry-qy,rx+ry-Gamma)
 need(flow==target,'mixed removal flow vs four-term formula')
 return target

def boundary_descent(t,u,A,B,tr,ur):
 # A separate exact implementation of the proof's dominated boundary point.
 a,b=F(22)-t,F(28)-u
 if t in tr or u in ur:return t,u
 P,R=F(44-A),F(56-B)
 need(a>0 and b>0,'interior residual positivity')
 amin,amax=F(22-tr[1]),F(22-tr[0]);bmin,bmax=F(28-ur[1]),F(28-ur[0])
 coeff=P*b-R*a
 if coeff<=0:
  eps=min((amax-a)/a,(b-bmin)/b)
 else:
  eps=-min((a-amin)/a,(bmax-b)/b)
 anew,bnew=a*(1+eps),b*(1-eps)
 tnew,unew=22-anew,28-bnew
 need(tr[0]<=tnew<=tr[1] and ur[0]<=unew<=ur[1],'boundary descent feasible')
 need(tnew in tr or unew in ur,'boundary descent reaches edge')
 need(anew*bnew<=a*b and (P-anew)*(R-bnew)<=(P-a)*(R-b),'both products weakly decrease')
 return tnew,unew

def crt(values,mods):
 M=prod(mods);return sum(v*(M//m)*pow(M//m,-1,m) for v,m in zip(values,mods))%M

def literal_control(vx,vy,profile,other_profile=None):
 if other_profile is None:other_profile=profile
 ps=(3,5,7,11,13,17,19);es=(max(vx,vy)+1,)+tuple(max(e,f)+1 for e,f in zip(profile,other_profile));mods=tuple(p**e for p,e in zip(ps,es));M=prod(mods)
 a=0;b=crt((1,0,0,0,0,0,0),mods)
 x=crt((3**vx,)+tuple(p**e for p,e in zip(ps[1:],profile)),mods)
 y=crt((1+3**vy,)+tuple(2*p**e for p,e in zip(ps[1:],other_profile)),mods)
 qx=qy=N=count=0
 for exps in product(*(range(e+1) for e in es)):
  d=prod(p**e for p,e in zip(ps,exps))
  ax=(x-a)%d==0;bx=(x-b)%d==0;ay=(y-a)%d==0;by=(y-b)%d==0
  qx+=ax or bx;qy+=ay or by;N+=max(int(ax)+int(ay),int(bx)+int(by));count+=1
 C=prod(e+1 for e in profile);D=prod(e+1 for e in other_profile)
 intersection=prod(min(e,f)+1 for e,f in zip(profile,other_profile))
 need((qx,qy,N)==((vx+1)*C,(vy+1)*D,(vx+1)*C+(vy+1)*D-min(vx,vy)*intersection),'literal joint original-label inventory')
 need(N>=max(qx,qy)+1,'unit-label strict joint surplus')
 bound,t,u=envelope(qx,qy,N)[0]
 return {'vx':vx,'vy':vy,'nonternary_profile':profile,'other_nonternary_profile':other_profile,'C':C,'other_C':D,'intersection':intersection,'CRT_period':M,'reference_a':a,'reference_b':b,'old_x':x,'old_y':y,'labels_checked':count,'Qx':qx,'Qy':qy,'N':N,'minimum_scaled_survivor':str(bound),'minimizer':[str(t),str(u)],'pair_survival_lower':str(bound/616),'former_pair_survival_lower':str(F(old_bound(qx,qy,N),616))}

def verify():
 # Natural integer inventory triples. An interior rational grid independently
 # checks the boundary descent and its domination, not just the implementation
 # of edge candidate generation. Exact proof establishes the continuum result.
 triple_count=interior_checks=0
 for qx in range(41):
  for qy in range(41):
   for N in range(max(qx,qy),qx+qy+1):
    (minimum,mt,mu),(A,B,tr,ur),positions,fs=envelope(qx,qy,N)
    need(minimum>=old_bound(qx,qy,N),'retaining mixed caps cannot weaken bound')
    need(max(fs(mt,mu))==minimum,'reported minimizer')
    for nt,nu in product(range(5),repeat=2):
     t=F(tr[0])+F(nt,4)*(tr[1]-tr[0]);u=F(ur[0])+F(nu,4)*(ur[1]-ur[0])
     rx=(22-t)*(28-u);ry=(22-A+t)*(28-B+u)
     need(max(fs(t,u))==mixed_formula(rx,ry,qx,qy,N),'mixed formula at feasible axes')
     tb,ub=boundary_descent(t,u,A,B,tr,ur)
     need(minimum<=max(fs(tb,ub))<=max(fs(t,u)),'boundary optimizer dominates interior')
     interior_checks+=1
    triple_count+=1

 cutoffs=[]
 for qx,qy,N,want in [(20,37,38,F(7)),(20,38,39,F(4,3)),(20,39,40,F(0))]:
  (value,t,u),_,_,_=envelope(qx,qy,N)
  need(value==want,'critical cutoff value')
  cutoffs.append({'Qx':qx,'Qy':qy,'N':N,'minimum_scaled_survivor':str(value),'minimizer':[str(t),str(u)]})
 # General monotonicity proof plus the zero at(20,39,40) makes this complete:
 # minQ>=20 and maxQ>=39 imply zero. Thus1<=C<=19,20<=Qx<=Qy<=38.
 edges=[]
 for C in range(1,20):
  for va in range(1,38//C):
   for vb in range(va,38//C):
    qx=(va+1)*C;qy=(vb+1)*C;N=qy+C
    if qx<20:continue
    value,t,u=envelope(qx,qy,N)[0]
    if value>0:edges.append({'C':C,'va':va,'vb':vb,'Qx':qx,'Qy':qy,'N':N,'minimum_scaled_survivor':str(value),'minimizer':[str(t),str(u)],'pair_survival_lower':str(value/616),'former_pair_survival_lower':str(F(old_bound(qx,qy,N),616))})
 need(len(edges)==81 and sum(r['va']==r['vb'] for r in edges)==23,'complete positive-edge counts')
 need(min(F(r['minimum_scaled_survivor']) for r in edges)==F(4,5),'global smallest additional positive bound')
 new_edges=[r for r in edges if F(r['former_pair_survival_lower'])==0]
 need(len(new_edges)==10,'ten additional positive types')
 maxima=[{'C':C,'depth_pairs':{str(v):max(r['vb'] for r in edges if r['C']==C and r['va']==v) for v in sorted({r['va'] for r in edges if r['C']==C})}} for C in sorted({r['C'] for r in edges})]
 controls=[literal_control(3,3,(1,2,0,0,0,0)),literal_control(1,1,(10,0,0,0,0,0)),literal_control(3,5,(4,0,0,0,0,0)),literal_control(1,1,(2,3,0,0,0,0)),literal_control(19,37,(0,0,0,0,0,0)),literal_control(20,31,(0,0,0,0,0,0)),literal_control(9,9,(1,0,0,0,0,0),(0,1,0,0,0,0))]
 need(all(F(row['pair_survival_lower'])>0 for row in controls),'literal controls positive')
 out={'scope':'exact full individual-and-shared axis/mixed capacity relaxation; finite all-height profile classification follows the proved monotonic cutoff; actual old-survivor point existence is a separate hypothesis','natural_budget_triples_checked':triple_count,'rational_grid_descent_and_mixed_checks':interior_checks,'cutoff_controls':cutoffs,'complete_additional_positive_edges':edges,'new_edges_over_axis_individual_caps':new_edges,'complete_edge_depth_maxima':maxima,'smallest_additional_pair_survival':'1/770','literal_CRT_controls':controls,'Lean_rerun':False,'actual_old_survivor_pair_existence_proved':False}
 return out


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path,help='write regenerated exact data')
 args=parser.parse_args()
 out=verify()
 rendered=json.dumps(out,indent=2)+'\n'
 if args.output:
  args.output.write_text(rendered)
 else:
  expected=Path(__file__).with_suffix('.json')
  need(expected.read_text()==rendered,'retained result data match exact replay')
 print('budget triples',out['natural_budget_triples_checked'],
       'rational descent and mixed checks',out['rational_grid_descent_and_mixed_checks'],
       'positive types',len(out['complete_additional_positive_edges']),
       'minimum pair survival',out['smallest_additional_pair_survival'])
 print('literal label controls',[row['labels_checked'] for row in out['literal_CRT_controls']])

if __name__=='__main__':main()
