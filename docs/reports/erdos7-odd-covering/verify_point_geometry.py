#!/usr/bin/env python3
"""Recompute a75point all-height357 head bound from integer input.

Usage: python3 verify_point_geometry.py [point_geometry_certificate.json]
Requires Python3 and NumPy. All comparisons and certificate arithmetic are
integer or Fraction; no optimizer, external service, or scratch module is used.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import lcm
import json,sys
import numpy as np
C=(1,3,5,9,15,45)
SUBS=[np.array([t for t in range(s+1) if t&s==t],dtype=np.int64) for s in range(64)]
BITS=np.array([[(s>>e)&1 for e in range(6)] for s in range(64)],dtype=np.int64)
PAIRS=list(combinations(range(6),2))
PAIRBITS=np.array([[(s>>e&1)*(s>>f&1) for e,f in PAIRS] for s in range(64)],dtype=np.int64)

def require(condition,message):
 if not condition:raise ArithmeticError(message)

def geometry(points):
 pts=np.array(points,dtype=np.int64)
 residues=[sorted(set(int(x%d) for x in pts)) for d in C]
 cylinders=[np.array([[int(x%d==a) for x in pts] for a in rr],dtype=np.int64) for d,rr in zip(C,residues)]
 features=np.array([[cylinders[0][0],*row] for row in product(*cylinders[1:])],dtype=np.int64)
 return cylinders,features


def coeffs(cut):
 exps=list(product(range(3),range(2),range(2)));ds=[3**a*5**b*7**c for a,b,c in exps];gamma=[];eta=[F(0)]*12
 for a in exps:
  v=F(1)
  for p,h,e in zip((3,5,7),(2,1,1),a):
   if e==h:v*=F(p,p-1)
  gamma.append(v-1)
 for aa,d in zip(exps,ds):
  for bb,e in zip(exps,ds):
   v=F(1)
   for p,h,x,y in zip((3,5,7),(2,1,1),aa,bb):v*=F(p*(p+1),(p-1)**2) if x==h and y==h else F(p,p-1) if x==h or y==h else 1
   eta[ds.index(lcm(d,e))]+=v-1
 depths=list(product(*(range(k+1) for k in cut)));probs=[F(2,3**(a+1))*F(4,5**(b+1))*F(6,7**(c+1)) for a,b,c in depths];beta=sum(probs,F(0));eo=eta[:]
 for z,pr in zip(depths,probs):
  w=[(1+z[0] if a==2 else 1)*(1+z[1] if b==1 else 1)*(1+z[2] if c==1 else 1) for a,b,c in exps]
  for i,d in enumerate(ds):
   for j,e in enumerate(ds):eo[ds.index(lcm(d,e))]-=pr*(w[i]*w[j]-1)
 rem=[g-(F(1,2) if d in (9,45) else 0)-(F(1,4) if d in (5,15,45) else 0)-(F(1,6) if d%7==0 else 0) for d,g in zip(ds,gamma)]
 require(min(eo)>=0 and min(rem)>=0,'geometric coefficient nonnegativity')
 return ds,gamma,eta,rem,depths,probs,beta,eo

def exact_squares(weights,points,ri,loads,depths,low_roots=None,high_loads=None):
 nrows=int(ri.max())+1;R=np.array([sum(int(w) for w,j in zip(weights,ri) if int(j)==i) for i in range(nrows)],dtype=np.int64);v=np.array([max(int(w) for w,j in zip(weights,ri) if int(j)==i) for i in range(nrows)],dtype=np.int64);W=np.array([[sum(int(w) for w,x,j in zip(weights,points,ri) if int(j)==i and x%7==digit) for i in range(nrows)] for digit in range(1,7)],dtype=np.int64);total=int(weights.sum());records=[]
 for z3,z5,z7 in depths:
  L=loads[z3,z5];LB=L if high_loads is None else high_loads[z3,z5];u=z7+1;s=(z3+1)*(z5+1);nl=len(L);M=LB-1;maxload=max(int(L.max()),int(LB.max()))+s;bound=(1+u)**2*maxload**2*total;require(bound<2**63,'pure7 integer range')
  require(L.shape==LB.shape,'matching low/high base-layout dimensions and singleton weights')
  base=(L*L@R)[:,None]+2*u*(L*v)@M.T+(u*u*(M*M@v))[None,:]
  scores0=base[None,:,:]+(2*u*(W@L.T))[:,:,None]+(u*u*(W@(2*LB-1).T))[:,None,:]
  amax=np.zeros((6,nl,nl),dtype=np.int64);bmax=amax.copy();jmax=amax.copy()
  for i in range(nrows):
   a=L[:,i,None];b=LB[None,:,i];wj=W[:,i,None,None]
   ai=(R[i]*(2*s*a+s*s)+2*u*s*v[i]*(b-1))[None,:,:]+2*u*s*wj
   bi=(v[i]*(2*u*s*a+u*u*(2*s*(b-1)+s*s)))[None,:,:]+2*u*u*s*wj
   ji=ai+bi+2*u*v[i]*s*s
   np.maximum(amax,ai,out=amax);np.maximum(bmax,bi,out=bmax);np.maximum(jmax,ji,out=jmax)
  scores=scores0+np.maximum(amax+bmax,jmax);digit,ai,bi=map(int,np.unravel_index(scores.argmax(),scores.shape));best=int(scores[digit,ai,bi]);A=L[ai].copy();B=LB[bi].copy();av=R*(2*s*A+s*s)+2*u*s*(v*(B-1)+W[digit]);bv=v*(2*u*s*A+u*u*(2*s*(B-1)+s*s))+2*u*u*s*W[digit];jv=av+bv+2*u*v*s*s
  if int(jv.max())>int(av.max())+int(bv.max()):ia=ib=int(jv.argmax())
  else:ia,ib=int(av.argmax()),int(bv.argmax())
  A[ia]+=s;B[ib]+=s;cw=(A*A)[ri]+(points%7==digit+1)*(2*u*A+u*u*(2*B-1))[ri];cv=2*u*A*(B-1)+u*u*(B-1)*(B-1)
  require(sum(int(c)*int(w) for c,w in zip(cw,weights))+sum(int(c)*int(w) for c,w in zip(cv,v))==best,'pure7 maximizing witness')
  record={'depth':[z3,z5,z7],'numerator':best,'pure7_digit':digit+1,'base_pair':[ai,bi],'singleton_rows':[ia,ib],'A_loads':A.tolist(),'B_loads':B.tolist(),'int64_bound':bound}
  if low_roots is not None:
   require(len(low_roots)==nl,'one original mod3 root per low base layout')
   # Only A carries the original mod3 label. B's cofactor3 is mod21.
   record['root_numerators']={str(int(r)):int(scores[:,low_roots==r,:].max()) for r in np.unique(low_roots)}
  records.append(record)
 return records,R,v,W

class FixedADP:
 def __init__(self,pts,xs,ri):
  self.pts=pts;self.xs=xs;self.ri=ri;self.digit=pts%7
  self.cyl,self.features=geometry(xs)
 def query(self,w,z,return_details=False,root_values=False,original_nine=None):
  require(np.issubdtype(w.dtype,np.integer),'integer DP input');dtype=np.int64
  W=np.zeros((6,len(self.xs)),dtype=dtype)
  for k in range(1,7):
   ix=self.digit==k
   np.add.at(W[k-1],self.ri[ix],w[ix])
  z3,z5,z7=z;b=np.array([1,1,1+z5,1+z3,1+z5,(1+z3)*(1+z5)],dtype=np.int64);u=1+z7
  L=np.einsum('aer,e->ar',self.features,b,dtype=np.int64)
  if original_nine is not None:
   require(type(original_nine) is int and original_nine in set(map(int,self.xs%9)), 'original mod9 test root')
   # Remove the original9 contribution from its saturated aggregate and
   # restore its prescribed cylinder. Its higher descendants remain free.
   L=L-self.features[:,3,:]+(self.xs%9==original_nine).astype(np.int64)
  Q=(L*L)@W.sum(axis=0)
  M=np.array([(W@cy.T).max(axis=1) for cy in self.cyl]).T
  R=np.empty((6,6,len(L)),dtype=dtype)
  for e,cy in enumerate(self.cyl):
   for y in range(6):
    R[y,e]=((W[y]*(u*u*b[e]*b[e]+2*u*b[e]*L))@cy.T).max(axis=1)
  J=np.array([2*u*u*b[e]*b[f]*M[:,C.index(lcm(C[e],C[f]))] for e,f in PAIRS],dtype=dtype).T
  H=np.einsum('se,yea->ysa',BITS,R)+np.einsum('sp,yp->ys',PAIRBITS,J)[:,:,None]
  # All labels can be assigned to digit1 initially. Subsequent digits permit empty blocks.
  D=H[0].copy()
  trace=[]
  for y in range(1,6):
   N=np.empty_like(D);arg=np.empty(D.shape,dtype=np.uint8) if return_details else None
   for s in range(64):
    tt=SUBS[s];cand=D[s^tt]+H[y,tt]
    if return_details:
     at=cand.argmax(axis=0);N[s]=cand[at,np.arange(len(L))];arg[s]=tt[at]
    else:N[s]=cand.max(axis=0)
   D=N
   if return_details:trace.append(arg)
  total=Q+D[63];ai=int(total.argmax());value=total[ai].item()
  if root_values:
   # The unchanged original mod3 test is the second feature of A.
   return {str(int(r)):int(total[self.features[:,1,int(np.flatnonzero(self.xs%3==r)[0])]==1].max()) for r in np.unique(self.xs%3)}
  if not return_details:return value
  chosen=[];s=63
  for y in range(5,0,-1):
   t=int(trace[y-1][s,ai]);chosen.append([y+1,t]);s^=t
  chosen.append([1,s]);chosen.reverse()
  return value,{'low_index':ai,'low_load':L[ai].tolist(),'digit_partition':chosen,'Q':Q[ai].item(),'high':D[63,ai].item()}

def group_setup(family,e3,extra=35):
 full=np.array(family['survivors'],dtype=np.int64);pts=np.array(family['points'],dtype=np.int64);index=np.array([family['points'].index(int(x%45)) for x in full],dtype=np.int64)
 def cylinders(d):
  residues=sorted(set(int(x%d) for x in full));ms=np.array([[int(x%d==a) for x in full] for a in residues],dtype=np.int64);return residues,ms
 ares=[];am=[]
 for d in e3:rr,mm=cylinders(d);ares.append(rr);am.append(mm)
 alayouts=list(product(*ares));A=np.array([a+b for a,b in product(*am)],dtype=np.int64)
 bold=(5,15,45);bres=[];bm=[]
 for d in bold:rr,mm=cylinders(d);bres.append(rr);bm.append(mm)
 blayouts=list(product(*bres));B=np.array([a+b+c for a,b,c in product(*bm)],dtype=np.int64)
 extres,E=cylinders(extra);digits=full%7;mods=(1,3,5,9,15,45);cyl=[];cylres=[];other_indices=[];same_indices=[]
 for co in mods:
  rr,mm=cylinders(7*co);cyl.append(mm);cylres.append(rr)
  same_indices.append([np.array([i for i,a in enumerate(rr) if a%7==k],dtype=np.int64) for k in range(7)])
  other_indices.append([np.array([i for i,a in enumerate(rr) if a%7!=k],dtype=np.int64) for k in range(7)])
 return {'family':family,'full':full,'pts':pts,'index':index,'e3':list(e3),'extra':extra,'A':A,'B':B,'alayouts':alayouts,'blayouts':blayouts,'extres':extres,'E':E,'cyl':cyl,'cylres':cylres,'same':same_indices,'other':other_indices}

def group_oracle(q,D,top=0,chunk=16):
 q=np.asarray(q);require(q.ndim==1 and len(q) in (len(D['pts']),len(D['full'])) and np.all(q>=0),'group input dimensions and nonnegativity');full_weights=(len(q)==len(D['full']));wf=q if full_weights else q[D['index']];nb=len(D['B']);B=D['B'];E=D['E'];res=[];best=None;topcuts=[]
 for left in range(0,len(D['A']),chunk):
  right=min(left+chunk,len(D['A']));na=right-left
  AA=np.repeat(D['A'][left:right],nb,axis=0);BB=np.tile(B,(na,1));T=2-AA;K=T*(4-BB);base=24*AA+6*T*BB
  require(min(T.flat)>=0 and min(K.flat)>=0,'group complement nonnegativity')
  Tw=T*wf;Kw=K*wf;vbase=base@wf;groups=len(AA);mats=[Kw@cm.T for cm in D['cyl']]
  other=[np.stack([mat[:,jj].max(axis=1) if len(jj) else np.zeros(groups,dtype=np.int64) for jj in oo],axis=1) for mat,oo in zip(mats,D['other'])]
  for ei,em in enumerate(E):
   digit=D['extres'][ei]%7;vals=vbase+6*(Tw@em);args=[]
   for j,(mat,cm) in enumerate(zip(mats,D['cyl'])):
    si=D['same'][j][digit];altered=mat[:,si]-Tw@(cm[si]*em).T if len(si) else np.empty((groups,0),dtype=np.int64);am=altered.max(axis=1) if len(si) else np.zeros(groups,dtype=np.int64);om=other[j][:,digit];vals=vals+np.maximum(am,om)
    if top:args.append((altered,am,om,si))
   gi=int(vals.argmax());value=int(vals[gi])
   if best is None or value>best['value']:
    best={'value':value,'A_index':left+gi//nb,'B_index':gi%nb,'extra_index':ei,'A_residues':list(D['alayouts'][left+gi//nb]),'B_residues':list(D['blayouts'][gi%nb]),'extra_residue':D['extres'][ei]}
   if top:
    for gi in np.argsort(vals)[-2:]:
     gi=int(gi);row=base[gi].copy()+6*T[gi]*em;chosen=[]
     for j,(altered,am,om,si) in enumerate(args):
      if len(si) and am[gi]>=om[gi]:ci=int(si[int(altered[gi].argmax())])
      else:
       oi=D['other'][j][digit];ci=int(oi[int(mats[j][gi,oi].argmax())])
      row+=(K[gi]-T[gi]*em)*D['cyl'][j][ci];chosen.append(D['cylres'][j][ci])
     cv=row.astype(np.int64) if full_weights else np.bincount(D['index'],weights=row,minlength=len(D['pts'])).astype(np.int64)
     require(int(cv@q)==int(vals[gi]),'group maximizing witness')
     topcuts.append((int(vals[gi]),cv,{'A_residues':list(D['alayouts'][left+gi//nb]),'B_residues':list(D['blayouts'][gi%nb]),'extra_residue':D['extres'][ei],'E7_residues':chosen}))
  if top and len(topcuts)>4*top:topcuts=sorted(topcuts,key=lambda a:a[0],reverse=True)[:top]
 topcuts=sorted(topcuts,key=lambda a:a[0],reverse=True)[:top]
 return best,topcuts,{'A_layouts':len(D['A']),'B_layouts':nb,'extra_layouts':len(E),'outer_layouts':len(D['A'])*nb*len(E),'exact_integer':True}


def main():
 path=Path(sys.argv[1]) if len(sys.argv)>1 else (Path(__file__).resolve().parent / 'certificates/point_geometry_certificate.json')
 data=json.loads(read_artifact_text(path))
 require(type(data) is dict,'certificate object')
 require(data['target']=='3849/106','pinned target3849/106')
 for name in ['points','old_points','weight_numerators','depth_box','divisors','cap_numerators','pure7_square_numerators','fixedA_square_numerators']:
  raw=data[name];require(type(raw) is list and all(type(v) is int for v in raw),'integer list: '+name)
 for name in ['weight_denominator','group_numerator48']:
  require(type(data[name]) is int,'integer scalar: '+name)
 require(type(data['family']) is list and all(type(row) is list and len(row)==2 and all(type(v) is int for v in row) for row in data['family']),'integer family pairs')
 require(type(data['depths']) is list and all(type(row) is list and len(row)==3 and all(type(v) is int for v in row) for row in data['depths']),'integer depth triples')
 require(all(0<=x<315 for x in data['points']) and all(0<=x<45 for x in data['old_points']),'point coordinate range')
 require(data['weight_numerators'] and all(0<=w<2**63 for w in data['weight_numerators']),'raw integer weight range')
 family=data['family'];points=np.array(data['points'],dtype=np.int64);weights=np.array(data['weight_numerators'],dtype=np.int64);den=sum(map(int,weights));xs=np.array(data['old_points'],dtype=np.int64)
 require(data['schema']=='erdos7-point-geometry-v1','schema')
 require(len(family)==len(set(d for d,a in family))==11,'unique low labels')
 require({d for d,a in family}=={d for d in range(2,316) if 315%d==0},'complete low divisor labels')
 require(all(0<=a<d for d,a in family),'canonical residues')
 require(points.tolist()==[x for x in range(315) if all(x%d!=a for d,a in family)],'actual survivor carrier')
 require(len(points)==75 and len(xs)==16,'carrier sizes')
 require(xs.tolist()==sorted(set(int(x%45) for x in points)),'actual old projection')
 require(len(weights)==len(points) and weights.min()>=0 and den==data['weight_denominator']>0,'probability weights')
 ri=np.array([xs.tolist().index(int(x%45)) for x in points],dtype=np.int64)
 require(set(int(x%7) for x in points)<=set(range(1,7)),'digit0 excluded')
 cut=tuple(data['depth_box']);require(len(cut)==3 and all(0<=k<=100 for k in cut),'depth box')
 # A common bound controls every nonnegative intermediate in both square oracles.
 bmax=[1,1,1+cut[1],1+cut[0],1+cut[1],(1+cut[0])*(1+cut[1])]
 safety=(2+cut[2])**2*sum(bmax)**2*den
 require(safety<2**63 and 48*den<2**53,'integer arithmetic range')
 ds,ga,eta,rem,depths,probs,beta,eo=coeffs(cut);rem[ds.index(35)]-=F(1,4)
 require(ds==data['divisors'] and list(map(list,depths))==data['depths'],'coefficient indexing')
 require(min(rem)>=0 and min(eo)>=0 and 0<beta<1,'nonnegative transfer coefficients')
 require(data['groups']=={'3':[9,45],'5':[5,15,45,35],'7':[7,21,35,63,105,315]},'group specification')
 mods=(3,5,9,15);choices=list(product(*(sorted(set(int(x%d) for x in xs)) for d in mods)))
 features=np.array([[[int(x%d==a) for x in xs] for d,a in zip(mods,row)] for row in choices],dtype=np.int64)
 require(len(choices)==280,'base layout count')
 loads={(z3,z5):1+np.einsum('ajn,j->an',features,np.array([1,1+z5,1+z3,1+z5],dtype=np.int64),dtype=np.int64) for z3,z5 in product(range(cut[0]+1),range(cut[1]+1))}
 precords,R,v,W=exact_squares(weights,points,ri,loads,depths);pn=[r['numerator'] for r in precords]
 dp=FixedADP(points,xs,ri);dn=[dp.query(weights,z) for z in depths]
 require(pn==data['pure7_square_numerators'],'pure7 maxima')
 require(dn==data['fixedA_square_numerators'],'fixedA DP maxima')
 nums=list(map(min,zip(pn,dn)))
 caps=[]
 for d in ds:
  caps.append(max(sum(int(w) for x,w in zip(points,weights) if int(x%d)==a) for a in range(d)))
 require(caps==data['cap_numerators'],'actual cylinder caps')
 fam={'survivors':points.tolist(),'points':xs.tolist()};GD=group_setup(fam,(9,45),35);best,cuts,stats=group_oracle(weights,GD,top=1);groupnum=best['value']
 require(groupnum==data['group_numerator48'],'group union maximum')
 require(cuts and cuts[0][0]==groupnum and int(cuts[0][1]@weights)==groupnum,'group witness')
 _,cv,desc=cuts[0];independent=[]
 for x in points:
  A=sum(int(x%d==a) for d,a in zip((9,45),desc['A_residues']))
  B=sum(int(x%d==a) for d,a in zip((5,15,45),desc['B_residues']))+int(x%35==desc['extra_residue'])
  H=sum(int(x%d==a) for d,a in zip((7,21,35,63,105,315),desc['E7_residues']))
  independent.append(24*A+12*B-6*A*B+(2-A)*(4-B)*H)
 require(independent==cv.tolist(),'pointwise grouped union identity')
 capvals=[F(n,den) for n in caps];union=F(groupnum,48*den)
 q=1-union-sum((a*m for a,m in zip(rem,capvals)),F(0))
 require(q>0,'positive survival')
 vals=[F(n,den) for n in nums]
 U=(1-beta)*vals[0]+sum((p*f for p,f in zip(probs,vals)),F(0))+sum((e*m for e,m in zip(eo,capvals)),F(0))
 require(U>=1,'unit-adjusted moment')
 Gamma=1+(U-1)/q;target=F(3849,106)
 for key,value in [('survival_lower',q),('U_B',U),('Gamma',Gamma)]:require(str(value)==data[key],key)
 require(Gamma<target,'strict target inequality')
 result={'verified':True,'points':len(points),'depths':len(depths),'weight_denominator':den,'survival_lower':str(q),'U_B':str(U),'Gamma':str(Gamma),'target':str(target),'strict_saving':str(target-Gamma),'maximum_integer_bound':safety}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
