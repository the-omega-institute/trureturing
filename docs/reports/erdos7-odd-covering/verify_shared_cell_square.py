#!/usr/bin/env python3
"""Exact actual shared-cell square hinges, complete tails, same AP13 law.

The accompanying ordinary proof supplies the full-height comparison and
separately convex vertex reduction. No Lean endpoint is asserted.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod,isqrt
import json
import argparse
import hashlib
from pathlib import Path

ROOT=(0,0,1,1,1)
CHOICES=tuple(product(range(2),range(5)))
BS=tuple(tuple(1+(ROOT[l]==r)+(l==j) for l in range(5)) for r,j in CHOICES)
G=F(3849,106)
RHO=F(18925009844347,38266567762500)
BASE=Path(__file__).resolve().parent
PINS={'certificates/pure_root_profile_certificate.json':'b1ba6c871d993fd43152351c2b823a7955d93ce4500fbe29f9420c38f7f72196',
      'certificates/shared_cell_hinges_certificate.json':'585fd5cc59e7c121e64141aec6717ead06b3d5dfd00e2a40a2278e796f7f8845'}

def need(ok,message):
 if not ok:raise ValueError(message)

def ceilroot(t):
 k=isqrt(t.numerator//t.denominator)
 return k+(k*k<t)

def tails(p,N):
 # Sum p^-n, n p^-n, n^2 p^-n over every n>=N.
 r=F(1,p);m0=r**N/(1-r)
 return m0,m0*(N+r/(1-r)),m0*(N*N+2*N*r/(1-r)+r*(1+r)/(1-r)**2)

def ff(t,v):return max(F(v*v)-t,F(0))

@lru_cache(None)
def deep_f(t,b,d):
 # Every future increment is 2a+2b-5 after this entrance.
 A=max(3,ceilroot(t)+3)
 slopes=[2*v for v in d];intercepts=[v*(2*x-5) for v,x in zip(d,b)]
 j=max(range(5),key=lambda k:(slopes[k],intercepts[k]))
 for slope,intercept in zip(slopes,intercepts):
  if slope<slopes[j]:
   c=(intercept-intercepts[j])/(slopes[j]-slope)
   A=max(A,(c.numerator+c.denominator-1)//c.denominator)
 out=sum((F(1,3**a)*max(v*(ff(t,x+a-2)-ff(t,x+a-3)) for v,x in zip(d,b)) for a in range(3,A)),F(0))
 m0,m1,_=tails(3,A)
 return out+slopes[j]*m1+intercepts[j]*m0

@lru_cache(None)
def eta_g_deep(t,n,b):
 g=lambda v:ff(t,n*v)/n-ff(t,v)
 A=max(3,ceilroot(t)+3)
 while any(F((n-1)*(2*(x+A-3)+1))<max(g(k+1)-g(k) for k in range(x,x+A-2)) for x in b):A+=1
 out=sum((F(1,3**a)*max(g(k+1)-g(k) for x in b for k in range(x,x+a-2)) for a in range(3,A)),F(0))
 m0,m1,_=tails(3,A)
 return out+(n-1)*(2*m1+(2*max(b)-5)*m0)

def p_eta(t,b,ps):return sum(m*ff(t,x) for m,x in zip(ps,b))+deep_f(t,b,(F(1),)*5)

@lru_cache(None)
def pure_add(t,ps):
 p2=[p_eta(F(0),b,ps) for b in BS];M2=max(p2);x=sum(ps)
 N=max(2,ceilroot(t)+1)
 out=[F(0)]*10
 for n in range(2,N):
  mf=max(n*n*p_eta(t/(n*n),b,ps) for b in BS)
  for j,b in enumerate(BS):
   pg=sum(m*(ff(t,n*v)/n-ff(t,v)) for m,v in zip(ps,b))+eta_g_deep(t,n,b)
   out[j]+=F(4,5**n)*(pg+F(n-1,n)*mf)
 m0,m1,m2=(4*x for x in tails(5,N))
 for j,b in enumerate(BS):out[j]+=m1*p2[j]+(m2-m1)*M2-m0*(p_eta(t,b,ps)+t*x)
 return tuple(out)

def simplex(n,cap):return [(F(0),)*n]+[tuple(cap if i==j else F(0) for i in range(n)) for j in range(n)]

def parameters():return product(simplex(5,F(1,2)),simplex(2,F(1,4)),simplex(5,F(1,4)),simplex(5,F(1,72)),(F(3,4),F(1)))

def data(par):
 D,alpha,beta,late,z=par
 w=tuple(1-v for v in D);d=tuple(z-alpha[ROOT[l]]-beta[l] for l in range(5));mass=tuple(w[l]*d[l]/9-late[l] for l in range(5));ps=tuple(v/9 for v in w)
 s=sum(mass);T=max(sum(mass[l] for l in range(5) if ROOT[l]==r) for r in (0,1))+max(mass)+max(d)/18+sum(w)/36+max(sum(w[l] for l in range(5) if ROOT[l]==r) for r in (0,1))/36+max(w)/36+F(1,72)
 den=s-T/5
 if den<=0:raise ValueError('positive actual survivor denominator')
 return d,mass,ps,s,den

def f35(t,dat):
 d,mass,ps,s,den=dat
 return max(sum(m*ff(t,x) for m,x in zip(mass,b))+deep_f(t,b,d)+a for b,a in zip(BS,pure_add(t,ps)))

def grid(h):
 # Every finite inner7 threshold is h^2/k^2 for some k<h.
 thresholds={F(h*h,k*k) for k in range(1,h)}|{F(0)}
 maxima={t:F(0) for t in thresholds if t}
 witnesses={}
 for count,par in enumerate(parameters(),1):
  dat=data(par);s=dat[3];den=dat[4]
  fs={t:f35(t,dat) for t in thresholds}
  for k in range(1,h):
   t=F(h*h,k*k);N=max(2,ceilroot(t))
   raw=F(29,35)*fs[t]
   for n in range(2,N):raw+=F(36*n*n,5*7**n)*fs[t/(n*n)]
   m0,_,m2=tails(7,N)
   raw+=F(36,5)*(m2*fs[F(0)]-t*m0*s)
   val=raw/den
   if val>maxima[t]:maxima[t]=val;witnesses[t]=par
 need(count==1296,'all1296 product vertices')
 return maxima,witnesses

def product_mass(caps,N):
 out={1:F(1)}
 for p,c in caps:
  nxt={}
  for a,w in out.items():
   for n in range(1,(N-1)//a+1):nxt[a*n]=nxt.get(a*n,F(0))+w*(1-c/p if n==1 else c*F(p-1,p**n))
  out=nxt
 return out

def fallback(branch,t):
 u=list(map(F,branch['reference_pure_masses']));caps=tuple(zip((3,5,7),(1/v for v in u)))
 N=ceilroot(t);pr=product_mass(caps,N)
 second=prod(1+c*F(3*p-1,(p-1)**2) for p,c in caps)
 return F(branch['uniform357_Haar_density_bound'])*prod(u)*(second-t+sum((t-n*n)*w for n,w in pr.items()))

def run(h,pr):
 maxima,witnesses=grid(h)
 bound={}
 branch_rows={}
 for t,v in maxima.items():
  rows=[min(v,fallback(b,t)) if b['ternary_case']=='modulus9_effective' else fallback(b,t) for b in pr['branches']]
  bound[t]=min(max(rows),G-min(t,F(1)))
  branch_rows[str(t)]=rows
 need(len(pr['branches'])==12,'all12 original missing-class branches')
 caps=((11,F(5,3)),(13,F(2)));pm=product_mass(caps,h)
 second=prod(1+c*F(3*p-1,(p-1)**2) for p,c in caps)
 tail2=second-sum(n*n*w for n,w in pm.items());tail0=1-sum(pm.values())
 physical=sum(w*n*n*bound[F(h*h,n*n)] for n,w in pm.items())+G*tail2-h*h*tail0
 return {'h':h,'tau':h*h,'vertex_count':1296,'relaxed_source_maxima':{str(t):v for t,v in maxima.items()},
   'relaxed_maximum_vertices':{str(t):p for t,p in witnesses.items()},'twelve_branch_bounds':branch_rows,
   'source_bounds':{str(t):v for t,v in bound.items()},'physical':physical,'supported_hinge':physical/RHO,
   'shift_square':h*h+physical/RHO,'AP_tail_mass':tail0,'AP_tail_second_moment':tail2}

def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [encode(v) for v in x]
 return x

def unique(pairs):
 out={}
 for k,v in pairs:
  need(k not in out,'duplicate JSON key: '+k);out[k]=v
 return out

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--source-directory',type=Path,default=BASE)
 parser.add_argument('--certificate',type=Path,default=BASE/'certificates/shared_cell_square_certificate.json')
 parser.add_argument('--write',action='store_true')
 args=parser.parse_args();sources={}
 for name,pin in PINS.items():
  raw=read_artifact_bytes(args.source_directory/name)
  need(hashlib.sha256(raw).hexdigest()==pin,'source SHA-256: '+name)
  sources[name]=json.loads(raw,object_pairs_hook=unique)
 pr=sources['certificates/pure_root_profile_certificate.json'];hc=sources['certificates/shared_cell_hinges_certificate.json']['same_actual_AP13_consumer']
 need(F(pr['source_inputs']['G'])==G and F(hc['survival_lower'])==RHO,'same actual source square and AP13 normalization')
 rows=[run(h,pr) for h in (4,9)]
 need(rows[0]['shift_square']==F(148878188597300778613,914721425816667898),'exact tau16 shift square')
 need(rows[0]['shift_square']<F(hc['supported_square']),'strict same-law square improvement')
 need(rows[1]['supported_hinge']==F(7950179084001887172777104410541784715667,76933096761156988347518483945560826250),'exact tau81 supported hinge')
 need(rows[1]['supported_hinge']<F(27462732511027063792077002926276002,234516374824438312292389830652525),'strict improvement on pure-root square hinge')
 result=encode({'schema':'erdos7-shared-cell-square-v1','source_sha256':PINS,'same_actual_law_inputs':{'G357':G,'rho13':RHO,'previous_Gamma13':F(hc['supported_square'])},'targets':rows,
   'scope':'Same actual uniform357 and supported AP(4,6)13 laws, every original residue/label and arbitrary finite heights. Complete ternary,5,7,11,13 tails. Ordinary monotone-cost and continuous-vertex proof; no actual-layout sharpness or Lean endpoint.'})
 if args.write:write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
 else:need(json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique)==result,'whole certificate mismatch')
 print('PASS 2x1296 vertices and all12 branches; Gamma13 <= '+str(float(rows[0]['shift_square']))+'; T13(81) <= '+str(float(rows[1]['supported_hinge'])))

if __name__=='__main__':main()
