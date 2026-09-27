#!/usr/bin/env python3
"""Exact signed-pair certificate for all per-edge root endpoints.
One actual Scott-Sokal submeasure; complete inherited loss/query arrays.
The source and all-height arguments are in Report623; no Lean verification.
"""
import argparse,hashlib,json,struct,subprocess,tempfile,time
from fractions import Fraction as Q
from itertools import product,combinations
from math import prod
from pathlib import Path
QS=(7,11,13,17,19)
POINTS=tuple((i,j) for i,j in product(range(2),range(4)) if (i,j)!=(0,0))
MBASE=(0,5,11,15);MNEXT={0:1,5:6,11:12,15:16}
TEMPLATES=tuple((R,C,I,J,L,M) for R,C,(I,J),L,M in product(range(2),range(4),POINTS,range(5),[m for m in range(20) if m!=10]))
TIDX={t:i for i,t in enumerate(TEMPLATES)}
CELLS=tuple((l,m) for l,m in product(range(5),range(20)) if m!=10 and (l//3,m//5)!=(0,0))
HS=1<<23;CS=1<<27;DEN=58400
# The source-data pin is checked against the exact published bytes below.
SOURCE_SHA='2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f'
def fp_floor(x,scale):return x.numerator*scale//x.denominator
def fp_ceil(x,scale):return -((-x.numerator*scale)//x.denominator)
def sw(j):return 4-j if j in (1,3) else j
def swap(t):
 R,C,I,J,L,M=t
 return R,sw(C),I,sw(J),L,5*sw(M//5)+M%5

def pair_reps():
 for t in ((R,C,I,J,L,M) for R,C,(I,J),L,M in product(range(2),range(4),POINTS,(0,3,4),MBASE)):
  if t>swap(t):continue
  ls=(0,1,3,4) if t[4]==0 else (0,3,4)
  ms=tuple(sorted(MBASE+(MNEXT[t[5]],)))
  for u in ((R,C,I,J,L,M) for R,C,(I,J),L,M in product(range(2),range(4),POINTS,ls,ms)):
   if t==swap(t) and u>swap(u):continue
   yield t,u

def orbit_size(t,u):
 l,k=t[4],u[4]
 if l<3 and k<3:ternary=3 if l==k else 6
 elif l<3 or k<3:ternary=3
 else:ternary=1
 m,n=t[5],u[5];nr=lambda j:4 if j==2 else 5
 if m//5==n//5:quinary=nr(m//5) if m==n else nr(m//5)*(nr(m//5)-1)
 else:quinary=nr(m//5)*nr(n//5)
 root=1 if t==swap(t) and u==swap(u) else 2
 return ternary*quinary*root

def intprod(lines):
 co=[Q(1)]
 for a,b in lines:
  nxt=[Q(0)]*(len(co)+1)
  for k,v in enumerate(co):nxt[k]+=v*a;nxt[k+1]+=v*(b-a)
  co=nxt
 return sum(Q(2)*v/((k+1)*(k+2)) for k,v in enumerate(co))

checks=[]
def check(name,yes,units=1):
 if not yes:raise ArithmeticError(name)
 checks.append({'name':name,'units':units})

def matching(mask,Z,r):
 vs=[q for q in range(5) if mask>>q&1];es=list(combinations(vs,2))
 ans=prod((Z[q] for q in vs), start=Q(1))
 for e in es:ans-=prod(r[q] for q in e)*prod(Z[q] for q in vs if q not in e)
 for e,f in combinations(es,2):
  if set(e).isdisjoint(f):ans+=prod(r[q] for q in e+f)*prod(Z[q] for q in vs if q not in e+f)
 return ans

def integrated_matching(mask,start,end,r):
 vs=[q for q in range(5) if mask>>q&1];es=list(combinations(vs,2))
 ans=intprod([(start[q],end[q]) for q in vs])
 for e in es:ans-=prod(r[q] for q in e)*intprod([(start[q],end[q]) for q in vs if q not in e])
 for e,f in combinations(es,2):
  if set(e).isdisjoint(f):ans+=prod(r[q] for q in e+f)*intprod([(start[q],end[q]) for q in vs if q not in e+f])
 return ans

def generate(source,path):
 raw=source.read_bytes();data=json.loads(raw);check('published full coefficient pin',hashlib.sha256(raw).hexdigest()==SOURCE_SHA)
 c=Q(data['constants']['continuation_c']);gain=1-c;L=list(map(Q,data['complete_coefficients']['loss']));W=list(map(Q,data['complete_coefficients']['weighted_nonunit_query']));co=[gain*l+c*w for l,w in zip(L,W)]
 check('full inventory and query arrays',len(L)==len(W)==512 and L[0]==W[0]==0 and min(co)>=0)
 clo=[fp_floor(x,CS) for x in co];chi=[fp_ceil(x,CS) for x in co]
 check('directed full coefficient intervals',all(Q(lo,CS)<=x<=Q(hi,CS) for x,lo,hi in zip(co,clo,chi)),512)
 screen_bound=2*HS*DEN
 budget_bound=screen_bound*(fp_ceil(gain,CS)+sum(chi))
 check('signed integer overflow excluded',screen_bound<2**63 and 1000*10*budget_bound<2**120)
 r=[Q(1,q-1) for q in QS];a=[Q(1,q*(q-2)) for q in QS]
 mean=[1-Q(3047,2660)*rq-Q(3,4)*aq for rq,aq in zip(r,a)]
 lower=[1-5*rq-aq for rq,aq in zip(r,a)];upper=[1-aq for aq in a]
 es=list(combinations(range(5),2));umax=[r[q]*r[s]/(lower[q]*lower[s]) for q,s in es]
 pol=[]
 for mask in range(1024):
  ee=[k for k in range(10) if mask>>k&1]
  pol.append(1-sum((umax[k] for k in ee),Q())+sum((umax[j]*umax[k] for j,k in combinations(ee,2) if set(es[j]).isdisjoint(es[k])),Q()))
 disjoint=max(sum((umax[j] for j in range(10) if set(es[i]).isdisjoint(es[j])),Q()) for i in range(10))
 check('strict Shearer box all subsets',min(pol)>0 and min(pol)==pol[-1] and disjoint<1,1024)
 codes=[]
 for R,C,I,J,L9,M25 in TEMPLATES:
  codes.append(bytes(((int(m//5==C)*4+int((l//3,m//5)==(I,J))+int(l==L9)+int(m==M25))*2+int(l//3!=R)) for l,m in CELLS))
 local=[]
 for q in range(5):
  vals=[1-r[q]-(r[q]+a[q])*ca-r[q]*n+(r[q]-a[q])*bon for ca,n,bon in product(range(2),range(4),range(2))]
  check('full local Z box '+str(q),min(vals)==lower[q] and max(vals)==upper[q],16)
  local.append([v-mean[q] for v in vals])
  check('whole vector mean '+str(q),all(sum(local[q][row[j]] for row in codes)==0 for j in range(80)),80*5320)
 prs=[(TIDX[t],TIDX[u]) for t,u in pair_reps()]
 covered=sum(orbit_size(TEMPLATES[t],TEMPLATES[u]) for t,u in prs)
 check('complete common source symmetry',len(prs)==317920 and covered==5320**2,len(prs))
 hbar=[matching(31^T,mean,r) for T in range(32)]
 integrated=[]
 for mask in range(32):
  lo=integrated_matching(mask,mean,lower,r);hi=integrated_matching(mask,mean,upper,r)
  check('ordered integrated matching '+str(mask),0<lo<=hi)
  integrated.append((lo,hi))
 edges=[]
 for q,s in es:
  em=(1<<q)|(1<<s);mass=[];query=[None]*8192
  for cq,cs in product(range(16),repeat=2):
   d=local[q][cq];e=local[s][cs];U=d*e;up=max(U,Q());um=min(U,Q());code=16*cq+cs
   for T in range(32):
    base=hbar[T]/10
    if not T>>q&1:base+=hbar[T|(1<<q)]*d/4
    if not T>>s&1:base+=hbar[T|(1<<s)]*e/4
    lo,hi=(Q(),Q()) if T&em else integrated[31^(T|em)]
    high=base+hi*up+lo*um;query[256*T+code]=fp_ceil(high,HS)
    if T==0:mass.append(fp_floor(base+lo*up+hi*um,HS))
  check('directed pair local range '+str((q,s)),len(mass)==256 and len(query)==8192 and all(abs(v)<=2*HS for v in mass+query),8448)
  edges.append((mass,query))
 with path.open('wb') as f:
  f.write(b'E7MATCHPAIRIV1'.ljust(16,b'\0'));f.write(struct.pack('<7I',80,5320,317920,10,16,32,DEN));f.write(struct.pack('<4q',HS,CS,fp_floor(gain,CS),fp_ceil(gain,CS)))
  f.write(bytes(x for c in CELLS for x in c));f.write(bytes(x for t in TEMPLATES for x in t));f.write(b''.join(codes))
  for p in prs:f.write(struct.pack('<2H',*p))
  f.write(struct.pack('<512q',*clo));f.write(struct.pack('<512q',*chi))
  for mass,query in edges:f.write(struct.pack('<256q',*mass));f.write(struct.pack('<8192q',*query))
 return {'source':source.name,'integer_arithmetic_ranges':{'screen_abs_bound':str(screen_bound),'pair_budget_abs_bound':str(budget_bound),'final_crossproduct_abs_bound':str(1000*10*budget_bound)},'source_sha256':hashlib.sha256(raw).hexdigest(),'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'strict_Shearer_min':str(min(pol)),'strict_disjoint_edge_sum':str(disjoint),'mean_Z':list(map(str,mean)),'min_Z':list(map(str,lower)),'max_Z':list(map(str,upper)),'checks':checks,'local_scale':HS,'coefficient_scale':CS}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--source',type=Path,default=Path(__file__).with_name('actual_pair_activation_certificate.json'))
 ap.add_argument('--out',type=Path,default=Path(__file__).with_suffix('.json'))
 ap.add_argument('--threads',type=int,default=2)
 ap.add_argument('--keep-input',type=Path)
 args=ap.parse_args();start=time.monotonic();cpp=Path(__file__).with_suffix('.cpp')
 with tempfile.TemporaryDirectory(prefix='matching-endpoint-exact-') as td:
  td=Path(td);inp=args.keep_input or td/'input.bin';exe=td/'verify';meta=generate(args.source,inp)
  subprocess.run(['c++','-std=c++20','-O3','-DNDEBUG','-pthread',str(cpp),'-o',str(exe)],check=True)
  result=subprocess.run([str(exe),str(inp),str(args.threads)],capture_output=True,text=True,check=True)
  print(result.stderr,end='',flush=True);cert=json.loads(result.stdout)
  gate=Q(int(cert['gate_lower_numerator']),int(cert['denominator']));alpha=Q(2673,138320)
  check('positive complete gate',gate>Q(7,1000))
  check('reference ten-prime head survivor',alpha*gate>Q(1,7100))
  fee=Q(1,780)+Q(4,125000)+Q(1,65536)+2*(Q(1,250000)+Q(1,1600))
  check('Report616 same-source network margin',alpha*(gate-fee)>Q(1,11000))
  check('simpler Report616 margin',alpha*(Q(7,1000)-fee)>Q(1,12000))
  answer={'schema':'matching-endpoint-complete-gate-v1','scope':'Fixed Report617 FA1 central pure source and 15 mask; five live linear-star roots may coincide; square stars project to corresponding first/second linear-star roots; every edge twelve retained labels share endpoint first roots, arbitrary between different edges; full actual source and complete L/W. No arbitrary-head transport. Ordinary exact arithmetic, no Lean.',
   'gate_lower':str(gate),'gate_strict':'7/1000','haar_lower':str(alpha*gate),'haar_strict':'1/7100',
   'network616':{'fee_upper':str(fee),'extendible_head_lower':str(alpha*(gate-fee)),'strict':'1/11000','simpler_strict':'1/12000','scope':'Exactly Report616 fixed parent tuples and ordinary private interfaces; does not pay Reports619/620 arbitrary three-parent fee.'},
   'certificate':cert,'metadata':meta,'predicates':len(checks),'finite_evaluations':sum(x['units'] for x in checks),'elapsed_seconds':time.monotonic()-start,
   'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'kernel_sha256':hashlib.sha256(cpp.read_bytes()).hexdigest(),'new_lean_verification':False}
  args.out.write_text(json.dumps(answer,indent=2)+'\n')
  print(json.dumps({key:answer[key] for key in ('gate_lower','haar_lower','predicates','finite_evaluations','elapsed_seconds')}),flush=True)
if __name__=='__main__':main()
