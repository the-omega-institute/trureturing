#!/usr/bin/env python3
"""Exact full-layout root-one continuation certificate.
Python standard library constructs rational interval tables; the companion
C++20 kernel exhausts the finite source-symmetry orbits using exact integers.
No floating arithmetic, optimizer result or unpublished numerical probe is
an input. All writes are to the selected output or a temporary directory.
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
HS=1<<21;CS=1<<24;CENTRAL_DEN=58400
# The source-data pin is checked against the exact published bytes below.
SOURCE_SHA='2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f'
NETWORK_SHA='238e10ff2318c7c77f60d533da6901788d53fc882632b8766c448c5f76fb269a'
CHECKS=[]
def check(name,test,units=1):
 if not test:raise ArithmeticError(name)
 CHECKS.append(dict(name=name,evaluations=units))
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

def generate(source,data_path):
 raw=source.read_bytes();sha=hashlib.sha256(raw).hexdigest();check('published complete coefficient pin',sha==SOURCE_SHA)
 data=json.loads(raw);c=Q(data['constants']['continuation_c']);gain=1-c
 L=list(map(Q,data['complete_coefficients']['loss']));W=list(map(Q,data['complete_coefficients']['weighted_nonunit_query']))
 check('full original/query coefficient arrays',len(L)==len(W)==512 and W[0]==L[0]==0 and c==Q(1084133,201247200),1024)
 co=[gain*l+c*w for l,w in zip(L,W)];clo=[fp_floor(x,CS) for x in co];chi=[fp_ceil(x,CS) for x in co]
 check('coefficient interval directions',all(Q(lo,CS)<=x<=Q(hi,CS) for x,lo,hi in zip(co,clo,chi)),512)
 check('nonnegative complete coefficients',all(0<=lo<=hi for lo,hi in zip(clo,chi)) and 0<gain<1,512)
 screen_bound=2*HS*CENTRAL_DEN
 pair_budget_bound=screen_bound*(fp_ceil(gain,CS)+sum(chi))
 # Every selector has total mass at most one; all central denominators
 # divide CENTRAL_DEN. Ten edges and the final250 cross-product are paid.
 arithmetic_ranges=dict(screen_abs_bound=screen_bound,pair_budget_abs_bound=str(pair_budget_bound),final_crossproduct_abs_bound=str(250*10*pair_budget_bound))
 check('signed integer arithmetic cannot overflow',screen_bound<2**63 and 250*10*pair_budget_bound<2**120)
 r=[Q(1,q-1) for q in QS];a=[Q(1,q*(q-2)) for q in QS]
 abar=[1-rq-(rq+aq)/4-rq*(Q(1,7)+Q(1,5)+Q(1,19)) for rq,aq in zip(r,a)]
 bbar=[(rq-aq)/2 for rq,aq in zip(r,a)]
 amin=[1-5*rq-aq for rq,aq in zip(r,a)];amax=[1-rq for rq in r];bmax=[rq-aq for rq,aq in zip(r,a)]
 check('positive aligned source templates',min(amin)==Q(29,210) and all(x>0 for x in amin),5)
 check('mean formula',all(x==1-Q(4377,2660)*rq-aq/4 for x,rq,aq in zip(abar,r,a)),5)
 check('complete template and central domains',len(TEMPLATES)==len(TIDX)==5320 and len(CELLS)==80)
 codes=[]
 for R,C,I,J,L9,M25 in TEMPLATES:
  codes.append(bytes(((int(m//5==C)*4+int((l//3,m//5)==(I,J))+int(l==L9)+int(m==M25))*2+int(l//3!=R)) for l,m in CELLS))
 check('local state bounds',all(v<16 for row in codes for v in row),5320*80)
 # Uniform template means are identical at all positive unmasked cells.
 sums=[(sum(row[k]//8 for row in codes),sum((row[k]//2)%4 for row in codes),sum(row[k]%2 for row in codes)) for k in range(80)]
 check('actual template means at every cell',all((Q(x,5320),Q(y,5320),Q(z,5320))==(Q(1,4),Q(1,7)+Q(1,5)+Q(1,19),Q(1,2)) for x,y,z in sums),80)
 prs=[];covered=0;first=set()
 for t,u in pair_reps():prs.append((TIDX[t],TIDX[u]));covered+=orbit_size(t,u);first.add(t)
 check('common source pair orbit coverage',len(first)==372 and len(prs)==317920 and covered==5320**2,len(prs))
 hbar=[];pbar=[]
 for T in range(32):
  rest=[q for q in range(5) if not T>>q&1];pp=prod((abar[q] for q in rest),start=Q(1));hh=pp+sum(bbar[q]*prod((abar[j] for j in rest if j!=q),start=Q(1)) for q in rest)
  hbar.append(hh);pbar.append(pp)
 local=[]
 for q in range(5):
  vals=[]
  for ca,n,bon in product(range(2),range(4),range(2)):
   av=1-r[q]-(r[q]+a[q])*ca-r[q]*n;bv=(r[q]-a[q])*bon
   vals.append((av-abar[q],bv-bbar[q]))
  local.append(vals)
 intervals=[];rational_bounds=[]
 for q,rr in combinations(range(5),2):
  loaa=[];hiaa=[];loab=[];hiab=[];mask=(1<<q)|(1<<rr)
  for T in range(32):
   if T&mask:loaa.append(Q(0));hiaa.append(Q(0));loab.append(Q(0));hiab.append(Q(0));continue
   rest=[j for j in range(5) if not (T|mask)>>j&1]
   for aa,bb,aaout,about in [(amin,[Q(0)]*5,loaa,loab),(amax,bmax,hiaa,hiab)]:
    pp=intprod([(abar[j],aa[j]) for j in rest]);hh=pp
    for j in rest:hh+=intprod([(bbar[j],bb[j])]+[(abar[k],aa[k]) for k in rest if k!=j])
    aaout.append(hh);about.append(pp)
  check('ordered integrated positive coefficients '+str((q,rr)),all(0<=loaa[T]<=hiaa[T] and 0<=loab[T]<=hiab[T] for T in range(32)),32)
  mass=[];query=[None]*8192;edge_lo=Q(0);edge_hi=Q(0)
  for cq,cr in product(range(16),repeat=2):
   da,db=local[q][cq];dc,dd=local[rr][cr];U=da*dc;V=da*dd+db*dc;up=max(U,Q(0));um=min(U,Q(0));vp=max(V,Q(0));vm=min(V,Q(0));code=16*cq+cr
   for T in range(32):
    base=hbar[T]/10
    if not T>>q&1:base+=(hbar[T|(1<<q)]*da+pbar[T|(1<<q)]*db)/4
    if not T>>rr&1:base+=(hbar[T|(1<<rr)]*dc+pbar[T|(1<<rr)]*dd)/4
    high=base+hiaa[T]*up+loaa[T]*um+hiab[T]*vp+loab[T]*vm
    query[256*T+code]=fp_ceil(high,HS)
    if Q(query[256*T+code],HS)<high:raise ArithmeticError('upper interval')
    if T==0:
     low=base+loaa[T]*up+hiaa[T]*um+loab[T]*vp+hiab[T]*vm;mass.append(fp_floor(low,HS))
     if Q(mass[-1],HS)>low:raise ArithmeticError('lower interval')
     edge_lo=min(edge_lo,low)
    edge_hi=max(edge_hi,abs(high))
  check('directed signed local grids '+str((q,rr)),len(mass)==256 and len(query)==8192 and all(abs(x)<=2*HS for x in mass+query),8448)
  intervals.append((mass,query));rational_bounds.append(dict(edge=[q,rr],mass_min=str(edge_lo),query_abs_max=str(edge_hi)))
 with data_path.open('wb') as f:
  f.write(b'E7ROOTONEINTV1'.ljust(16,b'\0'));f.write(struct.pack('<7I',80,5320,317920,10,16,32,58400));f.write(struct.pack('<4q',HS,CS,fp_floor(gain,CS),fp_ceil(gain,CS)))
  f.write(bytes(x for cell in CELLS for x in cell));f.write(bytes(x for tp in TEMPLATES for x in tp));f.write(b''.join(codes))
  for pair in prs:f.write(struct.pack('<2H',*pair))
  f.write(struct.pack('<512q',*clo));f.write(struct.pack('<512q',*chi))
  for mass,query in intervals:f.write(struct.pack('<256q',*mass));f.write(struct.pack('<8192q',*query))
 return dict(source_sha256=sha,source=source.name,input_sha256=hashlib.sha256(data_path.read_bytes()).hexdigest(),input_bytes=data_path.stat().st_size,rational_local_bounds=rational_bounds,integer_arithmetic_ranges=arithmetic_ranges,source_density_D='3458/405',Haar_factor='2673/138320',local_scale=HS,coefficient_scale=CS,central_denominator=CENTRAL_DEN,templates=5320,pair_representatives=317920,covered_template_pairs=covered,mean_A=list(map(str,abar)),mean_B=list(map(str,bbar)),checks=CHECKS)

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--source',type=Path,default=Path(__file__).with_name('actual_pair_activation_certificate.json'));parser.add_argument('--network-source',type=Path,default=Path(__file__).with_name('three_parent_forward_kernels.json'));parser.add_argument('--out',type=Path,default=Path(__file__).with_suffix('.json'));parser.add_argument('--threads',type=int,default=2);parser.add_argument('--keep-input',type=Path);args=parser.parse_args();start=time.monotonic()
 cpp=Path(__file__).with_suffix('.cpp')
 with tempfile.TemporaryDirectory(prefix='root-one-exact-') as td:
  td=Path(td);inp=args.keep_input or td/'input.bin';exe=td/'verify';meta=generate(args.source,inp)
  subprocess.run(['c++','-std=c++20','-O3','-DNDEBUG','-pthread',str(cpp),'-o',str(exe)],check=True)
  result=subprocess.run([str(exe),str(inp),str(args.threads)],capture_output=True,text=True,check=True)
  print(result.stderr,end='',flush=True);exact=json.loads(result.stdout)
  gate=Q(int(exact['gate_lower_numerator']),int(exact['denominator']));haar=Q(2673,138320)*gate
  check('full-layout strict continuation margin',gate>Q(7,250))
  check('ten-prime Haar margin',haar>Q(1,1900))
  nraw=args.network_source.read_bytes();nsha=hashlib.sha256(nraw).hexdigest();check('published whole-network coefficient pin',nsha==NETWORK_SHA)
  nd=json.loads(nraw);nf=nd['fees'];nc=nd['constants']
  check('same-source network density interfaces',Q(nc['alpha'])==Q(2673,138320) and nc['single_head_cap']==2 and nc['head_pair_cap']==4 and list(map(Q,nc['head_continuation_caps']))==[Q(5,3),Q(20,11),Q(2)] and nc['generated_conditional_Haar_cap']==6)
  check('whole-network analytic fee bounds',Q(nf['early_roots'])<Q(1,2600) and Q(nf['late_roots'])<Q(1,125000) and Q(nf['ordinary_single_head'])==Q(1,131072) and Q(nf['two_parent'])<Q(1,250000) and Q(nf['three_parent'])<Q(1,1600),5)
  fee=Q(1,780)+Q(4,125000)+Q(1,65536)+2*(Q(1,250000)+Q(1,1600))
  network_simple=Q(2673,138320)*(Q(7,250)-fee);network_exact=Q(2673,138320)*(gate-fee)
  check('same-source extendible head margin',network_exact>network_simple>Q(1,2100))
  network=dict(source_sha256=nsha,scope='Exactly Report616 outside-owner and ordinary-domain conditions, attached to the fixed reference ten-prime head and the present restricted head phase class; no arbitrary-head-prime transfer asserted.',total_fee_upper=str(fee),exact_extendible_head_lower=str(network_exact),simple_extendible_head_lower=str(network_simple),strictly_greater_than='1/2100',full_density_lower='1/(2100 Q_off)')
  answer=dict(schema='root-one-all-star-complete-gate-v1',scope='Fixed central FA1+15=0; outside first pure0modq or absent; higher outside pure phases/heights arbitrary; every central star and pair phase arbitrary; outside star roots1..5, square1/2modq^2, paircomponents1; same complete Report604 L/W arrays.',certificate=exact,gate_lower=str(gate),gate_strict='7/250',haar_lower=str(haar),haar_strict='1/1900',network_consequence=network,metadata=meta,predicates=len(CHECKS),finite_evaluations=sum(x['evaluations'] for x in CHECKS),elapsed_seconds=time.monotonic()-start,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),kernel_sha256=hashlib.sha256(cpp.read_bytes()).hexdigest(),new_lean_verification=False)
  args.out.write_text(json.dumps(answer,indent=2)+'\n');print(json.dumps({k:answer[k] for k in ['gate_lower','haar_lower','predicates','finite_evaluations','elapsed_seconds']}),flush=True)
if __name__=='__main__':main()
