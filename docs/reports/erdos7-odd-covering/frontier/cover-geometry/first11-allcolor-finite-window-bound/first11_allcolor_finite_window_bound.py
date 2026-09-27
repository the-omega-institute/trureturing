#!/usr/bin/env python3
"""Exact all-color certificate for two finite first-eleven windows (report553).

Requires Python 3.10+ and a C++17 compiler with signed 128-bit integers
(GCC or Clang). The generated integer loop is compiled in a temporary
folder; no binary is retained. The default output is beside this script.
All mathematical arithmetic is rational or explicitly bounded integer.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import lcm
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import tempfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
parser.add_argument('--compiler', default='c++', help='C++17 compiler executable (default: c++)')
args = parser.parse_args()
compiler = shutil.which(args.compiler)
if compiler is None:
    parser.error('C++ compiler not found; provide --compiler with GCC or Clang')
if not args.output.parent.is_dir():
    parser.error('output parent directory does not exist')

COFACTORS=[(0,b) for b in range(8)]+[(1,b) for b in range(3)]+[(2,b) for b in range(2)]+[(a,0) for a in range(3,8)]
checks={}
def check(name,v):
    if not v:raise ValueError(name)
    checks[name]=True

def chain(p,j,e):
    return (e,0 if e==0 else (4 if p==5 else 5)+(p if j==1 and e>=2 else 0))

def partition(p):
    pure={(e,j*p**(e-1)) for e,j in product(range(1,5),(1,2))}
    mixed={(e,j*p**(e-1)) for e,j in product(range(1,5),((3,) if p==5 else (3,4)))}
    slots={chain(p,j,e) for e,j in product(range(8),range(2))}
    cuts=pure|mixed|slots
    leaves=[]
    def walk(d,r):
        if d<(2 if p==5 else 1) or any(e>d and s%p**d==r for e,s in cuts):
            for j in range(p):walk(d+1,r+j*p**d)
        else:leaves.append((d,r))
    walk(0,0)
    def hit(atom,c):
        d,r=atom;e,s=c
        return d>=e and r%p**e==s
    check('partition_mass_'+str(p),sum(F(1,p**d) for d,r in leaves)==1)
    out=[]
    for atom in leaves:
        if any(hit(atom,c) for c in pure):continue
        active={(j,e) for j,e in product(range(2),range(8)) if hit(atom,chain(p,j,e))}
        out.append((atom[1],p**(7-atom[0]),any(hit(atom,c) for c in mixed),active))
    return leaves,out

p5,xs=partition(5);p7,ys=partition(7)
period=5**7*7**7
groups=defaultdict(int);Ms=defaultdict(int)
for (x,wx,mx,ax),(y,wy,my,ay) in product(xs,ys):
    if mx and my:continue
    M=sum((j,a) in ax and (j,b) in ay for a,b in COFACTORS for j in range(2))
    groups[x%25,y%7,min(M,10)]+=wx*wy
    Ms[M]+=wx*wy
w5,w7=F(313,625),F(1601,2401)
mass=F(sum(groups.values()),period)
check('cofactor_inventory',len(COFACTORS)==18)
check('old_source_mass',mass==F(53759,214375))
check('active_slot_range',min(Ms)>=2 and max(Ms)<=36)

# Pattern=3*root_sentinel_mask+depth2_type; type0 readsG1,type1 readsG2,
# type2 reads the ray cylinder120. Colors merge separately per depth.
from functools import lru_cache
@lru_cache(None)
def candidates(m):
    out=[]
    for k1,k2 in product(range(1,m+1),repeat=2):
        tails={(1,1),(m,m)}
        if k1==k2==4 and m>=5:tails|={(4,4),(4,5)}
        for k3,k4 in tails:
            z1,z2,zT=F(k1,11),F(k2,121),F(11*k3+k4,14641)
            g=1-z1-z2-zT;h=min(F(5,3),1/g)
            out.append(((k1,k2,k3,k4),g,h,z1,z2,zT))
    return out

def raw_cost(A,t,ts,dtype,ks):
    k1,k2,k3,k4=ks
    z1,z2,zT=F(k1,11),F(k2,121),F(11*k3+k4,14641)
    g=1-z1-z2-zT;h=min(F(5,3),1/g)
    q=F(t,11)+F(1,121)-ts*(z2+zT)-(int(dtype==2))*zT
    if k1==10:q-=F(t-ts,11)+F(int(dtype==0),121)
    if k2==10:q-=F(int(dtype==1),121)
    return h*(A*g-q)

@lru_cache(None)
def minimum(m,A,t,ts,dtype):
    best=None;arg=None
    for ks,g,h,z1,z2,zT in candidates(m):
        k1,k2,_,_=ks
        q=F(t,11)+F(1,121)-ts*(z2+zT)-int(dtype==2)*zT
        if k1==10:q-=F(t-ts,11)+F(int(dtype==0),121)
        if k2==10:q-=F(int(dtype==1),121)
        val=h*(A*g-q)
        if best is None or val<best:best,arg=val,ks
    return best,arg

active_Ms={min(M,10) for M in Ms}
values={};choices={}
for p,M,n,u,v in product(range(24),sorted(active_Ms),range(4),range(2),range(2)):
    mask,dtype=divmod(p,3)
    coeff=[int(n>=1),u,v]
    t=sum(coeff);ts=sum(c for j,c in enumerate(coeff) if mask&(1<<j))
    value,arg=minimum(M,4-max(n-1,0),t,ts,dtype)
    values[p,M,n,u,v]=value;choices[p,M,n,u,v]=arg
check('local_pattern_inventory',len(values)==24*len(active_Ms)*16)

# Verify every tail pair at the only possible cap-crossing first pair,
# for the selected m values. The general reduction is proved in report553.
tail_checks=0
for m in (2,4,10):
    localtypes={(4-max(n-1,0),int(n>=1)+u+v,
                 sum(c for j,c in enumerate((int(n>=1),u,v)) if mask&(1<<j)),dtype)
                for n,u,v,mask,dtype in product(range(4),range(2),range(2),range(8),range(3))}
    # Check breakpoints via exact one-dimensional endpoint algebra; all
    # integer tails are visited only for the cap-crossing pair(4,4).
    if m>=4:
        for A,t,ts,dtype in localtypes:
            allvals=[raw_cost(A,t,ts,dtype,(4,4,k3,k4)) for k3,k4 in product(range(1,m+1),repeat=2)]
            tails={(1,1),(m,m)}|({(4,4),(4,5)} if m>=5 else set())
            reduced=[raw_cost(A,t,ts,dtype,(4,4,k3,k4)) for k3,k4 in tails]
            if min(allvals)!=min(reduced):raise ValueError('tail kink reduction')
            tail_checks+=1
check('tail_kink_cases',tail_checks>0)
den=lcm(*(v.denominator for v in values.values()))
group_list=[(x,y,M,w) for (x,y,M),w in sorted(groups.items())]
lut=[0 if M not in active_Ms else int(values[p,M,n,u,v]*den)
     for p,M,n,u,v in product(range(24),range(11),range(4),range(2),range(2))]
check('signed64_group_weights',max(w for _,_,_,w in group_list)<2**63)
check('integer_lookup_exact',all((v*den).denominator==1 for v in values.values()))
# Exact scaling fits signed128 including every integrated sum.
check('signed128_integration_bound',sum(w for _,_,_,w in group_list)*max(abs(v) for v in lut)<2**126)
cpp=r'''#include <iostream>
#include <string>
#include <algorithm>
using bigint=__int128_t;
bigint parse(const char* s){bool neg=*s=='-';if(neg)s++;bigint x=0;while(*s){x=10*x+(*s-'0');s++;}return neg?-x:x;}
std::string fmt(bigint x){if(!x)return "0";bool neg=x<0;if(neg)x=-x;std::string s;while(x){s+=char('0'+x%10);x/=10;}if(neg)s+='-';std::reverse(s.begin(),s.end());return s;}
struct G{int x,y,m;long long w;};G gs[]={GROUPS};
const char* raw[]={LUT};
int main(){bigint lut[sizeof(raw)/sizeof(raw[0])];for(int i=0;i<int(sizeof(raw)/sizeof(raw[0]));i++)lut[i]=parse(raw[i]);
 for(int p=0;p<24;p++){bigint best;bool seen=false;int ba=0,bb=0,bd=0,bu=0,bv=0;long long ties=0,cases=0;
  for(int a=0;a<5;a++)for(int b=0;b<7;b++)for(int d=0;d<25;d++)for(int u=0;u<5;u++)for(int v=0;v<7;v++){
   bigint val=0;cases++;for(auto g:gs){int n=(g.x%5==a)+(g.y==b)+(g.x==d);int iu=g.x%5==u,iv=g.y==v;
    int idx=((((p*11+g.m)*4+n)*2+iu)*2+iv);val+=lut[idx]*g.w;}
   if(!seen||val<best){seen=true;best=val;ba=a;bb=b;bd=d;bu=u;bv=v;ties=1;}else if(val==best)ties++;
  }std::cout<<p<<" "<<fmt(best)<<" "<<ba<<" "<<bb<<" "<<bd<<" "<<bu<<" "<<bv<<" "<<ties<<" "<<cases<<"\n";
 }
}'''
cpp=cpp.replace('GROUPS',','.join('{'+','.join(map(str,g))+'}' for g in group_list)).replace('LUT',','.join('"'+str(v)+'"' for v in lut))
with tempfile.TemporaryDirectory(prefix='first11-allcolor-') as build_dir:
    src=Path(build_dir)/'exact_loop.cpp'
    exe=Path(build_dir)/'exact_loop'
    src.write_text(cpp)
    subprocess.run([compiler,'-O3','-std=c++17',str(src),'-o',str(exe)],check=True)
    run=subprocess.run([str(exe)],check=True,capture_output=True,text=True)
rows=[]
for line in run.stdout.splitlines():
    p,val,a,b,d,u,v,ties,cases=map(int,line.split())
    rows.append({'pattern':p,'integral':F(val,den*period),'old_query_phases':[a,b,d,u,v],'ties':ties,'evaluated_cases':cases})
check('all735000_query_cases',len(rows)==24 and all(r['evaluated_cases']==30625 for r in rows))
for row in rows:
    p=row['pattern'];a,b,d,u,v=row['old_query_phases']
    exact=sum(F(w,period)*values[p,M,int(gx%5==a)+int(gy==b)+int(gx==d),int(gx%5==u),int(gy==v)] for gx,gy,M,w in group_list)
    if exact!=row['integral']:raise ValueError('exact minimum re-evaluation')
check('24_python_exact_reevaluations',True)
best=min(rows,key=lambda r:r['integral']);Imin=best['integral']
F11=(w5+F(1,4))*(w7+F(1,6))-2*w5*w7+(w5-F(1,5))*(w7-F(1,7))
check('F11_affine_formula',F11==w5/42+w7/20+F(59,840))
def seven_cap_constant(x,y):
    return 5*x*y/363+10*x/231+83*y/825+F(4,165)

def pa_hinge(coords, threshold):
    """Full geometric first moments; only atoms below threshold are finite."""
    mass=F(1);mean=F(1)
    for total,first,_ in coords:
        mass*=total
        mean*=first
    correction=F(0)
    for ns in product(range(1,threshold),repeat=len(coords)):
        nprod=1;weight=F(1)
        for n,(_,_,atom) in zip(ns,coords):
            nprod*=n
            weight*=atom(n)
        if nprod<threshold:
            correction+=(threshold-nprod)*weight
    return mean-threshold*mass+correction

def pure_coordinate(p,w):
    return w,w+F(1,p-1),lambda n:w-F(1,p) if n==1 else F(p-1,p**n)

def capped_coordinate(p,c):
    return F(1),1+c/F(p-1),lambda n:1-c/F(p) if n==1 else c*F(p-1,p**n)

def pa_consumer(x,y):
    coords=[pure_coordinate(5,x),pure_coordinate(7,y)]
    alpha=x*y-F(1,12)
    for p,t,c,a in ((11,2,F(5,3),F(1,3)),(13,2,F(3,2),F(1,4)),
                    (17,4,F(2),F(1,4)),(19,4,F(9,5),F(1,5))):
        alpha-=a*pa_hinge(coords,t)
        coords.append(capped_coordinate(p,c))
    return alpha,pa_hinge(coords,3)

Cref=seven_cap_constant(w5,w7)
check('seven_cap_constant',Cref==F(4270892,36315125))
saving=F11/3-mass+Cref/4+Imin/4
T=F(257,51)
alpha_pure,phi_pure=pa_consumer(F(1,2),F(2,3))
c0=phi_pure-(T-2)*alpha_pure
check('NC4_constant_from_geometric_laws',c0==F(6168733163201163811,542935350932041267200))
check('positive_PA_mass',alpha_pure==F(7575003978548161,73724315753088000)>0)
coefficients=(F(44887686823492905683,27146767546602063360),
              F(20281636668601030051,20313907687933516800),
              F(585035299774741193,203139076879335168))
for x,y in product((F(1,2),F(1)),(F(2,3),F(1))):
    alpha,phi=pa_consumer(x,y)
    d5=x-F(1,2);d7=y-F(2,3)
    if (T-2)*alpha-phi!=-c0+coefficients[0]*d5+coefficients[1]*d7+coefficients[2]*d5*d7:
        raise ValueError('NC4 pure rectangle')
    if alpha<alpha_pure:
        raise ValueError('PA mass minimum')
check('NC4_entire_multiaffine_rectangle',all(c>0 for c in coefficients))
for x,y in product((F(1,2),w5),(F(2,3),w7)):
    union=x*y-(x-F(1,5))*(y-F(1,7))*F(28,33)
    caps=y/5+x/7+F(5,33)*x*y+y/25+y/33+F(5,231)*x+F(5,363)*x*y
    if caps-union!=seven_cap_constant(x,y):
        raise ValueError('seven cap polynomial')
    if pa_hinge([pure_coordinate(5,x),pure_coordinate(7,y)],2)!=x/42+y/20+F(59,840):
        raise ValueError('F11 affine hinge')
check('cap_polynomial_and_first11_hinge',True)
req=c0/(T-2)
check('fixed_source_joint_saving_positive_gap',saving>req)
check('exact_relaxed_minimum',Imin==F(420749579455862173508,553884116843385453125))
check('exact_fixed_source_saving',saving==F(280758968969368570519,39879656412723752625000))

# All originals outside the two stated finite exponent windows may vary.
# Old source shrinkage is charged through G=F11/3+C/4; the nonnegative
# integrand 1-s+f*k/4 proves its comparison in the accompanying report.
def G(x,y):
    return (x/42+y/20+F(59,840))/3+seven_cap_constant(x,y)/4
Gref=G(w5,w7)
Gmin=G(F(1,2),F(2,3))
old_source_charge=Gref-Gmin
# Complement of 0<=a,b<=7,1<=e<=4, counted with two numerical slots.
A=w5+F(1,4);B=w7+F(1,6)
Ahi=F(1,4*5**7);Bhi=F(1,6*7**7)
Joutside=2*(A*B/F(10*11**4)+(Ahi*B+A*Bhi-Ahi*Bhi)*(1-F(1,11**4))/10)
box_charge=2*(w5+sum(F(1,5**a) for a in range(1,8)))*(w7+sum(F(1,7**b) for b in range(1,8)))*sum(F(1,11**e) for e in range(1,5))
check('full_outside_cap_sum',Joutside==2*A*B/10-box_charge)
check('outside_cap_sum_exact',Joutside==F(149819363,16442035995000))
check('pure_rectangle_charge_exact',old_source_charge==F(10687,466908750))
tail_charge=F(5,2)*Joutside
finite_window_saving=saving-old_source_charge-tail_charge
mu=(T-2)*finite_window_saving-c0
check('finite_window_saving_exact',finite_window_saving==F(557875428274563578713,79759312825447505250000))
check('finite_window_nc4_margin_exact',mu==F(6056459552437856401017774855403,612014962076980275282633964800000))
check('finite_window_nc4_margin_positive',mu>0)
check('finite_window_original_inventory',48+18*2*4==192 and 8*8*4-18*4==184)
# A finite stress check supplements, but does not replace, the general
# signed-kernel variation proof. Extreme payoff values suffice for its
# linear optimization at fixed allowed masses.
variation_cases=0
for size in range(1,14):
    for ia in range(1,size+1):
        for ib in range(ia+1):
            a=F(ia,size);b=F(ib,size);c=F(5,3)
            h=min(c,1/a);hp=c if b==0 else min(c,1/b)
            negative=h*(a-b);positive=b*(hp-h)
            for lost,kept in product((F(-1,2),F(1)),repeat=2):
                change=kept*positive-lost*negative
                if change < -F(3,2)*c*(a-b):
                    raise ValueError('signed variation bound')
                variation_cases+=1
check('signed_variation_extreme_payoffs',variation_cases>0)
# Integrate the earlier actual, globally fixed canonical table. Its
# score must be no smaller than the new independent-depth relaxation.
canonical={(0,0):(0,4),(0,1):(2,6),(0,2):(8,8),(0,3):(1,1),
 (0,4):(3,3),(0,5):(5,5),(0,6):(7,7),(0,7):(9,9),
 (1,0):(1,5),(1,1):(3,7),(1,2):(9,9),(2,0):(8,8),(2,1):(9,9),
 (3,0):(2,2),(4,0):(3,3),(5,0):(6,6),(6,0):(7,7),(7,0):(9,9)}
canonical_integral=F(0);canonical_mass=F(0)
for (x,wx,mx,ax),(y,wy,my,ay) in product(xs,ys):
    if mx and my:continue
    G={cs[j] for (a,b),cs in canonical.items() for j in range(2) if (j,a) in ax and (j,b) in ay}
    K=len(G);g=1-F(1464*K,14641);h=min(F(5,3),1/g)
    n=int(x%5==4)+int(y%7==6)+int(x%25==14)
    q=(F(int(n>=1)+int(x%5==4)+int(y%7==6),11)+F(1,121)) if 9 not in G else F(0)
    weight=F(wx*wy,period)
    canonical_integral+=weight*h*((4-max(n-1,0))*g-q)
    canonical_mass+=weight*h*g
check('actual_canonical_above_relaxed_optimum',canonical_integral>=Imin)
check('actual_canonical_integral_exact',canonical_integral==F(1262248822071443611378,1661652350530156359375))
def active_slots(x,y):
    return {(a,b,j) for a,b in COFACTORS for j in range(2)
            if x%5**a==chain(5,j,a)[1] and y%7**b==chain(7,j,b)[1]}
check('same_actual_slots_in_two_regions',active_slots(4,6)==active_slots(4,3) and len(active_slots(4,6))==10)
check('incompatible_relaxed_cardinalities',minimum(10,3,3,0,0)[1]==(9,10,10,10)
      and minimum(10,4,2,0,0)[1]==(10,10,10,10))
check('strict_pointwise_preference_gaps',
      raw_cost(3,3,0,0,(10,10,10,10))-raw_cost(3,3,0,0,(9,10,10,10))==F(5,363)
      and raw_cost(4,2,0,0,(9,10,10,10))-raw_cost(4,2,0,0,(10,10,10,10))==F(35,121))
witness=[]
p=best['pattern'];a,b,d,u,v=best['old_query_phases']
for gx,gy,M,w in group_list:
    n=int(gx%5==a)+int(gy==b)+int(gx==d);iu=int(gx%5==u);iv=int(gy==v)
    Ks=choices[p,M,n,iu,iv]
    witness.append({'r25':gx,'r7':gy,'M_capped':M,'weight':F(w,period),'chosen_Ks':Ks})
out={'scope':'Uniform bound for all144 independently colored original slots on fixed18 cofactors, oldN4/E4; arbitrary originals outside the two stated finite windows and arbitrary13/17/19 continuations. Color sets may vary by old cell in the relaxation; its minimizing choices are not asserted jointly realizable.',
     'checks':checks,'partition_sizes':{5:len(p5),7:len(p7)},'old_group_count':len(groups),'M_mass':{M:F(w,period) for M,w in Ms.items()},
     'oldmass':mass,'query_phase_count':24*5*7*25*5*7,'local_unique_types':minimum.cache_info().currsize,'tail_kink_cases':tail_checks,'lookup_denominator':den,
     'rows':rows,'minimum':best,'relaxed_integral':Imin,'F11':F11,'Cref':Cref,
     'NC4_constant':c0,'PA_mass_minimum':alpha_pure,'NC4_coefficients':coefficients,
     'joint_saving_lower':saving,'required_saving':req,'gap_to_required':saving-req,
     'actual_canonical_integral':canonical_integral,'actual_canonical_lambda11_mass':canonical_mass,
     'old_source_charge':old_source_charge,'outside_cap_sum':Joutside,'joint_tail_charge':tail_charge,
     'finite_window_saving':finite_window_saving,'finite_window_nc4_margin':mu,'finite_window_query_bound':T-mu,
     'variation_stress_case_count':variation_cases,'canonical_colors':{str(k):v for k,v in canonical.items()},
     'relaxed_witness_convention':'For each chosen_K<10 use colors1..K; forK=10 use0..9. This is a pointwise relaxed profile for pattern0, not a global original coloring.',
     'relaxed_witness':witness}
def enc(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return {str(k):enc(x) for k,x in v.items()}
    if isinstance(v,(tuple,list)):return [enc(x) for x in v]
    return v
dest=args.output;dest.write_text(json.dumps(enc(out),indent=2)+'\n')
print(json.dumps(enc({k:out[k] for k in ('old_group_count','query_phase_count','minimum','joint_saving_lower','required_saving','gap_to_required','finite_window_saving','finite_window_nc4_margin','variation_stress_case_count')}),indent=2))
