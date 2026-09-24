#!/usr/bin/env python3
"""Arbitrary first-eleven phases in a finite old-slot rectangle (report554).

Requires Python 3.10+ and a C++17 compiler with signed 128-bit integers
(GCC or Clang). Temporary integer code evaluates all old query phases.
Inside-window originals are optional, at most one per prescribed old
slot, and have arbitrary first-eleven residues. No family is enumerated.
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

COFACTORS=list(product(range(8),repeat=2))
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
    groups[x%25,y%7,M]+=wx*wy
    Ms[M]+=wx*wy
w5,w7=F(313,625),F(1601,2401)
mass=F(sum(groups.values()),period)
check('cofactor_inventory',len(COFACTORS)==64)
check('old_source_mass',mass==F(53759,214375))
check('active_slot_range',min(Ms)>=2 and max(Ms)<=128)

from functools import lru_cache
@lru_cache(None)
def local(M,A,t):
    gmin=max(F(0),1-F(1464*M,14641))
    gs={gmin}|{x for x in (F(1,121),F(1,11),F(3,5),F(1)) if x>=gmin}
    ans=[]
    for g in gs:
        h=min(F(5,3),1/g) if g else F(5,3)
        q=t*min(g,F(1,11))+min(g,F(1,121))
        ans.append((h*(A*g-q),g))
    return min(ans)
scalar_cases=0
for M,A,t in product(range(1,129),range(2,5),range(4)):
    gmin=max(F(0),1-F(1464*M,14641))
    g=max(gmin,F(1,11) if t>A else F(1,121) if t==A else F(0))
    h=min(F(5,3),1/g) if g else F(5,3)
    value=h*(A*g-t*min(g,F(1,11))-min(g,F(1,121)))
    if value!=local(M,A,t)[0]:raise ValueError('closed scalar minimum')
    scalar_cases+=1
check('all1536_scalar_closed_forms',scalar_cases==1536)
values={};choices={}
for M,n,u,v in product(sorted(Ms),range(4),range(2),range(2)):
    val,g=local(M,4-max(n-1,0),int(n>=1)+u+v)
    values[M,n,u,v]=val;choices[M,n,u,v]=g
den=lcm(*(v.denominator for v in values.values()))
groups_list=[(x,y,M,w) for (x,y,M),w in sorted(groups.items())]
lut=[0 if M not in Ms else int(values[M,n,u,v]*den)
     for M,n,u,v in product(range(max(Ms)+1),range(4),range(2),range(2))]
check('integer_scale',all((v*den).denominator==1 for v in values.values()))
check('int64_group_weights',max(w for _,_,_,w in groups_list)<2**63)
check('int64_lookup',max(abs(v) for v in lut)<2**63)
check('int128_integrals',sum(g[-1] for g in groups_list)*max(abs(v) for v in lut)<2**126)
cpp=r'''#include <iostream>
#include <string>
#include <algorithm>
using bigint=__int128_t;
std::string fmt(bigint x){if(!x)return "0";bool neg=x<0;if(neg)x=-x;std::string s;while(x){s+=char('0'+x%10);x/=10;}if(neg)s+='-';std::reverse(s.begin(),s.end());return s;}
struct G{int x,y,m;long long w;};G gs[]={GROUPS};long long lut[]={LUT};
int main(){bigint best;bool seen=false;int ba=0,bb=0,bd=0,bu=0,bv=0;long long ties=0,cases=0;
 for(int a=0;a<5;a++)for(int b=0;b<7;b++)for(int d=0;d<25;d++)for(int u=0;u<5;u++)for(int v=0;v<7;v++){
  bigint val=0;cases++;for(auto g:gs){int n=(g.x%5==a)+(g.y==b)+(g.x==d);int iu=g.x%5==u,iv=g.y==v;
   val+=bigint(lut[((g.m*4+n)*2+iu)*2+iv])*g.w;}
  if(!seen||val<best){seen=true;best=val;ba=a;bb=b;bd=d;bu=u;bv=v;ties=1;}else if(val==best)ties++;
 }std::cout<<fmt(best)<<" "<<ba<<" "<<bb<<" "<<bd<<" "<<bu<<" "<<bv<<" "<<ties<<" "<<cases<<"\n";
}'''
cpp=cpp.replace('GROUPS',','.join('{'+','.join(map(str,g))+'}' for g in groups_list)).replace('LUT',','.join(map(str,lut)))
with tempfile.TemporaryDirectory(prefix='e7-arbitrary-rectangle-') as tmpdir:
    src=Path(tmpdir)/'exact_loop.cpp';src.write_text(cpp)
    exe=Path(tmpdir)/'exact_loop'
    subprocess.run([compiler,'-O3','-std=c++17',str(src),'-o',str(exe)],check=True)
    run=subprocess.run([str(exe)],capture_output=True,text=True,check=True)
val,q5,q7,q25,q55,q77,ties,cases=map(int,run.stdout.split())
I=F(val,den*period)
check('all30625_queries',cases==30625)
check('minimizing_query_record',(q5,q7,q25,q55,q77,ties)==(4,6,14,4,6,3))
exact=sum(F(w,period)*values[M,int(gx%5==q5)+int(gy==q7)+int(gx==q25),int(gx%5==q55),int(gy==q77)] for gx,gy,M,w in groups_list)
check('exact_minimum_reevaluation',I==exact)
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
saving=F11/3-mass+Cref/4+I/4
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
check('exact_relaxed_minimum',I==F(1262238451165943772442,1661652350530156359375))
check('exact_fixed_source_saving',saving==F(280697245759512082027,39879656412723752625000))

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
check('finite_window_saving_exact',finite_window_saving==F(557751981854850601729,79759312825447505250000))
check('finite_window_nc4_margin_exact',mu==F(672620076855595943409909974611,68001662452997808364737107200000))
check('finite_window_nc4_margin_positive',mu>0)
check('finite_window_potential_inventory',len(COFACTORS)*2*4==512)
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
witness=[{'r25':gx,'r7':gy,'M':M,'weight':F(w,period),'gmin':max(F(0),1-F(1464*M,14641)),
          'chosen_g':choices[M,int(gx%5==q5)+int(gy==q7)+int(gx==q25),int(gx%5==q55),int(gy==q77)]}
          for gx,gy,M,w in groups_list]
out={'scope':'Fixed48oldsource, full64cofactor rectangle0<=a,b<=7 and depths1..4, eachof512 potential slots optional with atmostoneoriginal peroldslot and arbitrary full11^e residue. Pointwise arbitrary allowed11sets ofmass g>=max0(1−M*1464/14641) relaxes these families; M NOT capped. No assertion that minimizing relaxedsets come from an actual family.',
 'checks':checks,'passed_count':len(checks),'old_group_count':len(groups),'M_range':[min(Ms),max(Ms)],'query_cases':cases,'scale':den,
 'minimum_integral':I,'old_query_phases':[q5,q7,q25,q55,q77],'ties':ties,'joint_score_lower':saving,'required_saving':req,'base_gap':saving-req,
 'source_adjustment':old_source_charge,'outside_cap_sum':Joutside,'outside_tail_charge':tail_charge,'extended_joint_lower':finite_window_saving,'extended_NC4_margin':mu,'final_query_bound':T-mu,
 'PA_mass_minimum':alpha_pure,'NC4_constant':c0,'NC4_coefficients':coefficients,
 'partition_sizes':{5:len(p5),7:len(p7)},'variation_stress_case_count':variation_cases,
 'relaxed_witness':witness,'scalar_closed_form_cases':scalar_cases,'potential_core_slots':64*2*4}
def enc(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return {str(k):enc(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)):return [enc(x) for x in v]
    return v
args.output.write_text(json.dumps(enc(out),indent=2)+'\n')
print(json.dumps(enc({k:out[k] for k in ('passed_count','minimum_integral','old_query_phases','ties','joint_score_lower','required_saving','base_gap','extended_NC4_margin')}),indent=2))
