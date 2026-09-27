#!/usr/bin/env python3
"""Same-law ten-square head with complete first and second query moments.

Each q=7,11,13,17,19 block retains3q,5q,15q,3q^2,5q^2. A fixed
cellwise thinning constructs a common submeasure with union-bound factors;
separate concavity reduces each such factor to64 aligned templates. All
358963200 column-symmetry classes/row choices/ternary endpoints are scanned.
Exact directed dyadic intervals and outward coefficient rounding certify
first-moment, raw-mass and seed180 moment bounds. All heights are summed by
Report591's analytic profiles; this is ordinary proof, not Lean verification.
"""
import argparse
from fractions import Fraction as F
from functools import reduce
from operator import mul
import hashlib
import importlib.util
import itertools
import json
from math import ceil,floor,prod
from pathlib import Path
import shutil
import subprocess
import tempfile

BITS=20
D=2**BITS
SCREEN_DENOMINATOR=12*D
EXPECTED_FIRST=F(2831549921194741,12582912000000000)
CONTROLS=((23,F(2,5)),(29,F(9,20)),(31,F(1,2)))

def product(values):return reduce(mul,values,F(1))


def weighted_coordinate(p):
    return F(3,p-1)+(F(2*p,(p-1)**2)+F(3,p-1))/F(p-2)


def coefficients(source):
    rows=source['coefficient_profile'](3)
    loss=[r['loss_weight'] for r in rows]
    query=[r['query_weight'] for r in rows]
    for j,p in enumerate(source['Q']):loss[128+(1<<j)]-=F(1,4*(p-1))
    weighted=[]
    for index,row in enumerate(rows):
        mode=index//32
        support=row['outside_support']+((5,) if mode in(1,4,5) else())
        w=product(weighted_coordinate(p) for p in support)
        if mode<2:w=w if support else F(0)
        elif mode in(2,4):w*=3
        else:w*=6
        weighted.append(w)
    return loss,query,weighted


def templates(prime):
    result=[]
    r=F(1,prime-1);a=r+F(1,prime*(prime-2))
    for row,column,point_row,point_column in itertools.product(range(2),range(4),range(2),range(4)):
        values=[1-a*(int(i==row)+int(j==column))-r*int((i,j)==(point_row,point_column)) for i,j in itertools.product(range(2),range(4))]
        result.append({'factor':values,'lower':[floor(v*D) for v in values],'upper':[ceil(v*D) for v in values]})
    return result


def canonical_columns():
    # Number of length10 restricted-growth words using0 and up to three
    # other names. Current k names permit k+1 old choices and one new name.
    counts=[1,0,0,0]
    for _ in range(10):
        new=[0,0,0,0]
        for k,n in enumerate(counts):
            new[k]+=(k+1)*n
            if k<3:new[k+1]+=n
        counts=new
    return counts


def screen_values(grid,t):
    first=grid[:4];second=grid[4:]
    a=sum(first);b=sum(second);ma=max(first);mb=max(second)
    return ((t*a+(1-t)*b)/4,max(t*first[j]+(1-t)*second[j] for j in range(4)),max(t*a,(1-t)*b)/4,max(a,b)/12,max(t*ma,(1-t)*mb),max(ma,mb)/3)


def witness_screens(all_templates,codes,t0):
    exact=[F()]*192;low=[F()]*192;high=[F()]*192
    for mask in range(32):
        eg=[];lg=[];hg=[]
        for cell in range(8):
            e=F(int(cell!=0));l=h=D if cell else 0
            for q,code in enumerate(codes):
                if mask>>q&1:continue
                item=all_templates[q][code]
                e*=item['factor'][cell]
                l=l*item['lower'][cell]//D
                h=(h*item['upper'][cell]+D-1)//D
            eg.append(e);lg.append(F(l,D));hg.append(F(h,D))
        for mode,value in enumerate(screen_values(eg,t0)):exact[32*mode+mask]=value
        for mode,value in enumerate(screen_values(lg,t0)):low[32*mode+mask]=value
        for mode,value in enumerate(screen_values(hg,t0)):high[32*mode+mask]=value
    return exact,low,high


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v) for v in value]
    return value
def decode(code):
 kc=code%4;code//=4;kr=code%2;code//=2;col=code%4;row=code//4;return row,col,kr,kc

def direct(source,codes,t0):
 s=source;P=s['P'];Q=s['Q'];G=s['G']
 factors=[]
 for p,code in zip(Q,codes):
  r,c,kr,kc=decode(code)
  factors.append([1-(F(1,p-1)+F(1,p*(p-2)))*(int(i==r)+int(j==c))-F(1,p-1)*int((i,j)==(kr,kc)) for i,j in itertools.product(range(2),range(4))])
 grids={};m=(t0,1-t0)
 for mask in range(32):
  grids[mask]=[F(int(k!=0))*product(factors[q][k] for q in range(5) if not mask>>q&1) for k in range(8)]
 a=sum(m[i]*grids[0][4*i+j]/4 for i,j in itertools.product(range(2),range(4)));sf=F();tail=F();R=F();W=F()
 for mask in range(1,128):
  supp=tuple(p for j,p in enumerate(P) if mask>>j&1);other=tuple(p for p in supp if p!=3);om=sum(1<<j for j,p in enumerate(Q) if p in supp);g=grids[om];mixed=len(supp)>=2
  auxiliary=(len(supp)==2 and bool(set(supp)&{3,5})) or (len(supp)==3 and {3,5}.issubset(supp))
  full=product(F(1,p-2) for p in other);low=product(F(1,p-2)-s['outside_tail'](p,3) for p in other);w=product(F(1,p-1) for p in other);omega=product(F(3,p-1)+(F(2*p,(p-1)**2)+F(3,p-1))/F(p-2) for p in other)
  if 3 not in supp:
   screen=max(sum(m[i]*g[4*i+j] for i in range(2)) for j in range(4)) if 5 in supp else sum(m[i]*g[4*i+j]/4 for i,j in itertools.product(range(2),range(4)))
   R+=screen*full;W+=screen*omega
   if mixed:
    tail+=screen*(full-low)
    if not auxiliary:sf+=screen*w
  else:
   rs=[max(g[4*i:4*i+4]) if 5 in supp else sum(g[4*i:4*i+4])/4 for i in range(2)];first=max(m[i]*rs[i] for i in range(2));deep=max(rs)/3
   R+=(first+deep)*full;W+=(3*first+6*deep)*omega
   if mixed:
    tail+=(first+deep)*(full-low)+max(rs)*low/9
    if not auxiliary:sf+=first*w
 mass=a-sf-tail
 return {'codes':codes,'t0':str(t0),'a':a,'sf':sf,'tail':tail,'s0':mass,'R':R,'W':W,'gate':G*mass-R,'169s0-W':169*mass-W,'Gamma_upper':1+W/mass}

def main():
    parser=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--source-profile',type=Path,default=Path(__file__).with_name('two_centre_star_profile.py'))
    parser.add_argument('--engine',type=Path,default=Path(__file__).with_name('multi_joint_square_scan.cpp'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--cxx',default=shutil.which('clang++') or shutil.which('g++'))
    args=parser.parse_args()
    if not args.cxx:parser.error('C++17 compiler required')
    spec=importlib.util.spec_from_file_location('cubic_source',args.source_profile)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);source=vars(module)
    checks={}
    def require(name,predicate):
        if not predicate:raise ArithmeticError('certificate failed: '+name)
        checks[name]=True
    loss,query,weighted=coefficients(source)
    profiles=[{'name':'first_moment','scale':10**9,'gain':source['G'],'coefficients':[source['G']*a+b for a,b in zip(loss,query)]},
              {'name':'raw_mass','scale':10**9,'gain':F(1),'coefficients':loss},
              {'name':'seed180_margin','scale':10**8,'gain':F(179),'coefficients':[179*a+b for a,b in zip(loss,weighted)]}]
    text=['3']
    for p in profiles:
        scale=p['scale'];gain=p['gain'];coeff=p['coefficients']
        rounded=[ceil(c*scale) for c in coeff];rg=floor(gain*scale)
        bound=(rg+sum(rounded))*SCREEN_DENOMINATOR
        round_error=gain-F(rg,scale)+sum((F(c,scale)-v for c,v in zip(rounded,coeff)),F())
        # For n queried-outside factors, local rounding plus product rounding
        # gives error <=(2n-1)/D<=9/D. Screen maps have Lipschitz constant<=1.
        total_error=F(9,D)*F(rg+sum(rounded),scale)+round_error
        require(p['name']+'_nonnegative',all(c>=0 for c in coeff))
        require(p['name']+'_outward',F(rg,scale)<=gain and all(F(c,scale)>=v for c,v in zip(rounded,coeff)))
        require(p['name']+'_int64',bound<2**63-1)
        p.update({'rounded_gain':rg,'rounded_coefficients':rounded,'accumulation_bound':bound,'bound_bits':bound.bit_length(),'uniform_error_upper':total_error})
        text.extend((f'{scale} {rg}',' '.join(map(str,rounded))))
    all_templates=[templates(p) for p in source['Q']]
    require('positive_thinning_targets',all(F(31,70)<=v<=1 for rows in all_templates for item in rows for v in item['factor']))
    require('factor_directed_intervals',all(F(l,D)<=v<=F(h,D) and h-l<=1 for rows in all_templates for item in rows for l,v,h in zip(item['lower'],item['factor'],item['upper'])))
    for rows in all_templates:
        for item in rows:text.append(' '.join(f'{l} {h}' for l,h in zip(item['lower'],item['upper'])))
    column_counts=canonical_columns()
    require('column_orbits',column_counts==[1,1023,28501,145750] and sum(column_counts)==(4**10+3*2**10+2)//6)
    expected_cases=sum(column_counts)*4**5*2
    require('expected_cases',expected_cases==358963200)
    input_text='\n'.join(text)+'\n'
    with tempfile.TemporaryDirectory(prefix='multi-joint-square-') as directory:
        temp=Path(directory);inp=temp/'coefficients.txt';exe=temp/'scan';inp.write_text(input_text)
        subprocess.run([args.cxx,'-std=c++17','-O3',str(args.engine),'-o',str(exe)],check=True,capture_output=True,text=True)
        output=subprocess.run([str(exe),str(inp)],check=True,capture_output=True,text=True).stdout
    lines=output.splitlines();require('output_rows',len(lines)==3)
    witnesses=[];minima=[]
    for index,line in enumerate(lines):
        fields=list(map(int,line.split()));require('row_shape_'+str(index),len(fields)==10)
        identity,cases,numerator,denominator,t,*codes=fields;p=profiles[index];scale=p['scale']
        require('coverage_'+str(index),identity==index and cases==expected_cases and denominator==scale*SCREEN_DENOMINATOR and t in(1,2) and all(0<=c<64 for c in codes))
        t0=F(t,3);lower=F(numerator,denominator)
        exact,lo,hi=witness_screens(all_templates,codes,t0)
        rg=F(p['rounded_gain'],scale);rounded=[F(c,scale) for c in p['rounded_coefficients']]
        reconstructed=rg*lo[0]-sum((c*x for c,x in zip(rounded,hi)),F())
        exact_gate=p['gain']*exact[0]-sum((c*x for c,x in zip(p['coefficients'],exact)),F())
        independent=direct(source,codes,t0)
        direct_value=(independent['gate'] if index==0 else independent['s0'] if index==1 else 179*independent['s0']-independent['W'])
        require('integer_witness_'+str(index),reconstructed==lower)
        require('fraction_witness_'+str(index),direct_value==exact_gate)
        require('rounding_gap_'+str(index),0<=exact_gate-lower<=p['uniform_error_upper'])
        require('positive_'+str(index),lower>0)
        p['minimum_lower']=lower;minima.append(lower)
        witnesses.append({'profile':p['name'],'codes':codes,'t0':t0,'certified_lower':lower,'exact_unrounded':exact_gate,'direct':independent})
    require('first_moment_certificate',minima[0]==EXPECTED_FIRST)
    nine_haar=49*minima[0]/(616*source['DENSITY'])
    require('nine_prime_haar',nine_haar==F(76451847872258007,36466956697600000000) and nine_haar>F(1,500))
    require('head_mass_sixth',minima[1]>F(1,6))
    # SAME normalized seed probability eta/eta(1), followed by Report592's
    # capped-deletion recurrence, now with certified Gamma<=180.
    gamma=F(180);survivor=F(1);density_factor=F(1);steps=[]
    for q,delta in CONTROLS:
        charge=gamma/(4*delta*(1-delta)*(q-1)**2)
        survivor-=charge;gamma*=1+F(3*q-1,(q-1)**2)/(1-delta);density_factor/=1-delta
        require('continuation_'+str(q),survivor>0)
        steps.append({'prime':q,'control':delta,'charge_upper':charge,'raw_survivor_lower':survivor,'joint_load_upper':gamma,'density_factor':density_factor})
    require('through31_tail',survivor==F(33907,1118040) and density_factor==F(200,33))
    tail_coefficient=(1-survivor)/180
    require('tail_linear_coefficient',tail_coefficient==F(1084133,201247200) and 1-180*tail_coefficient>0)
    # Both lower bounds hold on the SAME raw eta. Its normalized Gamma is
    # <=180-margin/eta(1); multiplying the continuation back by eta(1)
    # retains the margin credit instead of discarding it at normalization.
    same_law_raw=(1-180*tail_coefficient)*minima[1]+tail_coefficient*minima[2]
    ten_haar=same_law_raw/(source['DENSITY']*density_factor)
    require('ten_prime_haar',ten_haar>F(1,3400))
    result={'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),args.engine,args.source_profile)},'input_sha256':hashlib.sha256(input_text.encode()).hexdigest(),'factor_denominator':D,'screen_denominator':SCREEN_DENOMINATOR,'template_count_per_prime':64,'column_orbit_counts':column_counts,'cases_per_profile':expected_cases,'profiles':profiles,'witnesses':witnesses,'nine_prime_haar_lower':nine_haar,'continuation_seed':180,'continuation':steps,'tail_linear_coefficient':tail_coefficient,'same_law_raw_tail_lower':same_law_raw,'ten_prime_haar_lower':ten_haar,'checks':checks}
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps({'checks':len(checks),'cases_per_profile':expected_cases,'minima':[str(x) for x in minima],'nine_prime_haar':str(nine_haar),'ten_prime_haar':str(ten_haar)}))

if __name__=='__main__':main()
