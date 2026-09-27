#!/usr/bin/env python3
"""Exact same-source second-moment certificate for Report591's H=3 head.

Reuses its actual pure-survivor source and two-centre screens, certifies
head mass >=1/5 and normalized complete joint-load Gamma <170, and then
uses capped-deletion controls 2/5,9/20,1/2 at primes23,29,31.  All original
and query heights remain present.  This is finite-support ordinary
mathematics, not Lean verification or unrestricted Erdos7 resolution.
"""
import argparse
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from math import isqrt,lcm,prod
from pathlib import Path
import shutil
import subprocess
import tempfile

SEED=F(170)
DENSITY=F(3458,405)
EXPECTED_MARGIN=F(9734678258390705651,101239469005086720000)
CONTROLS=((23,F(2,5)),(29,F(9,20)),(31,F(1,2)))


def weighted_coordinate(p):
    # Sum_(e>=1) (2e+1)c_p(e), for p>=5.
    return F(3,p-1)+(F(2*p,(p-1)**2)+F(3,p-1))/F(p-2)


def direct_weighted_query(source,code,t0):
    """Independent support-by-support evaluation, without coefficient rows."""
    roles=source.decode_layout(code)
    masses=(t0,1-t0)
    W=F()
    for bits in range(1,128):
        support=tuple(p for j,p in enumerate(source.P) if bits>>j&1)
        grid=[]
        for i in range(2):
            for j in range(4):
                value=F(int((i,j)!=(0,0)))
                for role in roles:
                    p=role['prime']
                    if p in support:continue
                    a=int(i==role['row']);b=int(j==role['column'])
                    hit=a+b-a*b*int(role['equal_outside_roots'])
                    value*=1-F(hit,p-1)
                grid.append(value)
        other=tuple(p for p in support if p!=3)
        weight=prod((weighted_coordinate(p) for p in other),start=F(1))
        if 3 not in support:
            if 5 in support:
                screen=max(sum(masses[i]*grid[4*i+j] for i in range(2)) for j in range(4))
            else:
                screen=sum(masses[i]*grid[4*i+j]/4 for i in range(2) for j in range(4))
            W+=screen*weight
        else:
            row=[max(grid[4*i:4*i+4]) if 5 in support else sum(grid[4*i:4*i+4])/4 for i in range(2)]
            first=max(masses[i]*row[i] for i in range(2))
            # sum_(e>=2) (2e+1)*2/3^e =2.
            W+=(3*first+2*max(row))*weight
    return W


def capacity_37():
    scale=10**35
    def sqrt_interval(value):
        a=isqrt(value.numerator*scale**2//value.denominator)
        return F(a,scale),F(a+1,scale)
    def backward(q,H):
        a=F(3*q-1,(q-1)**2);b=F(1,4*(q-1)**2)
        low,high=sqrt_interval(H*b*(a+H*b))
        return H/(1+a+2*H*b+2*high),H/(1+a+2*H*b+2*low)
    low=high=F(36**2)
    for q in (31,29,23):
        low,high=backward(q,low)[0],backward(q,high)[1]
        low=F(low.numerator*scale//low.denominator,scale)
        high=F(-((-high.numerator*scale)//high.denominator),scale)
    return low,high


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v) for v in value]
    return value


def main():
    parser=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--source-profile',type=Path,default=Path(__file__).with_name('two_centre_star_profile.py'))
    parser.add_argument('--engine',type=Path,default=Path(__file__).with_name('two_centre_moment_scan.cpp'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--cxx',default=shutil.which('clang++') or shutil.which('g++'))
    args=parser.parse_args()
    if not args.cxx:parser.error('C++17 compiler with signed128-bit integers required')
    spec=importlib.util.spec_from_file_location('two_centre_head',args.source_profile)
    source=importlib.util.module_from_spec(spec);spec.loader.exec_module(source)
    rows=source.coefficient_profile(3)
    mass_coeff=[];moment_coeff=[]
    for index,row in enumerate(rows):
        mode=index//32
        support=row['outside_support']+((5,) if mode in (1,4,5) else ())
        weighted=prod((weighted_coordinate(p) for p in support),start=F(1))
        if mode<2:weighted=weighted if support else F(0)
        elif mode in (2,4):weighted*=3
        else:weighted*=6
        mass_coeff.append(row['loss_weight'])
        moment_coeff.append((SEED-1)*row['loss_weight']+weighted)
        row['second_moment_nonunit_weight']=weighted
        row['second_moment_gate_coefficient']=moment_coeff[-1]
    denominator=lcm(*(c.denominator for c in mass_coeff+moment_coeff))
    profiles=((F(1),mass_coeff),(SEED-1,moment_coeff))
    bound=max((gain+sum(coeff))*denominator*source.GRID_DENOMINATOR for gain,coeff in profiles)
    if bound>=2**126-1:raise ArithmeticError('signed integer bound exceeded')
    text=[str(denominator)]
    for identifier,(gain,coeff) in enumerate(profiles):
        text += [str(identifier),str(int(gain*denominator)),' '.join(str(int(c*denominator)) for c in coeff)]
    with tempfile.TemporaryDirectory(prefix='two-centre-moment-') as tmp:
        temp=Path(tmp); coefficient_path=temp/'coefficients.txt';exe=temp/'scan'
        coefficient_path.write_text('\n'.join(text)+'\n',encoding='utf-8')
        subprocess.run([args.cxx,'-std=c++17','-O3',str(args.engine),'-o',str(exe)],check=True,capture_output=True,text=True)
        output=subprocess.run([str(exe),str(coefficient_path)],check=True,capture_output=True,text=True).stdout
    lines=output.splitlines();total_denominator=denominator*source.GRID_DENOMINATOR
    checks={}
    def require(name,predicate):
        if not predicate:raise ArithmeticError('certificate failed: '+name)
        checks[name]=True
    require('output_header',len(lines)==5 and int(lines[0])==total_denominator)
    extrema=[];witnesses=[]
    for index,line in enumerate(lines[1:]):
        fields=list(map(int,line.split()))
        require('row_shape_'+str(index),len(fields)==9)
        identifier,t,mn,mx,cmin,cmax,nmin,nmax,cases=fields
        require('coverage_'+str(index),identifier==index//2 and t==index%2+1 and cases==16**5 and 0<=cmin<16**5 and 0<=cmax<16**5 and 1<=nmin<=cases and 1<=nmax<=cases)
        for tag,code,value in (('minimum',cmin,mn),('maximum',cmax,mx)):
            case=source.direct_case(3,code,F(t,3))
            W=direct_weighted_query(source,code,F(t,3))
            mass=case['mass_lower_bound']
            expected=mass if identifier==0 else (SEED-1)*mass-W
            require('direct_'+str(index)+'_'+tag,expected==F(value,total_denominator))
            witnesses.append({'profile':identifier,'extremum':tag,'code':code,'t0':F(t,3),'mass_lower_bound':mass,'weighted_nonunit_query_upper':W,'normalized_Gamma_upper':1+W/mass,'certified_value':expected})
        extrema.append({'profile':identifier,'t0':F(t,3),'minimum':F(mn,total_denominator),'maximum':F(mx,total_denominator),'minimum_code':cmin,'maximum_code':cmax,'minimum_ties':nmin,'maximum_ties':nmax,'cases':cases})
    mass_lower=min(row['minimum'] for row in extrema if row['profile']==0)
    moment_margin=min(row['minimum'] for row in extrema if row['profile']==1)
    require('mass_exceeds_one_fifth',mass_lower>F(1,5))
    require('moment_margin',moment_margin==EXPECTED_MARGIN and moment_margin>0)
    G=SEED;s=F(1);density_factor=F(1);steps=[]
    for q,delta in CONTROLS:
        charge=G/(4*delta*(1-delta)*(q-1)**2)
        s-=charge
        G*=1+F(3*q-1,(q-1)**2)/(1-delta)
        density_factor/=1-delta
        require('positive_survivor_'+str(q),s>0)
        steps.append({'prime':q,'delta':delta,'charge_upper':charge,'survivor_mass_lower':s,'Gamma_upper':G,'ratio_upper':G/s,'density_factor':density_factor})
    haar=F(1,5)*s/(DENSITY*density_factor)
    require('final_mass',s==F(1694459,20124720))
    require('haar_bound',haar==F(1173087,3604832000) and haar>F(1,4000))
    c37=capacity_37()
    require('through37_enclosure',0<c37[0]<c37[1]<SEED)
    out={'scope':'All Report591 H=3 heads on3,5,7,11,13,17,19; arbitrary original labels touching23,29,31. Finite support only. No Lean claim.',
         'source_sha256':hashlib.sha256(args.source_profile.read_bytes()).hexdigest(),
         'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'engine_sha256':hashlib.sha256(args.engine.read_bytes()).hexdigest(),
         'layout_endpoint_count':2*16**5,'same_actual_head_law':'eta=rho restricted to all actual head mixed survivors and auxiliary star survivors',
         'profiles':['mass lower bound','169*mass lower bound-weighted nonunit query upper'],
         'coefficient_denominator':denominator,'accumulator_bound':int(bound),
         'accumulator_bits':int(bound).bit_length(),'coefficients':rows,'endpoint_extrema':extrema,'independent_extremum_reconstructions':witnesses,
         'raw_mass_lower_bound':mass_lower,'normalized_Gamma_seed':SEED,'uniform_moment_margin':moment_margin,
         'continuation_steps':steps,'haar_density_upper_initial':DENSITY,'haar_survivor_lower_bound':haar,
         'through37_full_scalar_capacity_interval':c37,
         'limitation':'The seed170 bound alone does not pass the through37 full-height scalar capacity. This is certificate insufficiency, not an actual covering or impossibility statement.',
         'checks':checks}
    args.output.write_text(json.dumps(encode(out),indent=2)+'\n',encoding='utf-8')
    print(json.dumps(encode({'output':str(args.output),'mass_lower':mass_lower,'margin':moment_margin,'haar_lower':haar,'capacity37':c37,'checks':len(checks)}),indent=2))

if __name__=='__main__':main()
