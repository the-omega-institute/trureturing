#!/usr/bin/env python3
"""Joint 105/147/245 boundary on Report591's complete cubic-tail source.

The factor-vector generator exhausts root/child equality types and endpoint
masses; no precomputed vectors or floating hull are trusted. Coefficients are
rounded OUTWARD with exact Fraction arithmetic, then the C++ engine scans
367263744 cases using bounded signed 64-bit arithmetic. This is an ordinary
finite certificate with analytic all-height series, not Lean verification.
"""
import argparse
from fractions import Fraction as F
from functools import reduce
import hashlib
import importlib.util
import itertools
import json
from math import lcm
from operator import mul
from pathlib import Path
import shutil
import subprocess
import tempfile

SCALE = 10**9
SCREEN_DENOMINATOR = 12 * 210 * 10 * 12 * 16 * 18
EXPECTED_COUNTS = (374,347,416,320,347,277,410,311)
EXPECTED_LOWER = F(304081382950091,3110400000000000)
EXPECTED_HAAR = F(304081382950091,333864960000000000)


def product(values):
    return reduce(mul,values,F(1))


def candidates(row,column,equal):
    """All joint 7-factor vectors, each divided by210; equal vectors merge.

    Old roots are0 and(0 if equal else 1). The two square parents need at
    most two new names2/3. The105 parent can use one further name4. When
    old roots agree, the spare name1 only adds duplicate representations.
    Different square children have independent relaxed masses0 or1/35;
    identical children use one common endpoint mass.210/6=35,210/35=6.
    """
    old_b=0 if equal else 1
    result={}
    for rn,cn,p3,p5 in itertools.product(range(2),range(4),range(4),range(4)):
        for same in ((False,True) if p3==p5 else (False,)):
            endpoints=((0,0),(6,6)) if same else ((0,0),(6,0),(0,6),(6,6))
            for m3,m5 in endpoints:
                base=[];cell_data=[]
                for i,j in itertools.product(range(2),range(4)):
                    killed=set()
                    if i==row:killed.add(0)
                    if j==column:killed.add(old_b)
                    h3=i==rn and p3 not in killed
                    h5=j==cn and p5 not in killed
                    value=210-35*len(killed)-m3*h3-m5*h5
                    if same and h3 and h5:value+=m3
                    base.append(value);cell_data.append((killed,h3,h5))
                for it,jt,pt in itertools.product(range(2),range(4),range(5)):
                    factors=base.copy();k=4*it+jt;killed,h3,h5=cell_data[k]
                    removed=0 if pt in killed else 35-m3*(h3 and pt==p3)-m5*(h5 and pt==p5)+(m3 if same and h3 and h5 and pt==p3 else 0)
                    factors[k]-=removed
                    factors[0]=0  # auxiliary15 removes the central grid cell
                    if not all(0<=v<=210 for v in factors):raise ArithmeticError('invalid avoidance')
                    witness=(rn,cn,p3,p5,same,m3,m5,it,jt,pt)
                    result.setdefault(tuple(factors),witness)
    return result


def direct_case(source,code,t0,factors):
    """Independent exact support sum; does not use192 coefficient rows."""
    roles=source.decode_layout(code);masses=(t0,1-t0);grids={}
    for mask in range(32):
        support={p for i,p in enumerate(source.Q) if mask>>i&1};grid=[]
        for i,j in itertools.product(range(2),range(4)):
            value=F(int((i,j)!=(0,0)))
            for role in roles:
                p=role['prime']
                if p in support:continue
                if p==7:value*=F(factors[4*i+j],210);continue
                a=int(i==role['row']);b=int(j==role['column'])
                value*=1-F(a+b-a*b*int(role['equal_outside_roots']),p-1)
            grid.append(value)
        grids[mask]=grid
    block=sum(masses[i]*grids[0][4*i+j]/4 for i,j in itertools.product(range(2),range(4)))
    sf=F();tail=F();query=F();weighted=F()
    for mask in range(1,128):
        support=tuple(p for i,p in enumerate(source.P) if mask>>i&1)
        outside=sum(1<<i for i,p in enumerate(source.Q) if p in support);grid=grids[outside]
        other=tuple(p for p in support if p!=3)
        full=product(F(1,p-2) for p in other)
        low=product(F(1,p-2)-source.outside_tail(p,3) for p in other)
        squarefree=product(F(1,p-1) for p in other)
        omega=product(F(3,p-1)+(F(2*p,(p-1)**2)+F(3,p-1))/F(p-2) for p in other)
        mixed=len(support)>=2
        auxiliary=(len(support)==2 and bool(set(support)&{3,5})) or set(support)=={3,5,7}
        if 3 not in support:
            screen=max(sum(masses[i]*grid[4*i+j] for i in range(2)) for j in range(4)) if 5 in support else sum(masses[i]*grid[4*i+j]/4 for i,j in itertools.product(range(2),range(4)))
            query+=screen*full;weighted+=screen*omega
            if mixed:
                tail+=screen*(full-low)
                if not auxiliary:sf+=screen*squarefree
        else:
            rs=[max(grid[4*i:4*i+4]) if 5 in support else sum(grid[4*i:4*i+4])/4 for i in range(2)]
            first=max(masses[i]*rs[i] for i in range(2));deep=max(rs)/3
            query+=(first+deep)*full;weighted+=(3*first+6*deep)*omega
            if mixed:
                tail+=(first+deep)*(full-low)+max(rs)*low/9
                if not auxiliary:sf+=first*squarefree
    mass=block-sf-tail
    return {'block_mass':block,'squarefree_nonblock_charge':sf,'all_height_mixed_tail_charge':tail,'mass_lower':mass,'nonunit_query_upper':query,'gate':source.G*mass-query,'weighted_query_upper':weighted,'169_mass_minus_weighted_query':169*mass-weighted}


def vector_screens(source,code,t0,factors):
    roles=source.decode_layout(code);masses=(t0,1-t0);result=[F()]*192
    for mask in range(32):
        grid=[]
        for i,j in itertools.product(range(2),range(4)):
            v=F(int((i,j)!=(0,0)))
            for index,role in enumerate(roles):
                if mask>>index&1:continue
                p=role['prime']
                if p==7:v*=F(factors[4*i+j],210)
                else:
                    a=i==role['row'];b=j==role['column'];v*=1-F(a+b-a*b*role['equal_outside_roots'],p-1)
            grid.append(v)
        h=[sum(grid[4*i:4*i+4])/4 for i in range(2)]
        sc=[sum(masses[i]*h[i] for i in range(2)),max(sum(masses[i]*grid[4*i+j] for i in range(2)) for j in range(4)),max(masses[i]*h[i] for i in range(2)),max(h)/3,max(masses[i]*grid[4*i+j] for i,j in itertools.product(range(2),range(4))),max(grid)/3]
        for mode,value in enumerate(sc):result[mode*32+mask]=value
    return result


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v) for v in value]
    return value


def main():
    parser=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--source-profile',type=Path,default=Path(__file__).with_name('two_centre_star_profile.py'))
    parser.add_argument('--engine',type=Path,default=Path(__file__).with_name('joint_square_105_scan.cpp'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--cxx',default=shutil.which('clang++') or shutil.which('g++'))
    args=parser.parse_args()
    if not args.cxx:parser.error('C++17 compiler required')
    spec=importlib.util.spec_from_file_location('cubic_head',args.source_profile);source=importlib.util.module_from_spec(spec);spec.loader.exec_module(source)
    rows=source.coefficient_profile(3)
    coefficients=[r['combined_coefficient'] for r in rows]
    coefficients[129]-=source.G/24  #105 is now in the joint block
    rounded=[-(-c.numerator*SCALE//c.denominator) for c in coefficients]
    gain=source.G.numerator*SCALE//source.G.denominator
    bound=(gain+sum(rounded))*SCREEN_DENOMINATOR
    exact_denominator=lcm(49,*(c.denominator for c in coefficients))
    exact_bound=(source.G+sum(coefficients))*exact_denominator*SCREEN_DENOMINATOR
    error=source.G-F(gain,SCALE)+sum((F(a,SCALE)-c for a,c in zip(rounded,coefficients)),F())
    checks={}
    def require(name,predicate):
        if not predicate:raise ArithmeticError('certificate failed: '+name)
        checks[name]=True
    require('coefficient_nonnegative',all(c>=0 for c in coefficients))
    require('outward_rounding',F(gain,SCALE)<=source.G and all(F(a,SCALE)>=c for a,c in zip(rounded,coefficients)))
    require('rounding_error',F()<=error<F(193,SCALE))
    require('int64_accumulation_bound',bound<2**63-1)
    blocks=[]
    for r,c,eq in itertools.product(range(2),range(2),(False,True)):
        vectors=candidates(r,c,eq)
        blocks.append({'row':r,'column':c,'equal':eq,'vectors':list(vectors),'witnesses':list(vectors.values())})
    counts=tuple(len(b['vectors']) for b in blocks)
    require('vector_counts',counts==EXPECTED_COUNTS)
    cases=2*16**4*sum(counts)
    lines=[str(SCALE)+' '+str(gain),' '.join(map(str,rounded)),str(len(blocks))]
    for b in blocks:
        lines.append(f"{b['row']} {b['column']} {int(b['equal'])} {len(b['vectors'])}")
        lines.extend(' '.join(map(str,v)) for v in b['vectors'])
    text='\n'.join(lines)+'\n'
    with tempfile.TemporaryDirectory(prefix='joint-square-105-') as td:
        temp=Path(td);inp=temp/'coefficients.txt';exe=temp/'scan';inp.write_text(text)
        subprocess.run([args.cxx,'-std=c++17','-O3',str(args.engine),'-o',str(exe)],check=True,capture_output=True,text=True)
        output=subprocess.run([str(exe),str(inp)],check=True,capture_output=True,text=True).stdout
    fields=list(map(int,output.split()))
    require('engine_shape',len(fields)==7)
    found_cases,numerator,denominator,othercode,bi,vi,t=fields
    require('engine_full_coverage',found_cases==cases==367263744)
    require('engine_denominator',denominator==SCALE*SCREEN_DENOMINATOR)
    require('engine_witness_range',0<=othercode<16**4 and 0<=bi<len(blocks) and 0<=vi<counts[bi] and t in (1,2))
    lower=F(numerator,denominator);b=blocks[bi];factors=b['vectors'][vi]
    code=16*othercode+b['row']+2*b['column']+8*b['equal'];t0=F(t,3)
    sc=vector_screens(source,code,t0,factors)
    reconstructed=F(gain,SCALE)*sc[0]-sum((F(a,SCALE)*x for a,x in zip(rounded,sc)),F())
    direct=direct_case(source,code,t0,factors)
    exact=source.G*sc[0]-sum((c*x for c,x in zip(coefficients,sc)),F())
    require('rounded_witness_reconstruction',reconstructed==lower)
    require('independent_direct_reconstruction',direct['gate']==exact)
    require('actual_rounding_gap',0<=exact-lower<=error)
    require('positive_uniform_gate',lower==EXPECTED_LOWER and lower>0)
    haar=49*lower/(616*source.DENSITY)
    require('haar_certificate',haar==EXPECTED_HAAR and haar>F(1,1100))
    # A rational boundary example prevents automatically combining this head
    # extension with Report592's Gamma<170 through31 continuation.
    diagnostic=direct_case(source,419682,F(2,3),blocks[2]['vectors'][94])
    require('through31_bound_not_inherited',diagnostic['169_mass_minus_weighted_query']==-F(1810821875393558417,1985087627550720000))
    result={'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),args.engine,args.source_profile)},'generated_input_sha256':hashlib.sha256(text.encode()).hexdigest(),'scale':SCALE,'screen_denominator':SCREEN_DENOMINATOR,'rounded_accumulation_bound':bound,'rounded_bound_bits':bound.bit_length(),'unrounded_accumulation_bound':int(exact_bound),'unrounded_bound_bits':int(exact_bound).bit_length(),'uniform_rounding_error_upper':error,'vector_counts':counts,'cases':cases,'minimum_lower_gate':lower,'haar_lower_bound':haar,'witness':{'code':code,'t0':t0,'block':bi,'vector':vi,'factors':factors,'geometry':b['witnesses'][vi],'direct':direct},'through31_diagnostic':{'code':419682,'t0':F(2,3),'block':2,'vector':94,'direct':diagnostic},'coefficients':[{'exact':c,'rounded_up_integer':a} for c,a in zip(coefficients,rounded)],'checks':checks}
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps({'checks':len(checks),'cases':cases,'lower_gate':str(lower),'haar_lower':str(haar)}))

if __name__=='__main__':main()
