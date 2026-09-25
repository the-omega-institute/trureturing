#!/usr/bin/env python3
"""A same-boundary continuation certificate for749 additional square labels.

Centres3,5 have exponents0/1; five outside primes have exponents0/1/2.
Among844 labels with an outside square, discard5 pure squares,10 existing
star squares and80 ordered pair labels3^a5^b*q^2*r. The remaining749 labels
are charged on Report594's SAME thinned boundary. A single full scan bounds
(1-c)(s0-extra_loss)-c*W, exactly the raw through31 continuation criterion.
No query label or height is removed. This is ordinary mathematics, not Lean.
"""
import argparse
from fractions import Fraction as F
import hashlib
import importlib.util
import itertools
import json
from math import ceil,floor,prod
from pathlib import Path
import shutil
import subprocess
import tempfile

TAIL=F(1084133,201247200)
SCALE=10**9
EXPECTED=F(33025682868271,6291456000000000)
EXPECTED_HAAR=F(29425883435629461,290078064640000000000)


def load_module(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module


def inventory(outside):
    all_rows=[];groups={'pure':[],'old_star':[],'pair_core':[],'extra':[]}
    for exponents in itertools.product(range(3),repeat=5):
        if 2 not in exponents:continue
        size=sum(e>0 for e in exponents);squared=exponents.count(2)
        mask=sum(1<<j for j,e in enumerate(exponents) if e)
        for e3,e5 in itertools.product(range(2),repeat=2):
            label=3**e3*5**e5*prod(q**e for q,e in zip(outside,exponents))
            mode={(0,0):0,(0,1):1,(1,0):2,(1,1):4}[e3,e5]
            cap=F(1,4) if e5 else F(1)
            for q,e in zip(outside,exponents):
                if e==1:cap*=F(1,q-1)
                elif e==2:cap*=F(1,q*(q-2))
            row={'label':label,'e3':e3,'e5':e5,'outside_exponents':exponents,'outside_support_size':size,'squared_outside_coordinates':squared,'mode':mode,'mask':mask,'coefficient':cap}
            if size==1 and e3+e5==0:kind='pure'
            elif size==1 and e3+e5==1:kind='old_star'
            elif size==2 and squared==1:kind='pair_core'
            else:kind='extra'
            groups[kind].append(row);all_rows.append(row)
    return all_rows,groups


def enumerate_coefficients(rows):
    result=[F()]*192
    for row in rows:result[32*row['mode']+row['mask']]+=row['coefficient']
    return result


def closed_coefficients(outside):
    """Independent support formula; pair support keeps only both squares."""
    result=[F()]*192
    for mask in range(1,32):
        support=[q for j,q in enumerate(outside) if mask>>j&1]
        first=[F(1,q-1) for q in support]
        square=[F(1,q*(q-2)) for q in support]
        if len(support)==1:
            result[128+mask]=square[0]/4
            continue
        if len(support)==2:k=prod(square,start=F(1))
        else:k=prod((a+b for a,b in zip(first,square)),start=F(1))-prod(first,start=F(1))
        for mode in(0,1,2,4):result[32*mode+mask]=k/(4 if mode in(1,4) else 1)
    return result


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v) for v in value]
    return value


def main():
    parser=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--source-profile',type=Path,default=Path(__file__).with_name('two_centre_star_profile.py'))
    parser.add_argument('--boundary-profile',type=Path,default=Path(__file__).with_name('multi_joint_square_profile.py'))
    parser.add_argument('--engine',type=Path,default=Path(__file__).with_name('multi_joint_square_scan.cpp'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--cxx',default=shutil.which('clang++') or shutil.which('g++'))
    args=parser.parse_args()
    if not args.cxx:parser.error('C++17 compiler required')
    source=vars(load_module(args.source_profile,'cubic_source'))
    boundary=load_module(args.boundary_profile,'joint_boundary')
    checks={}
    def require(name,predicate):
        if not predicate:raise ArithmeticError('certificate failed: '+name)
        checks[name]=True
    all_rows,groups=inventory(source['Q'])
    counts={k:len(rows) for k,rows in groups.items()}
    labels={k:{row['label'] for row in rows} for k,rows in groups.items()}
    require('inventory_counts',len(all_rows)==844 and counts=={'pure':5,'old_star':10,'pair_core':80,'extra':749})
    require('unique_numerical_labels',len({r['label'] for r in all_rows})==844 and all(r['label']>1 and r['label']%2==1 for r in all_rows))
    require('disjoint_complete_partition',set.union(*labels.values())=={r['label'] for r in all_rows} and all(not labels[a]&labels[b] for a,b in itertools.combinations(labels,2)))
    expected_pairs={3**a*5**b*q*q*r for a,b in itertools.product(range(2),repeat=2) for q in source['Q'] for r in source['Q'] if q!=r}
    require('pair_core_exact',labels['pair_core']==expected_pairs and len(expected_pairs)==80)
    require('no_preexisting_debit',all(max(row['outside_exponents'])==2 and row['e3']<=1 and row['e5']<=1 for row in groups['extra']) and not labels['extra']&(labels['pure']|labels['old_star']))
    extra=enumerate_coefficients(groups['extra'])
    require('independent_closed_profile',extra==closed_coefficients(source['Q']) and sum(v!=0 for v in extra)==109)
    loss,query,weighted=boundary.coefficients(source)
    gain=1-TAIL
    coefficient=[gain*(a+b)+TAIL*w for a,b,w in zip(loss,extra,weighted)]
    rounded=[ceil(c*SCALE) for c in coefficient];rg=floor(gain*SCALE)
    denominator=boundary.SCREEN_DENOMINATOR;D=boundary.D
    bound=(rg+sum(rounded))*denominator
    error=F(9,D)*F(rg+sum(rounded),SCALE)+gain-F(rg,SCALE)+sum((F(c,SCALE)-v for c,v in zip(rounded,coefficient)),F())
    require('nonnegative_coefficients',all(c>=0 for c in coefficient))
    require('outward_rounding',F(rg,SCALE)<=gain and all(F(c,SCALE)>=v for c,v in zip(rounded,coefficient)))
    require('int64_bound',bound<2**63-1)
    all_templates=[boundary.templates(q) for q in source['Q']]
    require('positive_factors',all(F(31,70)<=f<=1 for rows in all_templates for item in rows for f in item['factor']))
    require('factor_intervals',all(F(l,D)<=v<=F(h,D) and h-l<=1 for rows in all_templates for item in rows for l,v,h in zip(item['lower'],item['factor'],item['upper'])))
    column_counts=boundary.canonical_columns();cases=sum(column_counts)*4**5*2
    require('complete_orbit_count',column_counts==[1,1023,28501,145750] and cases==358963200)
    text=['1',f'{SCALE} {rg}',' '.join(map(str,rounded))]
    for rows in all_templates:
        for item in rows:text.append(' '.join(f'{l} {h}' for l,h in zip(item['lower'],item['upper'])))
    input_text='\n'.join(text)+'\n'
    with tempfile.TemporaryDirectory(prefix='outside-square-pair-') as td:
        temp=Path(td);inp=temp/'coefficients.txt';exe=temp/'scan';inp.write_text(input_text)
        subprocess.run([args.cxx,'-std=c++17','-O3',str(args.engine),'-o',str(exe)],check=True,capture_output=True,text=True)
        output=subprocess.run([str(exe),str(inp)],check=True,capture_output=True,text=True).stdout
    fields=list(map(int,output.split()));require('engine_row',len(fields)==10)
    identity,found,numerator,den,t,*codes=fields
    require('full_coverage',identity==0 and found==cases and den==SCALE*denominator and t in(1,2) and all(0<=v<64 for v in codes))
    lower=F(numerator,den);t0=F(t,3)
    exact,lo,hi=boundary.witness_screens(all_templates,codes,t0)
    reconstructed=F(rg,SCALE)*lo[0]-sum((F(c,SCALE)*v for c,v in zip(rounded,hi)),F())
    algebraic=gain*exact[0]-sum((c*v for c,v in zip(coefficient,exact)),F())
    base=boundary.direct(source,codes,t0)
    per_label=sum((row['coefficient']*exact[32*row['mode']+row['mask']] for row in groups['extra']),F())
    independent=gain*(base['s0']-per_label)-TAIL*base['W']
    require('integer_reconstruction',reconstructed==lower)
    require('per_label_reconstruction',independent==algebraic and per_label==sum((c*v for c,v in zip(extra,exact)),F()))
    require('rounding_gap',0<=independent-lower<=error)
    require('positive_tail_certificate',lower==EXPECTED and lower>0)
    # This raw criterion implies head mass>0 and every earlier capped-deletion
    # stage is positive, since their nonnegative charges are partial sums of
    # the same total c*Gamma. No seed180 restriction is silently reimposed.
    density_factor=F(200,33);haar=lower/(source['DENSITY']*density_factor)
    require('haar_certificate',haar==EXPECTED_HAAR and haar>F(1,10000))
    full_remaining=groups['extra']+groups['pair_core']
    full_debit=sum((row['coefficient']*exact[32*row['mode']+row['mask']] for row in full_remaining),F())
    full_envelope=gain*(base['s0']-full_debit)-TAIL*base['W']
    require('full829_simple_union_obstruction',full_envelope<0)
    families={}
    for row in groups['extra']:
        key=f"{row['outside_support_size']},{row['squared_outside_coordinates']}"
        record=families.setdefault(key,{'count':0,'raw_cap_sum':F(),'witness_screened_debit':F()})
        record['count']+=1
        record['raw_cap_sum']+=row['coefficient']*(F(2,3) if row['mode'] in(2,4) else 1)
        record['witness_screened_debit']+=row['coefficient']*exact[32*row['mode']+row['mask']]
    result={'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),args.engine,args.source_profile,args.boundary_profile)},'input_sha256':hashlib.sha256(input_text.encode()).hexdigest(),'inventory':{'counts':counts,'outside_primes':source['Q'],'centre_exponents':[0,1],'outside_exponents':[0,1,2],'extra_labels':sorted(labels['extra']),'excluded_pair_labels':sorted(labels['pair_core']),'previous_pure_labels':sorted(labels['pure']),'previous_star_labels':sorted(labels['old_star']),'families':families},'continuation_coefficient':TAIL,'gain':gain,'scale':SCALE,'factor_denominator':D,'screen_denominator':denominator,'int64_accumulation_bound':bound,'bound_bits':bound.bit_length(),'uniform_rounding_error_upper':error,'column_orbit_counts':column_counts,'cases':cases,'minimum_raw_tail_lower':lower,'haar_lower':haar,'witness':{'codes':codes,'t0':t0,'base_direct':base,'extra_debit':per_label,'unrounded_raw_tail':independent,'full829_simple_union_envelope':full_envelope},'coefficients':[{'old_loss':l,'extra_loss':e,'weighted_query':w,'combined':c,'rounded_up':r} for l,e,w,c,r in zip(loss,extra,weighted,coefficient,rounded)],'checks':checks}
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps({'checks':len(checks),'cases':cases,'extra_labels':counts['extra'],'remaining_pair_labels':counts['pair_core'],'raw_tail_lower':str(lower),'haar_lower':str(haar)}))

if __name__=='__main__':main()
