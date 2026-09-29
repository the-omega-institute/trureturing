#!/usr/bin/env python3
"""Exact dual excluding one full357 scalar source-reweighting certificate."""
from pathlib import Path
from fractions import Fraction
from itertools import product
from math import prod,lcm
from hashlib import sha256
import argparse,json

def require(ok,why):
    if not ok:raise RuntimeError(why)

CERTIFICATE_SHA256='5527489f6a125cd5f7a7e4bada1aa10b773a193634656f9ec3f2ec4a9a0b9824'

def calculate():
    path=Path(__file__).resolve().with_name('fibre_credit_depth_two_full357_scalar_dual_certificate.json')
    require(sha256(path.read_bytes()).hexdigest()==CERTIFICATE_SHA256,'pinned exact dual certificate')
    c=json.loads(path.read_text())
    axes=(27,25,7);period=prod(axes)
    require(c['carrier']==period and c['heights']==[3,2,1],'literal carrier')
    mods=sorted(3**a*5**b*7**g for a,b,g in product(range(4),range(3),range(2)))[1:]
    original=dict(c['originals'])
    require(len(original)==len(c['originals']) and set(original)<=set(mods),'distinct numerical originals')
    require(lcm(*original)==period,'actual original lcm')
    require(all(isinstance(v,int) and 0<=v<d for d,v in original.items()),'original phases')
    D=c['dual_denominator'];require(D==10000,'certificate denominator')
    dual={d:dict(row) for d,row in c['dual_coefficients']}
    require(sorted(dual)==mods,'dual numerical slots')
    for d,row in c['dual_coefficients']:
        require(len(row)==len(dual[d]),'no repeated phase')
        require(all(isinstance(v,int) and v>0 and 0<=a<d for a,v in row),'integer positivity')
        require(sum(v for a,v in row)<=D,'each query-label mixture has mass at most one')
    crt=[(period//a)*pow(period//a,-1,a) for a in axes]
    surviving=[];scores=[];filled_scores=[];all_residues=set()
    for digits in product(*(range(a) for a in axes)):
        x=sum(a*t for a,t in zip(crt,digits))%period
        require(x not in all_residues,'CRT injective');all_residues.add(x)
        if any((x-a)%d==0 for d,a in original.items()):continue
        surviving.append(x)
        score=sum(dual[d].get(x%d,0) for d in mods)
        require(score>=21840,'pointwise dual lower bound')
        scores.append(score)
        extra=0
        for d in mods:
            deficit=D-sum(dual[d].values())
            phase=original.get(d,0)
            if d in original:require(x%d!=phase,'original-phase filler vanishes on actual support')
            if x%d==phase:extra+=deficit
        require(extra==0,'chosen fillers vanish, including missing labels divisible by forbidden3')
        filled_scores.append(score+extra)
    require(len(all_residues)==period and len(surviving)==1081,'complete actual survivor enumeration')
    require(min(scores)==21840,'exact score minimum')
    lower=Fraction(21840,D);require(lower==Fraction(273,125),'lower identity')
    pure_caps=[Fraction(1,p-2) for p in (11,13,17,19,23)]
    factor=prod(1+t for t in pure_caps)
    critical=(2+sum(pure_caps)-factor)/(factor-1)
    gap=lower-critical
    debit=(lower+1)*(factor-1)-sum(pure_caps)
    require(gap==Fraction(2144,127875) and gap>0,'strict lower gap')
    require(debit>1 and 1-debit==Fraction(-2144,294525),'scalar union deficit')
    theta=factor-1;beta=theta-sum(pure_caps)
    filled_deletion_min=beta+theta*Fraction(min(filled_scores),D)
    require(filled_deletion_min>=debit>1,'complete-query mixture permits all-one relaxed deletion')
    output={'CRT_points':period,'actual_survivors':len(surviving),'original_labels':len(original),
     'dual_coefficients':sum(len(v) for v in dual.values()),'lower':str(lower),
     'critical_mean':str(critical),'strict_gap':str(gap),'union_debit_at_lower':str(debit),
     'filled_query_min_score':min(filled_scores),'filled_relaxed_deletion_min':str(filled_deletion_min),
     'probability_cap_conclusion':'R_cap(v)=||v||_1 for every nonnegative measure v on this support, for the stated RC1 scalar support-function relaxation.',
     'scope':'All source laws on this actual finite survivor set; full-height coarse marginals inherit the bound. No LP optimality, covering, or Lean claim.',
     'certificate_sha256':CERTIFICATE_SHA256}

    return output

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        require(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
                'retained result agrees with complete dual replay')
        print(rendered,end='')
    else:args.output.write_text(rendered)

if __name__=='__main__':main()
