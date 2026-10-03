#!/usr/bin/env python3
"""Exact full-tail error for actual numerical-slot boundaries of the five-leaf source.

The output controls approximation of a common cap allocation, including
positive clipping. It supplies no positive uniform source estimate by itself.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import prod
from pathlib import Path
import argparse
import json

PRIMES=(5,7,11,13,17,19,23)
CUTOFFS=(100,1000,10000,100000,1000000,10000000,100000000)

def require(condition,reason):
    if not condition:
        raise ValueError(reason)

def calculate():
    b=tuple(F(1,p-2) for p in PRIMES)
    full=(1<<len(PRIMES))-1
    budgets=tuple(prod(b[i] for i in range(len(PRIMES)) if s>>i&1) for s in range(full+1))
    caps=tuple(prod(F(p-1,p-2) for i,p in enumerate(PRIMES) if s>>i&1) for s in range(full+1))

    @lru_cache(None)
    def majorant(s):
        if not s:
            return F(1)
        bit=s&-s
        rest=s^bit
        value=majorant(rest)
        part=rest
        while part:
            block=bit|part
            value+=3*budgets[block]*majorant(s^block)
            part=(part-1)&rest
        return value

    require(majorant(full)==F(189181,80325),'full positive matching majorant')
    rows=[]
    previous_error=None
    for cutoff in CUTOFFS:
        counts=[0]*(full+1)
        reciprocal_sums=[F(0)]*(full+1)
        def enumerate_slots(i,n,s):
            if i==len(PRIMES):
                if s:
                    counts[s]+=1
                    reciprocal_sums[s]+=F(1,n)
                return
            enumerate_slots(i+1,n,s)
            n*=PRIMES[i]
            while n<=cutoff:
                enumerate_slots(i+1,n,s|1<<i)
                n*=PRIMES[i]
        enumerate_slots(0,1,0)
        require(counts[0]==0 and reciprocal_sums[0]==0,'unit is not a root or leaf numerical slot')
        tails=tuple(budgets[s]-caps[s]*reciprocal_sums[s] for s in range(1,full+1))
        require(all(t>0 for t in tails),'every infinite Euler tail retained exactly')
        error=2*sum(t*majorant(full^s) for s,t in enumerate(tails,1))
        require(error>0 and (previous_error is None or error<previous_error),'strict error decrease along growing numerical cutoffs')
        previous_error=error
        rows.append({'nonternary_cutoff':cutoff,
                     'nonternary_numerical_slots':sum(counts),
                     'root_and_leaf_numerical_slots':2*sum(counts),
                     'complete_error_bound':str(error),
                     'complete_error_decimal':float(error)})
    require(rows[5]['nonternary_numerical_slots']==2007,'ten-million slot count')
    require(F(rows[5]['complete_error_bound'])<F(3,10000),'ten-million complete error below three ten-thousandths')
    require(rows[6]['nonternary_numerical_slots']==3819,'hundred-million slot count')
    require(F(rows[6]['complete_error_bound'])<F(1,20000),'hundred-million complete error below one twenty-thousandth')
    return {'schema':'actual-numerical-slot-tail-control-v1',
            'primes':list(PRIMES),
            'positive_matching_majorant':str(majorant(full)),
            'rows':rows,
            'scope':'Two completed allocations agree on the actual root and leaf labels 3n and 9n for every nonternary Q-smooth n up to the cutoff. Each unweighted leaf signed response, its positive clipping, and any one fixed probability-weighted clipped sum differ by at most the displayed complete error. Every exponent tail is retained. This is an approximation bound, not a uniform positive source certificate, actual-family realization, or Lean verification.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected',type=Path,default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    result=calculate()
    if args.write_result:
        args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(args.expected.read_text()),'retained full-tail result matches exact replay')
    print(json.dumps({'status':'PASS','rows':len(result['rows']),
                      'largest_cutoff_slots':result['rows'][-1]['nonternary_numerical_slots'],
                      'largest_cutoff_error':result['rows'][-1]['complete_error_decimal']}))

if __name__=='__main__':
    main()
