#!/usr/bin/env python3
"""Exact Bellman certificate producer for canonical y-rough integers.

Standard library only. The separate rough_max_check.py is the verifier.
The canonical-to-all-rough-integers normalization is an external theorem.
"""
import sys
sys.dont_write_bytecode = True

import argparse
from fractions import Fraction
from functools import lru_cache
import json
from math import isqrt
from pathlib import Path


def is_prime(n):
    if n < 2:
        return False
    if n in (2,3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    d = 5
    while d*d <= n:
        if n % d == 0 or n % (d+2) == 0:
            return False
        d += 6
    return True


def build(y,bound):
    assert type(y) is int and y >= 1
    assert type(bound) is int and bound >= 1
    primes = []
    states = {}

    def prime(i):
        while len(primes) <= i:
            candidate = primes[-1]+1 if primes else y+1
            while not is_prime(candidate):
                candidate += 1
            primes.append(candidate)
        return primes[i]

    first_prime = prime(0)
    height,power = 0,first_prime
    while power <= bound:
        height += 1
        power *= first_prime

    @lru_cache(maxsize=None)
    def solve(i,budget,cap):
        q = prime(i)
        best,best_witness = Fraction(1),1
        branches = []
        power = 1
        for a in range(1,cap+1):
            power *= q
            if power > budget:
                break
            child_key = (i+1,budget//power,a)
            child_value,child_witness = solve(*child_key)
            factor = Fraction(q*power-1,(q-1)*power)
            candidate_value = factor*child_value
            candidate_witness = power*child_witness
            branches.append({'a':a,'power':power,'child':list(child_key)})
            if candidate_value > best or (candidate_value == best and candidate_witness < best_witness):
                best,best_witness = candidate_value,candidate_witness
        key = (i,budget,cap)
        states[key] = {'key':list(key),'value':[best.numerator,best.denominator],
                       'witness':best_witness,'branches':branches}
        return best,best_witness

    root = (0,bound,height)
    value,witness = solve(*root)
    return {'schema':'rough-max-bellman-v1','y':y,'bound':bound,
            'root':list(root),'primes':primes,
            'states':[states[key] for key in sorted(states)],
            'scope':'Consecutive primes strictly above y; nonincreasing positive exponents; empty suffix allowed.'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--y',type=int,required=True)
    ap.add_argument('--bound',type=int,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args = ap.parse_args()
    cert = build(args.y,args.bound)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(cert,separators=(',',':'))+'\n')
    root = next(s for s in cert['states'] if s['key'] == cert['root'])
    print(json.dumps({'certificate':str(args.out),'y':args.y,'bound':args.bound,
                      'states':len(cert['states']),'primes':cert['primes'],
                      'value':root['value'],'witness':root['witness']}))


if __name__ == '__main__':
    main()
