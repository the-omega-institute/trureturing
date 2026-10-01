#!/usr/bin/env python3
"""Exact mandatory-core Bellman certificate producer (standard library)."""
from fractions import Fraction
from functools import lru_cache
import sys
sys.dont_write_bytecode = True

import argparse
import json
from pathlib import Path


def prime(n):
    if n < 2:
        return False
    if n in (2,3):
        return True
    if n%2 == 0 or n%3 == 0:
        return False
    d = 5
    while d*d <= n:
        if n%d == 0 or n%(d+2) == 0:
            return False
        d += 6
    return True


def build(profile,bound):
    assert type(bound) is int and bound >= 1
    assert all(type(a) is int and a > 0 for a in profile)
    assert all(a >= b for a,b in zip(profile,profile[1:]))
    profile = list(profile)
    primes = []
    states = {}

    def q(i):
        while len(primes) <= i:
            n = primes[-1]+1 if primes else 2
            while not prime(n):
                n += 1
            primes.append(n)
        return primes[i]

    r = len(profile)
    core_suffix = [1]*(r+1)
    for i in range(r-1,-1,-1):
        core_suffix[i] = q(i)**profile[i]*core_suffix[i+1]

    def required(i):
        return profile[i] if i < r else 0

    def remaining(i):
        return core_suffix[i] if i < r else 1

    @lru_cache(maxsize=None)
    def solve(i,budget,cap):
        p = q(i)
        key = (i,budget,cap)
        if cap < required(i) or budget < remaining(i):
            reason = 'required-cap' if cap < required(i) else 'remaining-core-budget'
            states[key] = {'key':list(key),'value':None,'witness':None,
                           'infeasible':reason,'branches':[]}
            return None,None
        best = Fraction(1) if i >= r else None
        witness = 1 if i >= r else None
        branches = []
        for a in range(max(1,required(i)),cap+1):
            power = p**a
            if power > budget:
                break
            child_key = (i+1,budget//power,a)
            if child_key[1] < remaining(i+1):
                branches.append({'a':a,'power':power,
                                 'pruned':'remaining-core-budget'})
                continue
            child_value,child_witness = solve(*child_key)
            branches.append({'a':a,'power':power,'child':list(child_key)})
            if child_value is None:
                continue
            candidate = Fraction(p*power-1,(p-1)*power)*child_value
            candidate_witness = power*child_witness
            if best is None or candidate > best or (candidate == best and candidate_witness < witness):
                best,witness = candidate,candidate_witness
        assert best is not None, ('unexpected infeasible unpruned state',key)
        states[key] = {'key':list(key),'value':[best.numerator,best.denominator],
                       'witness':witness,'infeasible':None,'branches':branches}
        return best,witness

    h = bound.bit_length()-1  # exact floor(log_2(bound))
    root = (0,bound,h)
    solve(*root)
    return {'schema':'mandatory-core-bellman-v1','profile':profile,'bound':bound,
            'core':core_suffix[0], 'core_suffix':core_suffix,
            'root':list(root),'primes':primes,
            'states':[states[k] for k in sorted(states)]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--profile',required=True,help='comma-separated positive nonincreasing exponents')
    ap.add_argument('--bound',required=True,type=int)
    ap.add_argument('--out',required=True,type=Path)
    args = ap.parse_args()
    profile = [] if not args.profile else list(map(int,args.profile.split(',')))
    cert = build(profile,args.bound)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(cert,separators=(',',':'))+'\n')
    root = next(s for s in cert['states'] if s['key'] == cert['root'])
    print(json.dumps({'states':len(cert['states']),'root':root}))


if __name__ == '__main__':
    main()
