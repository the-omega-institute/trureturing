#!/usr/bin/env python3
"""Independent exact checker; no import of the mandatory-core solver."""
from fractions import Fraction
from math import gcd,isqrt
import sys
sys.dont_write_bytecode = True

import argparse
import hashlib
import json
from pathlib import Path


def need(condition,reason):
    if not condition:
        raise ValueError(reason)


def integer(n,minimum=0):
    return type(n) is int and n >= minimum


def is_prime(n):
    return n >= 2 and all(n%d for d in range(2,isqrt(n)+1))


def key(raw):
    need(type(raw) is list and len(raw) == 3,'invalid state key')
    i,b,h = raw
    need(integer(i) and integer(b,1) and integer(h),'invalid state parameters')
    return i,b,h


def fraction(raw):
    need(type(raw) is list and len(raw) == 2,'invalid rational')
    n,d = raw
    need(integer(n,1) and integer(d,1) and gcd(n,d)==1,'invalid positive rational')
    return Fraction(n,d)


def check(cert):
    need(cert['schema']=='mandatory-core-bellman-v1','wrong schema')
    profile,bound,primes = cert['profile'],cert['bound'],cert['primes']
    need(type(profile) is list and all(integer(a,1) for a in profile),'invalid profile')
    need(all(a>=b for a,b in zip(profile,profile[1:])),'nonmonotone profile forbidden')
    need(integer(bound,1),'invalid bound')
    need(type(primes) is list and bool(primes),'empty prime list')
    previous = 1
    for p in primes:
        need(integer(p,2) and p > previous and is_prime(p),'invalid prime')
        need(not any(is_prime(n) for n in range(previous+1,p)),'skipped prime')
        previous = p
    r = len(profile)
    need(len(primes) >= r,'missing mandatory primes')
    suffix = [1]*(r+1)
    for i in reversed(range(r)):
        suffix[i] = primes[i]**profile[i]*suffix[i+1]
    need(cert['core_suffix'] == suffix and cert['core'] == suffix[0],'invalid core product')
    root = key(cert['root'])
    h = 0
    while 2**(h+1) <= bound:
        h += 1
    need(root == (0,bound,h),'incorrect root parameters')
    states = {}
    for state in cert['states']:
        k = key(state['key'])
        need(k not in states and k[0] < len(primes),'duplicate state or invalid prime index')
        states[k] = state
    need(root in states,'missing root')
    need(len(primes)==max(r,max(k[0] for k in states)+1),'extra prime entries')
    checked = {}
    pruned_branches = 0
    branches_total = 0
    for k in sorted(states,reverse=True):
        i,budget,cap = k
        state = states[k]
        lower = profile[i] if i<r else 0
        minimum_product = suffix[i] if i<r else 1
        if cap < lower or budget < minimum_product:
            reason = 'required-cap' if cap < lower else 'remaining-core-budget'
            need(state['value'] is None and state['witness'] is None,'infeasible state has a value')
            need(state['infeasible']==reason and state['branches']==[],'bad infeasibility proof')
            checked[k] = None,None
            continue
        need(state['infeasible'] is None,'false infeasibility claim')
        value = fraction(state['value'])
        witness = state['witness']
        need(integer(witness,1) and witness <= budget,'invalid witness budget')
        need(witness % minimum_product == 0,'witness misses remaining mandatory core')
        expected = []
        p = primes[i]
        a = max(1,lower)
        while a <= cap and p**a <= budget:
            power = p**a
            remainder_minimum = suffix[i+1] if i+1<r else 1
            # This is the exact integer test for the newly introduced pruning.
            if power*remainder_minimum > budget:
                expected.append({'a':a,'power':power,'pruned':'remaining-core-budget'})
            else:
                expected.append({'a':a,'power':power,'child':[i+1,budget//power,a]})
            a += 1
        need(state['branches']==expected,'missing, added, or wrongly pruned branch')
        attained = i>=r and value==1 and witness==1
        if i>=r:
            need(value>=1,'value below empty suffix')
        for branch in expected:
            branches_total += 1
            if 'pruned' in branch:
                pruned_branches += 1
                continue
            ck = tuple(branch['child'])
            need(ck in checked,'missing child')
            cv,cw = checked[ck]
            if cv is None:
                continue
            factor = sum((Fraction(1,p**j) for j in range(branch['a']+1)),Fraction(0))
            candidate = factor*cv
            need(candidate<=value,'Bellman upper bound violated')
            if candidate==value and witness==branch['power']*cw:
                attained = True
        need(attained,'value not attained by a legal branch')
        checked[k] = value,witness
    reachable = set()
    todo = [root]
    while todo:
        k = todo.pop()
        if k in reachable:
            continue
        reachable.add(k)
        todo.extend(tuple(b['child']) for b in states[k]['branches'] if 'child' in b)
    need(reachable==set(states),'unreachable certificate state')
    value,witness = checked[root]
    return {'status':'PASS','profile':profile,'bound':bound,'core':suffix[0],
            'maximum':None if value is None else [value.numerator,value.denominator],
            'witness':witness,'states':len(states),'branches':branches_total,
            'remaining_core_pruned_branches':pruned_branches,'prime_prefix':primes}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('certificate',type=Path)
    ap.add_argument('--out',type=Path,required=True,help='JSON check report file')
    args = ap.parse_args()
    raw = args.certificate.read_bytes()
    result = check(json.loads(raw))
    result['certificate_sha256'] = hashlib.sha256(raw).hexdigest()
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
