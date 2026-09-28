#!/usr/bin/env python3
"""Independent exact checker; does not import or invoke the producer.

Checks every allowed Bellman branch, prime consecutiveness, upper bounds,
attainment, witness budgets, root cap and reachability of the complete DAG.
All decisions use integers or exact rational numbers, without floating point.
"""
import sys
sys.dont_write_bytecode = True

import argparse
from fractions import Fraction
import hashlib
import json
from math import gcd,isqrt
from pathlib import Path


def require(condition,message):
    if not condition:
        raise ValueError(message)


def integer(x,minimum=0):
    return type(x) is int and x >= minimum


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2,isqrt(n)+1))


def read_key(raw):
    require(type(raw) is list and len(raw) == 3,'malformed state key')
    i,b,h = raw
    require(integer(i) and integer(b,1) and integer(h),'invalid state parameters')
    return i,b,h


def read_value(raw):
    require(type(raw) is list and len(raw) == 2,'malformed rational')
    n,d = raw
    require(integer(n,1) and integer(d,1) and gcd(n,d) == 1,'noncanonical positive rational')
    return Fraction(n,d)


def check(cert):
    require(cert['schema'] == 'rough-max-bellman-v1','wrong schema')
    y,bound = cert['y'],cert['bound']
    require(integer(y,1) and integer(bound,1),'invalid root problem')
    primes = cert['primes']
    require(type(primes) is list and bool(primes),'empty prime prefix')
    previous = y
    for p in primes:
        require(integer(p,2) and p > previous,'invalid increasing prime prefix')
        require(trial_prime(p),'composite in prime prefix')
        require(not any(trial_prime(n) for n in range(previous+1,p)),
                'missing intermediate prime')
        previous = p
    height = 0
    while primes[0]**(height+1) <= bound:
        height += 1
    root = read_key(cert['root'])
    require(root == (0,bound,height),'incorrect root parameters')
    states = {}
    for state in cert['states']:
        key = read_key(state['key'])
        require(key not in states,'duplicate state')
        require(key[0] < len(primes),'state prime index out of range')
        states[key] = state
    require(root in states,'missing root state')
    require(len(primes) == max(k[0] for k in states)+1,'unused trailing primes')

    checked = {}
    edge_count = 0
    for key in sorted(states,reverse=True):
        i,budget,cap = key
        q = primes[i]
        state = states[key]
        value = read_value(state['value'])
        witness = state['witness']
        require(integer(witness,1) and witness <= budget,'witness exceeds budget')
        require(value >= 1,'value below empty suffix')
        # Independently enumerate the mathematically allowed branch set.
        expected = []
        a = 1
        while a <= cap and q**a <= budget:
            expected.append({'a':a,'power':q**a,
                             'child':[i+1,budget//(q**a),a]})
            a += 1
        require(state['branches'] == expected,'missing, extra, or altered branch')
        attained = value == 1 and witness == 1
        for branch in expected:
            child_key = tuple(branch['child'])
            require(child_key in checked,'missing or unverified child state')
            child_value,child_witness = checked[child_key]
            a,power = branch['a'],branch['power']
            # Different expression from producer: explicit divisor-sum factor.
            factor = sum((Fraction(1,q**j) for j in range(a+1)),Fraction(0))
            candidate = factor*child_value
            require(candidate <= value,'Bellman upper bound violated')
            if candidate == value and witness == power*child_witness:
                attained = True
            edge_count += 1
        require(attained,'claimed value has no attaining witness branch')
        checked[key] = value,witness

    reachable = set()
    pending = [root]
    while pending:
        key = pending.pop()
        if key in reachable:
            continue
        reachable.add(key)
        pending.extend(tuple(b['child']) for b in states[key]['branches'])
    require(reachable == set(states),'unreachable certificate states')
    value,witness = checked[root]
    return {'status':'PASS','y':y,'bound':bound,'value':[value.numerator,value.denominator],
            'witness':witness,'states':len(states),'branches':edge_count,
            'prime_prefix':primes,
            'scope':'Exact canonical recurrence checked; normalization to all y-rough integers is an external mathematical argument.'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('certificate',type=Path)
    ap.add_argument('--out',type=Path,required=True,help='JSON check report file')
    args = ap.parse_args()
    data = args.certificate.read_bytes()
    result = check(json.loads(data))
    result['certificate_sha256'] = hashlib.sha256(data).hexdigest()
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
