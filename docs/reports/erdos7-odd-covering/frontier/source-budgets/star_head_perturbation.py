#!/usr/bin/env python3
"""Exact same-law stop for arbitrary 27-divisible or four-prime head classes.

The ordinary proof supplies conditional comparison and BBMST continuation.
All 1879 positive-part charges use the existing directed product-state API.
The two allowed head classes are alternatives, not their union.
"""
import argparse
from pathlib import Path
from fractions import Fraction as F
from math import prod, isqrt
import importlib.util
import json
import hashlib
import sys
sys.dont_write_bytecode = True

PROOF = 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md'
CERTIFICATE = 'certificates/source_norms/source-budgets/star_head_perturbation.json'
SOURCES = ('certificate_io.py', 'star_block/base.py', 'star_block/stoploss.py',
           'problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md',
           PROOF, '../../../Library/Arith/schroeder2026noncoverage.md',
           '../../../Library/Arith/balister2018covering.md')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None, 'Readable mathematical input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def calculate(base):
    api = module('perturbation_stoploss',base/'star_block/stoploss.py')
    S = 10**18
    B = 16384
    cap = (2*B+1)//5
    ps = [p for p in range(2, B+1)
          if all(p % d for d in range(2, isqrt(p)+1))]
    require(ps == api.primes_to(B), 'independent full prime list')
    require(len(ps) == 1900 and ps[-1] == 16381 and cap == 6553, 'stop parameters')
    w = [0]*(cap+1)
    w[1] = S
    mean = second = S
    charge = 0
    steps = []
    ceil = api.stoploss_ceiling

    for p in ps[1:]:
        if p <= 73:
            c = F(2) if p == 3 else F(p-1,p-3)
        else:
            cutoff = (2*p+1)//5
            require(cutoff <= cap, 'every query inside retained product states')
            n = 5*mean-(2*p+1)*S
            n += sum((2*p+1-5*d)*w[d] for d in range(1,cutoff+1))
            step = ceil(n,3*(p-2))
            charge += step
            steps.append((p,step,charge))
            c = F(5*(p-1),3*(p-2))
        w = api.stoploss_product_update(
            w, api.stoploss_atom_bounds(p,c,cap,S), S)
        f1 = 1+c/F(p-1)
        f2 = 1+c*F(3*p-1,(p-1)**2)
        mean = ceil(mean*f1.numerator,f1.denominator)
        second = ceil(second*f2.numerator,f2.denominator)

    C = F(charge,S)
    J = F(second,S)
    require(len(steps) == 1879 and steps[0][0] == 79 and steps[-1][0] == 16381,
            'all original tail-prime stages')
    require(C == F(55386439412229727,125000000000000000), 'root C reproduced')
    require(J == F(4344363876475156387651,500000000000000000), 'root J reproduced')

    log2 = 2*(F(1,3)+F(1,3)**3/3+F(1,3)**5/5)
    logk = 10*log2+2*(F(219,731)+F(219,731)**3/3)
    loglogk = 2*log2+2*(F(7,23)+F(7,23)**3/3)
    require(log2 == F(842,1215), 'three positive atanh terms at 2')
    require(logk == F(716376267476,94920147513) > F(377,50) > F(15,2),
            'log1900 lower')
    require(loglogk == F(29765348,14782905) > F(201,100), 'loglog1900 lower')
    bracket = F(377,50)+F(201,100)-3
    require(bracket == F(131,20) > 0, 'positive stopping bracket')
    T = 1900*bracket**2
    require(T == F(326059,4), 'short rational stopping threshold')
    epsilon = F(9,20)
    survival = 1-epsilon-C
    G = 1+(J-1)/survival
    require(survival > 0 and G < T, 'same-law strict continuation criterion')
    require(G == F(4343917330717507468743,53454242351081092), 'Gamma exact')
    require(T-G == F(3347967742569993841,13363560587770273), 'strict margin exact')

    coeff = [F(1),F(1)]
    product_other = F(1)
    for p in ps:
        if 5 <= p <= 73:
            product_other *= F(p-2,p-3)
            nxt = [F(0)]*(len(coeff)+1)
            for k,value in enumerate(coeff):
                nxt[k] += value
                nxt[k+1] += value/F(p-3)
            coeff = nxt
    budget27 = product_other/9
    budget4 = sum(coeff[4:],F(0))
    require(budget27 == F(27291063632391,67345087201280) < epsilon,
            'all head labels divisible by 27 fit')
    require(budget4 == F(288440010638780744436573,670918019074091909120000) < epsilon,
            'all head labels of support at least four fit')
    require(sum(coeff,F(0)) == 2*product_other, 'all support terms including non3')
    require(product_other/3 > epsilon and sum(coeff[3:],F(0)) > epsilon,
            'same envelopes do not certify the next shallower classes')
    for h in range(3,101):
        ternary = sum((2*F(1,3**e)/(1-F(1,3**h)) for e in range(3,h+1)),F(0))
        require(ternary == (F(1,9)-F(1,3**h))/(1-F(1,3**h)) <= F(1,9),
                'finite ternary high-exponent identity')
        require(sum((2*F(1,3**e)/(1-F(1,3**h)) for e in range(1,h+1)),F(0)) == 1,
                'finite ternary positive-support weight exactly one')


    def star35(i,j):
        if not j:
            return 3**(i-1)-1
        if not i:
            return 5**(j-1)-1
        return next(a for a in range(3**i*5**j)
                    if a % 3**i == 2*3**(i-1)-1
                    and a % 5**j == 2*5**(j-1)-1)


    def reserved(p,h):
        Fp = {x for x in range(p**h)
              if any(x % p**e == p**(e-1)-1 for e in range(1,h+1))}
        Cp = {x for x in range(p**h)
              if any(x % p**e == 2*p**(e-1)-1 for e in range(1,h+1))}
        return Cp,set(range(p**h))-Fp-Cp


    C3,_ = reserved(3,3)
    _,D5 = reserved(5,2)
    Q = 27*25
    R = {x for x in range(Q) if x % 27 in C3 and x % 25 in D5}
    head = {3**i*5**j:star35(i,j) for i in range(4) for j in range(3) if i+j}
    require(len(R) == 169 and len(head) == 11, 'actual depth-three fixture')
    require(all(all(x % d != a for d,a in head.items()) for x in R), 'reference branch')
    require(head[27] == 8 and head[15] == 1, 'original labelled residues')
    head[27] = 1
    bad = {x for x in R if any(x % d == a for d,a in head.items())}
    require(len(bad) == 13 and F(len(bad),len(R)) == F(1,13), 'actual changed27 bad mass')
    require((8-1) % 3 != 0 and (head[27]-head[15]) % 3 == 0,
            'disjoint original27/15 pair becomes intersecting')

    four = [3,5,7,11]
    Q4 = prod(four)
    R4 = {x for x in range(Q4) if x % 3 == 1
          and all(x % p not in (0,1) for p in four[1:])}
    new4 = next(x for x in R4 if all(x % p == 2 for p in four[1:]))
    head4 = {}
    for mask in range(1,1 << len(four)):
        support = [p for i,p in enumerate(four) if mask & (1 << i)]
        head4[prod(support)] = 1 if len(support) == 2 and 3 in support else 0
    require(len(head4) == 15 and len(R4) == 135 and Q4 == 1155 and new4 == 772,
            'literal four-support fixture')
    require(all(all(x % d != a for d,a in head4.items()) for x in R4), 'canonical avoidance')
    head4[Q4] = new4
    bad4 = {x for x in R4 if any(x % d == a for d,a in head4.items())}
    require(bad4 == {772} and Q4 % 27 != 0 and new4 % 3 != 0,
            'four-support change outside 27 class, actual probability 1/135')

    result = dict(result='PASS', scope='Ordinary comparison/BBMST inputs plus exact arithmetic.',
                  cutoff=B,last_prime=ps[-1],global_index=len(ps),tail_steps=len(steps),
                  retained_states=cap,max_query=(2*ps[-1]+1)//5,
                  C=str(C),J=str(J),epsilon=str(epsilon),survival=str(survival),
                  Gamma=str(G),stopping=str(T),margin=str(T-G),
                  budget27=str(budget27),budget_support4=str(budget4),
                  step_digest=hashlib.sha256(json.dumps(steps,separators=(',',':')).encode()).hexdigest(),
                  final_low_state_digest=hashlib.sha256(json.dumps(w,separators=(',',':')).encode()).hexdigest(),
                  fixture27=dict(period=Q,head_labels=len(head),source=len(R),bad=len(bad),
                                 old_residue=8,new_residue=1,probability='1/13'),
                  fixture_support4=dict(period=Q4,head_labels=len(head4),source=len(R4),bad=len(bad4),
                                        old_residue=0,new_residue=new4,probability='1/135'))
    result['schema'] = 'star-head-perturbation-v1'
    result['scope'] = 'Ordinary conditional comparison and BBMST continuation plus exact arithmetic. Any actual reference-head bad mass <=9/20 is paid once. Two separate original-head sufficient conditions allow all 27-divisible labels or all labels with at least four distinct primes to have arbitrary residues; all tail primes >73 are unrestricted. No assertion for the union of these two head classes or unrestricted Erdos7.'
    result['source_sha256'] = {p:hashlib.sha256((base/p).read_bytes()).hexdigest() for p in SOURCES}
    result['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    io = module('perturbation_io',args.base/'certificate_io.py')
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'Exact star-head perturbation certificate replay')
    print('PASS 1879 complete positive-part charges; one head-loss conditioning; both separate head budgets; two actual fixtures')
    print(json.dumps({k:result[k] for k in ('C','J','epsilon','Gamma','stopping','margin','budget27','budget_support4')},indent=2))


if __name__ == '__main__':
    main()
