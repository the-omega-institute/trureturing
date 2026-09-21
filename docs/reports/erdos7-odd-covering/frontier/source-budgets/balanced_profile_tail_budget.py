#!/usr/bin/env python3
"""Exact directed continuation for a fixed original-label depth-profile law.

The certificate retains all 1,879 prime stages. Infinite auxiliary head tails
cover arbitrary finite original head-cofactor heights. The exponent-frontier
producer charges extra head labels under the same actual law. All required
checks remain active under Python -O. Ordinary analytic inputs are explicit.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import prod
from pathlib import Path
import sys
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json'
HEAD_CERTIFICATE = 'certificates/source_norms/source-budgets/balanced_profile_head.json'
SOURCES = ('certificate_io.py', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md', 'problem-details/04c-full-history-capped-laws-and-exact-global-optimization.md', 'problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Probability.lean', '../../../D5/S3/Arith/GoldenResourceOptimalInteger.lean', '../../../Library/Arith/schroeder2026noncoverage.md', '../../../Library/Arith/balister2018covering.md', 'frontier/source-budgets/balanced_profile_head_input.json', 'frontier/source-budgets/capped_head_bellman.py', 'frontier/source-budgets/balanced_profile_head.py', 'frontier/source-budgets/depth_cap_bellman.py', 'certificates/source_norms/source-budgets/balanced_profile_head.json', 'star_block/stoploss.py', 'star_block/base.py', 'verify_finite_continuation.py')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'readable source module')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def directed_calculation(base, record, bound=16384, geometric_lift=True):
    solver=load_module('depth_solver',base/'frontier/source-budgets/depth_cap_bellman.py')
    api=load_module('profile_stoploss',base/'star_block/stoploss.py')
    continuation=load_module('profile_continuation',base/'verify_finite_continuation.py')
    loader=load_module('balanced_head_input',base/'frontier/source-budgets/balanced_profile_head.py')
    io,data,labels=loader.load_head_input(base)
    primes,heights=data['prime_order'],data['heights']
    solver.require(record['profiles']==data['profiles'],'same actual depth profile')
    profiles=tuple(tuple(F(x) for x in row) for row in record['profiles'])
    problem=solver.HeadProblem(primes,heights,labels,profiles)
    epsilon=problem.optimum()
    solver.require(epsilon==F(record['epsilon_exact']),'exact head objective reproduced')
    allprimes=api.primes_to(bound)
    scale=10**18
    cap=(2*bound+1)//5
    weights=[0]*(cap+1);weights[1]=scale
    mean=second=scale
    ceil=api.stoploss_ceiling
    for p,h,profile in zip(primes,heights,profiles):
        tails=profile+(F(0),)
        atoms=[F(0)]+[tails[e]-tails[e+1] for e in range(h+1)]
        solver.require(sum(atoms)==1 and all(a>=0 for a in atoms),'finite auxiliary law')
        first=1+sum(profile[1:],F(0))
        square=1+sum(((2*e+1)*profile[e] for e in range(1,h+1)),F(0))
        if geometric_lift:
            # Retain the specified shallow tails and extend the last one by
            # independent uniform extra p-adic digits at any finite height.
            # The infinite auxiliary extension dominates every such lift.
            atoms=atoms[:h+1]
            rounded=[ceil(a.numerator*scale,a.denominator) for a in atoms]
            numerator=scale*profile[h].numerator*(p-1)
            denominator=profile[h].denominator*p
            for factor in range(h+1,cap+1):
                if denominator>=numerator:
                    rounded.extend([1]*(cap+1-factor))
                    break
                rounded.append(ceil(numerator,denominator))
                denominator*=p
            first+=profile[h]/(p-1)
            square+=profile[h]*(F(2*h+1,p-1)+F(2*p,(p-1)**2))
        else:
            rounded=[ceil(a.numerator*scale,a.denominator) for a in atoms]
        weights=api.stoploss_product_update(weights,rounded,scale)
        mean=ceil(mean*first.numerator,first.denominator)
        second=ceil(second*square.numerator,square.denominator)
    charge=0;steps=[]
    for q in allprimes:
        if q<=73:continue
        cutoff=(2*q+1)//5
        numerator=5*mean-(2*q+1)*scale
        numerator+=sum((2*q+1-5*d)*weights[d] for d in range(1,cutoff+1))
        step=ceil(numerator,3*(q-2))
        charge+=step;steps.append((q,step,charge))
        c=F(5*(q-1),3*(q-2))
        weights=api.stoploss_product_update(weights,api.stoploss_atom_bounds(q,c,cap,scale),scale)
        first=1+c/F(q-1)
        square=1+c*F(3*q-1,(q-1)**2)
        mean=ceil(mean*first.numerator,first.denominator)
        second=ceil(second*square.numerator,square.denominator)
    C=F(charge,scale);J=F(second,scale)
    require(len(allprimes)==1900 and continuation.stopping_threshold(1900)>=F(326059,4),'existing threshold supports fixed conservative bound')
    T=F(326059,4)
    solver.require(T>1,'positive threshold denominator')
    score=epsilon+C+(J-1)/(T-1)
    survival=1-epsilon-C
    return {'status':'CERTIFIED_STRICT_PASS' if score<1 else 'NOT_ESTABLISHED_BY_THIS_UPPER_BOUND',
            'B':bound,'global_prime_index':len(allprimes),'tail_stages':len(steps),
            'epsilon_exact':str(epsilon),'C_upper':str(C),'J_upper':str(J),'T_lower':str(T),
            'consumer_score_upper':str(score),'consumer_score_float':float(score),
            'survival_lower':str(survival),'Gamma_upper':str(1+(J-1)/survival) if survival>0 else None,
            'profiles':record['profiles'],'scale':scale,'geometric_lift':geometric_lift,
            'stages':[list(row) for row in steps],'step_digest':sha256(json.dumps(steps,separators=(',',':')).encode()).hexdigest(),
            'source_sha256':{name:sha256(io.read_artifact_bytes(base/name)).hexdigest() for name in SOURCES},
            'scope':('Fixed original 154-label head. Uniform extra head digits allow arbitrary finite exponents in every original tail cofactor; tail support and tail-prime exponents are unrestricted. ' if geometric_lift else 'Fixed original 154-label head. Full head heights bounded by this entire-family height vector; arbitrary original tail support and tail-prime exponents. ')+'Ordinary conditional comparison and BBMST continuation remain analytic inputs. No universal head-profile existence assertion.'}


def bind_certificate(base, io, source_bytes, path, producer, schema):
    raw = io.read_artifact_bytes(base/path)
    record = json.loads(raw, object_pairs_hook=io._unique)
    require(record['schema'] == schema, 'canonical certificate schema: '+path)
    producer_raw = io.read_artifact_bytes(base/producer)
    require(record['producer_sha256'] == sha256(producer_raw).hexdigest(), 'current producer: '+producer)
    source_bytes[path] = raw
    source_bytes[producer] = producer_raw
    for name, digest in record['source_sha256'].items():
        dep = io.read_artifact_bytes(base/name)
        require(sha256(dep).hexdigest() == digest, 'current dependency: '+name)
        require(name not in source_bytes or source_bytes[name] == dep, 'consistent dependency: '+name)
        source_bytes[name] = dep
    return record


def calculate(base):
    io=load_module('balanced_tail_io',base/'certificate_io.py')
    source_bytes={name:io.read_artifact_bytes(base/name) for name in SOURCES}
    head=bind_certificate(base,io,source_bytes,'certificates/source_norms/source-budgets/balanced_profile_head.json','frontier/source-budgets/balanced_profile_head.py','balanced-profile-head-v1')
    verified=bind_certificate(base,io,source_bytes,'certificates/source_norms/source-budgets/balanced_profile_head_verification.json','frontier/source-budgets/verify_balanced_profile_head.py','balanced-profile-head-verification-v1')
    require(head['profiles']==verified['profiles'] and head['epsilon_exact']==verified['epsilon_exact'],
            'same independently verified head law')
    result=directed_calculation(base,head)
    require(result['B']==16384 and result['global_prime_index']==1900 and result['tail_stages']==1879,
            'complete fixed tail interval')
    require(F(result['C_upper'])==F(130197276585546949,250000000000000000) and
            F(result['J_upper'])==F(617212231457700477699,62500000000000000), 'exact balanced tail upper bounds')
    require(result['step_digest']=='dfd3bef484092e31434e67a4d08bda65f48d7e36216c2b3ff3689d4210d433b3',
            'all1879 exact directed stages')
    require(F(result['consumer_score_upper'])<1 and F(result['Gamma_upper'])<F(326059,4),
            'strict balanced sufficient certificate')
    require(all(io.read_artifact_bytes(base/name)==raw for name,raw in source_bytes.items()),'tail sources unchanged')
    result.update(schema='balanced-profile-tail-budget-v1',
                  source_sha256={name:sha256(raw).hexdigest() for name,raw in source_bytes.items()},
                  producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io=load_module('balanced_output_io',args.base/'certificate_io.py')
    result=calculate(args.base)
    path=args.base/'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json'
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact canonical balanced-profile replay')
    print(json.dumps({key:result[key] for key in ('schema', 'C_upper', 'J_upper', 'T_lower', 'tail_stages', 'consumer_score_float')},indent=2))

if __name__=='__main__':
    main()
