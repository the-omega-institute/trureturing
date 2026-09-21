#!/usr/bin/env python3
"""Exact directed continuation for a fixed original-label depth-profile law.

The certificate retains all 1,879 prime stages. Infinite auxiliary head tails
cover arbitrary finite original head-cofactor heights. The cutoff corollary
charges extra high-power head labels under the same actual law. All required
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

CERTIFICATE = 'certificates/source_norms/source-budgets/depth_profile_tail_budget.json'
HEAD_CERTIFICATE = 'certificates/source_norms/source-budgets/depth_cap_bellman.json'
SOURCES = ('certificate_io.py', 'problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md', 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md', 'problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Probability.lean', '../../../D5/S3/Arith/GoldenResourceOptimalInteger.lean', '../../../Library/Arith/schroeder2026noncoverage.md', '../../../Library/Arith/balister2018covering.md', 'frontier/source-budgets/depth_profile_head_input.json', 'frontier/source-budgets/capped_head_bellman.py', 'frontier/source-budgets/depth_cap_bellman.py', 'certificates/source_norms/source-budgets/depth_cap_bellman.json', 'star_block/stoploss.py', 'star_block/base.py', 'verify_finite_continuation.py')


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
    io,data,labels=solver.load_head_input(base)
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
    T=continuation.stopping_threshold(len(allprimes))
    solver.require(T>1,'positive threshold denominator')
    score=epsilon+C+(J-1)/(T-1)
    survival=1-epsilon-C
    return {'status':'CERTIFIED_STRICT_PASS' if score<1 else 'NOT_ESTABLISHED_BY_THIS_UPPER_BOUND',
            'B':bound,'global_prime_index':len(allprimes),'tail_stages':len(steps),
            'epsilon_exact':str(epsilon),'C_upper':str(C),'J_upper':str(J),'T_lower':str(T),
            'consumer_score_upper':str(score),'consumer_score_float':float(score),
            'survival_lower':str(survival),'Gamma_upper':str(1+(J-1)/survival) if survival>0 else None,
            'profiles':record['profiles'],'scale':scale,'geometric_lift':geometric_lift,
            'stages':steps,'step_digest':sha256(json.dumps(steps,separators=(',',':')).encode()).hexdigest(),
            'source_sha256':{name:sha256(io.read_artifact_bytes(base/name)).hexdigest() for name in SOURCES},
            'scope':('Fixed original 154-label head. Uniform extra head digits allow arbitrary finite exponents in every original tail cofactor; tail support and tail-prime exponents are unrestricted. ' if geometric_lift else 'Fixed original 154-label head. Full head heights bounded by this entire-family height vector; arbitrary original tail support and tail-prime exponents. ')+'Ordinary conditional comparison and BBMST continuation remain analytic inputs. No universal head-profile existence assertion.'}


def cutoff_recovery(record, cutoff):
    require(type(cutoff) is int and cutoff >= max(record['heights']), 'cutoff contains the original head')
    profiles = tuple(tuple(F(r) for r in row) for row in record['profiles'])
    whole = prod(1+sum(r[1:],F(0))+r[-1]/(p-1)
                 for p,r in zip(record['prime_order'],profiles))
    truncated = prod(1+sum((r[e] if e <= h else r[h]/p**(e-h)
                            for e in range(1,cutoff+1)),F(0))
                     for p,h,r in zip(record['prime_order'],record['heights'],profiles))
    require(0 <= truncated <= whole, 'positive high-exponent union bound')
    return whole-truncated


def calculate(base):
    io = load_module('depth_budget_io', base/'certificate_io.py')
    record = json.loads(io.read_artifact_bytes(base/HEAD_CERTIFICATE), object_pairs_hook=io._unique)
    require(record['schema'] == 'depth-cap-bellman-v1', 'head certificate schema')
    require(record['producer_sha256'] == sha256((base/'frontier/source-budgets/depth_cap_bellman.py').read_bytes()).hexdigest(),
            'current head producer')
    for name,digest in record['source_sha256'].items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == digest,
                'current head source dependency: '+name)
    result = directed_calculation(base, record)
    require(result['geometric_lift'] and result['B'] == 16384 and
            result['global_prime_index'] == 1900 and result['tail_stages'] == 1879,
            'complete lifted continuation interval')
    epsilon,C,J = (F(result[name]) for name in ('epsilon_exact','C_upper','J_upper'))
    short = F(326059,4)
    require(F(result['T_lower']) >= short, 'certified stopping threshold dominates short bound')
    short_score = epsilon+C+(J-1)/(short-1)
    require(short_score < 1 and F(result['survival_lower']) > F(13299,100000)
            and F(result['Gamma_upper']) < 67250, 'strict baseline consumer inequalities')
    error = cutoff_recovery(record,5)
    survival = 1-epsilon-C-error
    score = short_score+error
    gamma = 1+(J-1)/survival
    require(epsilon < F(2,5) and C < F(47,100) and J < 9000 and error < F(7,400),
            'simple rational upper bounds for the high-head corollary')
    require(survival > F(9,80) and gamma < F(719929,9) < short and score < 1,
            'same-law high-head cutoff corollary')
    result.update(schema='depth-profile-tail-budget-v1',short_T_lower=str(short),
                  short_consumer_score_upper=str(short_score),
                  high_head_cutoff=dict(cutoff=5,union_loss_upper=str(error),
                                        survival_lower=str(survival),
                                        consumer_score_upper=str(score),Gamma_upper=str(gamma),
                                        simple_survival_lower='9/80',simple_Gamma_upper='719929/9',
                                        simple_threshold_margin=str(short-F(719929,9))),
                  producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    result['scope'] += ' Extra distinct 73-smooth head labels are also allowed when each contains a prime sixth power; their separate cutoff charge and surviving-mass bounds are included.'
    return json.loads(json.dumps(result))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    io = load_module('depth_profile_tail_io',args.base/'certificate_io.py')
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact complete-stage lifted continuation replay')
    print(json.dumps({k:v for k,v in result.items() if k != 'stages'},indent=2))


if __name__ == '__main__':
    main()
