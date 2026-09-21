#!/usr/bin/env python3
"""Adaptive read-once original-label Bellman optimization and a literal witness.

The general optimizer uses complete p-adic laminar caps. The retained 315
witness reconstructs flat-cap rows only after exact profile validation.
All checks remain active under Python -O; no search trajectory is required.
"""
import argparse
import importlib.util
import json
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import permutations
from math import prod
from pathlib import Path
import sys
sys.dont_write_bytecode=True

INPUT='frontier/source-budgets/adaptive_head_input_315.json'
CERTIFICATE='certificates/source_norms/source-budgets/adaptive_head_bellman.json'
SOURCES=('certificate_io.py', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md', 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md', 'problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md', 'frontier/source-budgets/adaptive_head_input_315.json', 'frontier/source-budgets/depth_cap_bellman.py', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean', '../../../D5/S3/Arith/Congruence/ConditionalComparison/CappedGainRearrangement.lean', '../../../Library/Arith/schroeder2026noncoverage.md', '../../../Library/Arith/balister2018covering.md')


def require(ok,message):
    if not ok:
        raise ValueError(message)


def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'readable canonical module')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def adaptive(problem, retain=False):
    axes=tuple(range(len(problem.primes)))
    choices={}

    @lru_cache(None)
    def value(remaining,active):
        if not active:return F(0)
        if any(all(problem.rows[j][i][0]==0 for i in remaining) for j in active):return F(1)
        best=None;selected=None
        for axis in remaining:
            rest=tuple(i for i in remaining if i!=axis)
            cost,_=s.compressed_row(problem.primes[axis],problem.heights[axis],problem.profiles[axis],
                                     problem.by_axis[axis],active,lambda hits:value(rest,hits))
            if best is None or cost<best:best=cost;selected=axis
        choices[(remaining,active)]=selected
        return best

    result=value(axes,tuple(range(len(problem.labels))))
    return result,choices,value


def calculate(base):
    global s
    io=load_module('adaptive_head_io',base/'certificate_io.py')
    s=load_module('adaptive_head_depth_solver',base/'frontier/source-budgets/depth_cap_bellman.py')
    data=json.loads(io.read_artifact_bytes(base/INPUT),object_pairs_hook=io._unique)
    require(set(data)=={'schema','primes','heights','ks','labels','profiles'} and
            data['schema']=='adaptive-head-input-315-v1','exact literal input fields')
    require(data['primes']==[3,5,7] and data['heights']==[2,1,1] and data['ks']==[4,3,5],
            'literal 315 coordinate inventory and flat atom caps')
    require([n for n,_ in data['labels']]==[n for n in range(2,316) if 315%n==0],
            'all eleven original nonunit divisors of 315')
    profiles=tuple(tuple(F(r) for r in row) for row in data['profiles'])
    expected=tuple(s.flat_profile(p,h,F(1,k)) for p,h,k in
                   zip(data['primes'],data['heights'],data['ks']))
    require(profiles==expected,'flat reconstruction requires every depth cap to match the leaf cap')
    problem=s.HeadProblem(data['primes'],data['heights'],data['labels'],profiles)
    optimal,choices,value=adaptive(problem)
    fixed=[]
    for order in permutations(range(3)):
        other=s.HeadProblem([problem.primes[i] for i in order],
                            [problem.heights[i] for i in order],problem.labels,
                            [problem.profiles[i] for i in order])
        fixed.append({'order':[problem.primes[i] for i in order],'value':str(other.optimum())})
    require(optimal==0 and min(F(row['value']) for row in fixed)==F(1,60),
            'actual adaptive zero versus all strictly positive fixed orders')
    ks=data['ks'];axes=tuple(range(3));rows=[];law={}


    def visit(remaining,active,history,coordinates,mass):
        if not remaining:
            point=tuple(coordinates)
            s.require(point not in law,'one decision path per full tuple')
            law[point]=mass
            return
        axis=choices.get((remaining,active),remaining[0])
        rest=tuple(i for i in remaining if i!=axis)
        p=problem.primes[axis];N=p**problem.heights[axis]
        child=[]
        for a in range(N):
            hits=tuple(j for j in active if a%(p**problem.rows[j][axis][0])==problem.rows[j][axis][1])
            child.append((value(rest,hits),a,hits))
        child.sort();chosen=child[:ks[axis]]
        expected=sum((cost for cost,_,_ in chosen),F(0))/ks[axis]
        s.require(expected==value(remaining,active),'actual selected row realizes adaptive value')
        rows.append({'history':history,'next_prime':p,'selected_residues':[a for _,a,_ in chosen],'each_probability':str(F(1,ks[axis]))})
        for _,a,hits in chosen:
            updated=list(coordinates);updated[axis]=a
            visit(rest,hits,history+[[p,a]],updated,mass/ks[axis])


    visit(axes,tuple(range(len(problem.labels))),[],[None]*3,F(1))
    s.require(len(law)==60 and set(law.values())=={F(1,60)},'actual 60 equal-mass full tuples')
    integers=[]
    for point in law:
        integer=next(x for x in range(315) if all(x%(p**h)==a for p,h,a in zip(problem.primes,problem.heights,point)))
        s.require(all(integer%n!=a%n for n,a in problem.labels),'every actual integer avoids every original label')
        integers.append(integer)
    s.require(len(set(integers))==60,'unique CRT support')
    violations=[]
    for order in permutations(axes):
        found=None
        for index,axis in enumerate(order):
            conditional=defaultdict(lambda:defaultdict(F))
            for point,mass in law.items():conditional[tuple(point[j] for j in order[:index])][point[axis]]+=mass
            for prefix,distribution in sorted(conditional.items()):
                total=sum(distribution.values())
                for a,mass in sorted(distribution.items()):
                    if mass*ks[axis]>total:
                        found={'order':[problem.primes[j] for j in order],'prefix':prefix,'prime':problem.primes[axis],
                               'residue':a,'conditional_probability':str(mass/total),'allowed_atom_cap':str(F(1,ks[axis]))}
                        break
                if found:break
            if found:break
        s.require(found is not None,'adaptive witness lies outside each fixed-order capped class')
        violations.append(found)

    record={'status':'PASS','adaptive_value':str(optimal),'law_mass':str(sum(law.values())),
            'crt_support':sorted(integers),'each_point_mass':'1/60','rows':rows,
            'fixed_order_cap_violations':violations}

    require(sum(law.values())==1,'actual joint law normalized')
    record.update(schema='adaptive-head-bellman-v1',
                  scope='Exact literal 315 strict separation and complete adaptive read-once law under unchanged flat caps. General adaptive Bellman rows use laminar caps. Original labels remain fixed; numerical tail transfer is ordinary mathematics. The 154-label joint atom-cap obstruction remains valid.',
                  primes=data['primes'],heights=data['heights'],ks=data['ks'],profiles=data['profiles'],
                  original_label_count=len(problem.labels),original_period=problem.period,
                  original_label_source=INPUT,
                  original_labels_sha256=sha256(json.dumps(data['labels'],separators=(',',':')).encode()).hexdigest(),
                  fixed_values=fixed,fixed_minimum=str(min(F(row['value']) for row in fixed)),
                  adaptive_states=value.cache_info().currsize,
                  source_sha256={name:sha256(io.read_artifact_bytes(base/name)).hexdigest() for name in SOURCES},
                  producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    return json.loads(json.dumps(record))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io=load_module('adaptive_output_io',args.base/'certificate_io.py')
    result=calculate(args.base)
    path=args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact adaptive head complete-law replay')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
