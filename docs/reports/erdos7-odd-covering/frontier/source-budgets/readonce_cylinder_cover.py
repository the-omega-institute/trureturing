#!/usr/bin/env python3
"""Independent literal CRT and full-history audit of an atom-cap relaxation.

Only the standard library is used. Original events are evaluated as actual
integer congruences. No candidate solver, compressed label state or probe is
imported. All arithmetic and dual checks remain active under Python -O.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import permutations, product
from pathlib import Path
import json



def require(ok,message):
    if not ok:raise RuntimeError(message)


def fill(state,axis,x):
    return state[:axis]+(x,)+state[axis+1:]


def crt(state):
    return sum(x*(PERIOD//p)*pow(PERIOD//p,-1,p) for x,p in zip(state,PRIMES))%PERIOD


def bad(state):
    x=crt(state)
    return int(any(x%n==a for n,a in LABELS))


def calculate():
    points=tuple(product(*(range(p) for p in PRIMES)))
    require(len({crt(state) for state in points})==PERIOD,'actual full CRT bijection')
    require(all(all(crt(state)%p==x for p,x in zip(PRIMES,state)) for state in points),
            'actual coordinate reconstruction')
    require(len(LABELS)==len({n for n,_ in LABELS})==7 and
            all(n>1 and n%2 and PERIOD%n==0 and 0<=a<n for n,a in LABELS),
            'literal distinct original odd congruences')
    survivors=[x for x in range(PERIOD) if all(x%n!=a for n,a in LABELS)]
    require(len(survivors)==36,'actual original avoiding count')
    fibers={a:[x for x in survivors if x%3==a] for a in range(3)}
    require([len(fibers[a]) for a in range(3)]==[0,13,23],'actual ternary survivor fibers')
    uniform_marginals=[]
    for p,k in zip(PRIMES,KEEP):
        masses=[F(sum(x%p==a for x in survivors),len(survivors)) for a in range(p)]
        uniform_marginals.append(dict(prime=p,probabilities=list(map(str,masses)),
                                      allowed_marginal_cap=str(F(1,k)),
                                      violating_residues=[a for a,m in enumerate(masses) if m>F(1,k)]))
    require(F(1,len(survivors))<=F(1,30),'uniform avoiding law meets full-atom cap')
    require(F(23,36)>F(1,2),'uniform avoiding law already violates a marginal cap')

    fixed_results=[]
    fixed_roots=[]
    for order in permutations(range(3)):
        @lru_cache(None)
        def value(depth,state):
            if depth==3:return F(bad(state))
            axis=order[depth]
            costs=sorted(value(depth+1,fill(state,axis,x)) for x in range(PRIMES[axis]))
            return sum(costs[:KEEP[axis]],F(0))/KEEP[axis]
        answer=value(0,(-1,-1,-1))
        root=order[0]
        costs=[value(1,fill((-1,-1,-1),root,x)) for x in range(PRIMES[root])]
        require(answer==F(1,15),'every fixed order has bad mass one fifteenth')
        fixed_results.append(dict(order=[PRIMES[i] for i in order],bad_mass=str(answer),
                                  actual_history_states=value.cache_info().currsize,
                                  first_coordinate_costs=list(map(str,costs))))
        fixed_roots.append((root,costs))

    policy={}
    @lru_cache(None)
    def adaptive(state):
        if all(x>=0 for x in state):return F(bad(state))
        candidates=[]
        for axis,p in enumerate(PRIMES):
            if state[axis]>=0:continue
            rows=sorted((adaptive(fill(state,axis,x)),x) for x in range(p))
            chosen=tuple(x for _,x in rows[:KEEP[axis]])
            cost=sum((c for c,_ in rows[:KEEP[axis]]),F(0))/KEEP[axis]
            candidates.append((cost,axis,chosen))
        answer,axis,chosen=min(candidates)
        policy[state]=(axis,chosen)
        return answer
    optimum=adaptive((-1,-1,-1))
    require(optimum==F(1,15),'adaptive minimum matches every fixed order')
    adaptive_root_costs=[]
    for axis,p in enumerate(PRIMES):
        costs=[adaptive(fill((-1,-1,-1),axis,x)) for x in range(p)]
        require(all(fixed_costs==costs for root,fixed_costs in fixed_roots if root==axis),
                'both continuation orders attain the same conditional root values')
        adaptive_root_costs.append(dict(first_prime=p,costs=list(map(str,costs)),
                                        row_minimum=str(sum(sorted(costs)[:KEEP[axis]],F(0))/KEEP[axis])))
    require([row['costs'] for row in adaptive_root_costs]==
            [['1','2/15','0'],['1','1/2','1/5','0','0'],
             ['1','1/2','1/6','1/6','0','0','0']], 'complete exact root dual table')

    law=defaultdict(F);histories=[]
    def expand(state,mass,history):
        if all(x>=0 for x in state):
            law[state]+=mass;return
        axis,chosen=policy[state]
        histories.append((state,mass,history,axis,chosen))
        for x in chosen:
            expand(fill(state,axis,x),mass/KEEP[axis],history+((axis,x),))
    expand((-1,-1,-1),F(1),())
    require(len(law)==30 and set(law.values())=={F(1,30)} and sum(law.values())==1,
            'actual optimal thirty-point law')
    require(sum((mass*bad(state) for state,mass in law.items()),F(0))==optimum,
            'actual optimal original union payoff')
    rows=[];cap_checks=0
    def follows(state,history):
        partial=(-1,-1,-1)
        for axis,x in history:
            if policy[partial][0]!=axis or state[axis]!=x:return False
            partial=fill(partial,axis,x)
        return True
    for state,probability,history,axis,chosen in histories:
        branch={x:m for x,m in law.items() if follows(x,history)}
        require(sum(branch.values())==probability,'actual full-transcript probability')
        masses=[sum((m for x,m in branch.items() if x[axis]==a),F(0))/probability
                for a in range(PRIMES[axis])]
        require(masses==[F(1,KEEP[axis]) if a in chosen else F(0)
                         for a in range(PRIMES[axis])],'actual selected conditional row')
        for mass in masses:
            require(mass<=F(1,KEEP[axis]),'actual transcript conditional cap')
            cap_checks+=1
        rows.append(dict(transcript=[[PRIMES[i],x] for i,x in history],
                         transcript_probability=str(probability),next_prime=PRIMES[axis],
                         row=list(map(str,masses))))

    # Exact standard weak-dual cover: S is covered by its 13 X_3=1 atoms
    # and the entire X_3=2 cylinder. Every coefficient is one.
    atom_residues=fibers[1]
    for x in range(PERIOD):
        left=int(x in survivors)
        right=int(x%3==2)+sum(x==a for a in atom_residues)
        require(left<=right,'pointwise actual survivor-cylinder cover')
    dual=F(len(atom_residues),30)+F(1,2)
    require(dual==F(14,15) and 1-dual==optimum,'sharp schedule-independent weak dual')
    require(sum((m for x,m in law.items() if x[0]==2),F(0))==F(1,2),
            'optimal law saturates the ternary cylinder price')
    require(all(law[next(state for state in points if crt(state)==a)]==F(1,30)
                for a in atom_residues),'optimal law saturates all thirteen atom prices')
    # A short analytic attaining policy, independent of the DP tie choices.
    simple={}
    for x in (1,2):
        for y in ((2,3,4) if x==1 else (1,3,4)):
            for z in ((2,3,4,5,6) if x==1 else (1,2,3,4,5)):
                simple[(x,y,z)]=F(1,30)
    require(len(simple)==30 and sum(simple.values())==1,'simple normalized attaining law')
    simple_bad=sorted(crt(state) for state in simple if bad(state))
    require(simple_bad==[37,52] and F(len(simple_bad),30)==optimum,
            'simple attaining policy has exactly two actual bad CRT points')
    for depth,axis in enumerate((0,1,2)):
        conditional=defaultdict(lambda:defaultdict(F))
        for state,mass in simple.items():conditional[state[:depth]][state[axis]]+=mass
        for row in conditional.values():
            total=sum(row.values())
            require(all(mass<=total/KEEP[axis] for mass in row.values()),
                    'simple policy satisfies every actual conditional atom cap')
    return dict(schema='atom-cap-versus-readonce-105-v1',
                scope='Independent exact finite CRT/full-history calculation and sharp cylinder-cover weak dual. Full-atom caps alone admit a perfectly avoiding law; one ternary marginal cap already restores the exact bad-mass lower bound, so this is not evidence of a deeper conditional-only gap.',
                primes=PRIMES,keep=KEEP,labels=LABELS,period=PERIOD,
                actual_CRT_points_checked=len(points),actual_survivors=survivors,
                ternary_survivor_fibers=fibers,
                uniform_survivor_law=dict(support_count=len(survivors),each_atom_mass='1/36',
                                          allowed_full_atom_cap='1/30',bad_mass='0',
                                          coordinate_marginals=uniform_marginals),
                fixed_order_results=fixed_results,adaptive_bad_mass=str(optimum),
                adaptive_actual_history_states=adaptive.cache_info().currsize,
                adaptive_root_costs=adaptive_root_costs,
                optimal_readonce_law=dict(support=[dict(coordinates=x,CRT_residue=crt(x),
                                                        mass=str(m),bad=bool(bad(x)))
                                                   for x,m in sorted(law.items())],
                                         full_transcript_rows=rows,
                                         actual_conditional_caps_checked=cap_checks),
                simple_attaining_policy=dict(order=[3,5,7],first_values=[1,2],
                                             five_values_given_three={'1':[2,3,4],'2':[1,3,4]},
                                             seven_values_given_three={'1':[2,3,4,5,6],'2':[1,2,3,4,5]},
                                             each_full_atom_mass='1/30',bad_CRT_residues=simple_bad,
                                             CRT_support=sorted(crt(state) for state in simple)),
                dual=dict(full_atoms=atom_residues,each_full_atom_price='1/30',
                          additional_cylinder=dict(modulus=3,residue=2,price='1/2'),
                          pointwise_cover_checked_on_all=PERIOD,survival_upper=str(dual),
                          bad_mass_lower=str(1-dual),sharp_on_optimal_readonce_law=True),
                producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())


import argparse
import importlib.util
import sys
sys.dont_write_bytecode=True
SOURCES=('certificate_io.py', 'problem-details/56-exponent-frontiers-and-cylinder-cover-certificates.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'frontier/source-budgets/readonce_cylinder_cover_input105.json', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean', '../../../D5/S3/Arith/Congruence/ConditionalComparison/CappedGainRearrangement.lean', '../../../Library/Arith/schroeder2026noncoverage.md')

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'readable canonical module')
    value=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def certificate(base):
    global PRIMES,KEEP,LABELS,PERIOD
    io=load_module('cylinder_cover_input_io',base/'certificate_io.py')
    source_bytes={name:io.read_artifact_bytes(base/name) for name in SOURCES}
    data=json.loads(source_bytes['frontier/source-budgets/readonce_cylinder_cover_input105.json'],object_pairs_hook=io._unique)
    require(set(data)=={'schema','primes','keep','labels','period'} and
            data['schema']=='readonce-cylinder-cover-input-105-v1','unique literal105 input')
    require(data['primes']==[3,5,7] and data['keep']==[2,3,5] and data['period']==105,
            'actual coordinate dimensions and caps')
    require(all(type(x) is int for key in ('primes','keep') for x in data[key]) and
            type(data['period']) is int and
            all(len(row)==2 and all(type(x) is int for x in row) for row in data['labels']),
            'integer original data')
    digest=sha256(json.dumps(data['labels'],separators=(',',':')).encode()).hexdigest()
    require(digest=='3d7aae99c0b8ee232c5a299fb5907caab5cad42637199a97ac4cebfde6126f2a','same original seven congruence classes')

    PRIMES,KEEP,LABELS,PERIOD=tuple(data['primes']),tuple(data['keep']),tuple(map(tuple,data['labels'])),data['period']
    result=calculate()
    require(all(io.read_artifact_bytes(base/name)==value for name,value in source_bytes.items()),
            'actual source inputs unchanged')
    result.update(schema='readonce-cylinder-cover-v1',
                  original_label_source='frontier/source-budgets/readonce_cylinder_cover_input105.json',
                  original_labels_sha256=digest,
                  source_sha256={name:sha256(value).hexdigest() for name,value in source_bytes.items()})
    return json.loads(json.dumps(result))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io=load_module('canonical_result_io',args.base/'certificate_io.py')
    result=certificate(args.base)
    path=args.base/'certificates/source_norms/source-budgets/readonce_cylinder_cover.json'
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact canonical result replay')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
