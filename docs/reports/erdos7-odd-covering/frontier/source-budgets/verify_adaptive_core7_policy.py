"""Actual-leaf reconstruction of every positive policy row and absolute depth cylinder."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,isqrt,lcm,prod
from pathlib import Path
import argparse
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('adaptive_core_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/adaptive_core7_policy_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md', 'problem-details/63-squared-load-stoploss-continuation.md', 'certificates/source_norms/source-budgets/adaptive_core7_policy.json', 'certificates/source_norms/source-budgets/adaptive_core7_verification.json', 'frontier/source-budgets/adaptive_core7.py', 'frontier/source-budgets/verify_adaptive_core7.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','same complete literal source')
    policy=ctx.fresh('certificates/source_norms/source-budgets/adaptive_core7_policy.json','frontier/source-budgets/adaptive_core7.py')
    independent=ctx.fresh('certificates/source_norms/source-budgets/adaptive_core7_verification.json','frontier/source-budgets/verify_adaptive_core7.py')
    P,H,labels=data['prime_order'],data['heights'],data['labels']
    R=[list(map(F,r)) for r in data['profiles']]
    units=[r[-1].denominator for r in R]
    cap=[r[-1].numerator for r in R]
    sizes=[p**h for p,h in zip(P,H)]
    den=[prod(units[7:])*prod(units[i] for i in range(7) if u>>i&1) for u in range(128)]
    support=[sum(1<<i for i,p in enumerate(P) if m%p==0) for m,a in labels]
    complete=[sum(1<<j for j,s in enumerate(support) if s<128 and not s&u) for u in range(128)]
    terminal_ids=[[j for j,s in enumerate(support) if s>>i&1] for i in range(7,20)]
    leaf_masks=[]
    for i in range(7):
        factors=[gcd(m,sizes[i]) for m,a in labels]
        leaf_masks.append([sum(1<<j for j,((m,a),factor) in enumerate(zip(labels,factors)) if x%factor==a%factor)
                           for x in range(sizes[i])])
    values={}
    counts={'core_rows':0,'core_actual_leaves':0,'core_positive_actual_leaf_edges':0,
            'proper_and_leaf_cylinder_checks':0,'terminal_masks':0,'terminal_coordinate_rows':0,
            'terminal_actual_atoms':0,'positive_group_edges':0,'absorbing_edges':0}

    def check_row(axis,masses):
        require(len(masses)==sizes[axis] and sum(masses)==units[axis] and all(type(m) is int and 0<=m<=cap[axis] for m in masses),'normalized actual row within every leaf cap')
        for e in range(1,H[axis]+1):
            modulus=P[axis]**e
            bins=[0]*modulus
            for x,mass in enumerate(masses):
                bins[x%modulus]+=mass
            allowed=R[axis][e]*units[axis]
            require(allowed.denominator==1 and all(v<=allowed.numerator for v in bins),'each actual absolute depth cylinder satisfies its cap')
            counts['proper_and_leaf_cylinder_checks']+=len(bins)

    terminal_set=set()
    for live,claimed in policy['terminals']:
        active=int(live)
        require(active not in terminal_set and active>0 and not active&complete[0],'unique unresolved terminal mask')
        terminal_set.add(active)
        survival=1
        for axis,ids in enumerate(terminal_ids,7):
            forbidden={labels[j][1]%P[axis] for j in ids if active>>j&1}
            # Build the actual named residues, independent of the producer formula.
            ordered=[x for x in range(P[axis]) if x not in forbidden]+[x for x in range(P[axis]) if x in forbidden]
            masses=[0]*P[axis]
            remaining=units[axis]
            for x in ordered:
                masses[x]=min(remaining,cap[axis])
                remaining-=masses[x]
            require(remaining==0,'all terminal probability assigned')
            check_row(axis,masses)
            allowed=sum(masses[x] for x in range(P[axis]) if x not in forbidden)
            require(allowed==min(units[axis],cap[axis]*(P[axis]-len(forbidden))),'actual terminal allowed-first law attains claimed factor')
            survival*=allowed
            counts['terminal_coordinate_rows']+=1
            counts['terminal_actual_atoms']+=len(masses)
        bad=den[0]-survival
        require(bad==int(claimed),'each terminal continuation value independently attained')
        values[0,active]=bad
        counts['terminal_masks']+=1

    def get_value(u,active):
        if active&complete[u]:
            return den[u]
        if not active:
            return 0
        require((u,active) in values,'positive child continuation already reconstructed')
        return values[u,active]

    rows={}
    edges={}
    by_depth=[Counter() for _ in range(7)]
    last=None
    for record in policy['policy']:
        u,active=record['remaining'],int(record['live'])
        key=(u,active)
        require(last is None or last<key,'strict unique topological policy order')
        last=key
        require(0<u<128 and active>0 and not active&complete[u],'unresolved core boundary')
        axis=P.index(record['prime'])
        require(axis<7 and u>>axis&1 and record['mass_units']==units[axis],'selected unread original core coordinate')
        next_u=u^(1<<axis)
        actual_groups=defaultdict(list)
        for x,mask in enumerate(leaf_masks[axis]):
            actual_groups[active&mask].append(x)
        masses=[0]*sizes[axis]
        seen=set()
        total=0
        children=[]
        for live,multiplicity,allocated in record['branches']:
            child=int(live)
            require(child not in seen and child in actual_groups,'distinct existing actual leaf group')
            seen.add(child)
            require(multiplicity==len(actual_groups[child]) and type(allocated) is int and 0<allocated<=multiplicity*cap[axis],'literal group multiplicity and positive feasible mass')
            remaining=allocated
            for x in actual_groups[child]:
                masses[x]=min(remaining,cap[axis])
                remaining-=masses[x]
            require(remaining==0,'group allocation split over actual leaves in increasing order')
            child_value=get_value(next_u,child)
            total+=allocated*child_value
            children.append((next_u,child))
            counts['positive_group_edges']+=1
            if child&complete[next_u]:
                counts['absorbing_edges']+=1
        check_row(axis,masses)
        require(total==int(record['numerator']) and 0<=total<=den[u],'actual chosen row attains its recorded complete continuation value')
        values[key]=total
        rows[key]=record
        edges[key]=children
        by_depth[7-u.bit_count()][str(P[axis])]+=1
        counts['core_rows']+=1
        counts['core_actual_leaves']+=len(masses)
        counts['core_positive_actual_leaf_edges']+=sum(m>0 for m in masses)

    root=(127,(1<<154)-1)
    pending=[root]
    visited=set()
    while pending:
        key=pending.pop()
        u,active=key
        if active&complete[u] or not active or key in visited:
            continue
        visited.add(key)
        if u:
            require(key in edges,'every positive reachable boundary has a legal row')
            pending.extend(edges[key])
        else:
            require(active in terminal_set,'every positive terminal mask present')
    require(visited==set(rows)|{(0,a) for a in terminal_set},'all and only positive reachable policy states retained')
    epsilon=F(values[root],den[127])
    require(str(epsilon)==policy['epsilon_exact']==independent['epsilon_exact'],'actual reconstructed law attains independently optimized root')
    require(counts['core_rows']==policy['boundary_states']==6511 and counts['terminal_masks']==policy['terminal_states']==2542,'complete positive policy state counts')
    require(counts['positive_group_edges']==policy['positive_group_edges']==18796 and counts['absorbing_edges']==policy['absorbing_edges']==1291,'complete positive edge counts')
    require([dict(c) for c in by_depth]==policy['selected_coordinate_counts_by_depth'],'selected original coordinates at every depth')
    result={'schema':'adaptive-core7-actual-policy-verification-v1','status':'PASS','epsilon_exact':str(epsilon),'counts':counts,'full_coordinate_and_absolute_depth_caps':True,'positive_DAG_complete':True,'candidate_Bellman_values_consumed':False,'DP_recomputations':0}
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
