"""First9-prefix restricted queries refining the same full-H first3-root bounds."""
from collections import Counter, deque
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import gcd, lcm, prod
from pathlib import Path
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
_spec=importlib.util.spec_from_file_location('shared_root_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/shared_first9_prefix_queries.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/67-shared-root-prefix-bounds-for-the-actual-survivor-law.md', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'certificates/source_norms/source-budgets/adaptive_core7_policy.json', 'certificates/source_norms/source-budgets/adaptive_core7.json', 'frontier/source-budgets/adaptive_core7.py', 'certificates/source_norms/source-budgets/shared_first3_root_queries.json', 'frontier/source-budgets/shared_first3_root_queries.py', 'certificates/source_norms/source-budgets/survivor_cylinder_queries.json', 'frontier/source-budgets/survivor_cylinder_queries.py', 'certificates/source_norms/source-budgets/survivor_cylinder_literals.json', 'frontier/source-budgets/verify_survivor_cylinder_literals.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    policy=ctx.fresh('certificates/source_norms/source-budgets/adaptive_core7_policy.json','frontier/source-budgets/adaptive_core7.py')
    optimum=ctx.fresh('certificates/source_norms/source-budgets/adaptive_core7.json','frontier/source-budgets/adaptive_core7.py')
    old=ctx.fresh('certificates/source_norms/source-budgets/shared_first3_root_queries.json','frontier/source-budgets/shared_first3_root_queries.py')
    original_query=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_queries.json','frontier/source-budgets/survivor_cylinder_queries.py')
    literal=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_literals.json','frontier/source-budgets/verify_survivor_cylinder_literals.py')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','complete original literal input')
    require(sha256(ctx.raw('certificates/source_norms/source-budgets/adaptive_core7_policy.json')).hexdigest()==optimum['policy_sha256'],'complete canonical actual policy logical bytes')
    capacity={'capacity_exact':original_query['absolute_E154_capacity']}
    START=time.monotonic();SECONDS=120;LIMIT=2_000_000
    class Stop(Exception):pass
    def check_budget():
        if time.monotonic()-START>=SECONDS:raise Stop('120-second prefix-query budget')
    P,H,labels=data['prime_order'],data['heights'],data['labels']
    R=[list(map(F,row)) for row in data['profiles']]
    U=[r[-1].denominator for r in R]
    C=[r[-1].numerator for r in R]
    sizes=[p**e for p,e in zip(P,H)]
    den=[prod(U[7:])*prod(U[i] for i in range(7) if mask>>i&1) for mask in range(128)]
    support=[sum(1<<i for i,p in enumerate(P) if m%p==0) for m,a in labels]
    complete=[sum(1<<j for j,s in enumerate(support) if s<128 and not s&u) for u in range(128)]
    terminal_ids=[[j for j,s in enumerate(support) if s>>i&1] for i in range(7,20)]
    leaf_masks=[]
    for axis in range(7):
        factors=[gcd(m,sizes[axis]) for m,a in labels]
        leaf_masks.append([sum(1<<j for j,((m,a),f) in enumerate(zip(labels,factors)) if x%f==a%f) for x in range(sizes[axis])])

    # All children precede their parents; integer IDs avoid retaining huge masks
    # in the query cache. Absorbing covered children use ID -1 and value zero.
    states=[]
    index={}
    prep={'core_rows':0,'terminal_masks':0,'actual_core_leaves':0,'positive_actual_leaves':0,'positive_group_edges':0}
    for live,bad in policy['terminals']:
        active=int(live)
        allowed=[]
        for axis,ids in enumerate(terminal_ids,7):
            forbidden={labels[j][1]%P[axis] for j in ids if active>>j&1}
            allowed.append(min(U[axis],C[axis]*(P[axis]-len(forbidden))))
        survive=prod(allowed)
        require(survive==den[0]-int(bad),'complete actual terminal survival')
        index[0,active]=len(states)
        states.append({'u':0,'survival':survive,'allowed':tuple(allowed)})
        prep['terminal_masks']+=1
    for row in policy['policy']:
        u,active=row['remaining'],int(row['live'])
        axis=P.index(row['prime'])
        next_u=u^(1<<axis)
        remaining={int(child):mass for child,count,mass in row['branches']}
        multiplicities=Counter(active&mask for mask in leaf_masks[axis])
        branch_ids={}
        edges=[]
        for child,count,mass in row['branches']:
            child=int(child)
            require(multiplicities[child]==count and child!=0,'literal nonempty allocated group')
            child_id=-1 if child&complete[next_u] else index[next_u,child]
            branch_ids[child]=child_id
            edges.append((child_id,mass))
        actual=[]
        for x,mask in enumerate(leaf_masks[axis]):
            child=active&mask
            mass=min(C[axis],remaining.get(child,0))
            if mass:
                remaining[child]-=mass
                actual.append((x,mass,branch_ids[child]))
        require(not any(remaining.values()) and sum(mass for x,mass,child in actual)==U[axis],'all actual row mass assigned in increasing leaf order')
        survival=sum(mass*(states[child]['survival'] if child>=0 else 0) for child,mass in edges)
        require(survival==den[u]-int(row['numerator']),'actual surviving mass reconstructs retained row')
        index[u,active]=len(states)
        states.append({'u':u,'axis':axis,'survival':survival,'edges':tuple(edges),'actual':tuple(actual),'bins':{}})
        prep['core_rows']+=1
        prep['actual_core_leaves']+=sizes[axis]
        prep['positive_actual_leaves']+=len(actual)
        prep['positive_group_edges']+=len(edges)
        if len(states)%128==0:
            check_budget()
    root=index[127,(1<<154)-1]
    h=F(states[root]['survival'],den[127])
    require(h==1-F(policy['epsilon_exact']) and prep['core_rows']==6511 and prep['terminal_masks']==2542,'same complete survivor event and actual law')

    def price(m):
        result=F(1)
        for p,r in zip(P,R):
            exponent=0
            while m%p==0:
                m//=p
                exponent+=1
            result*=r[exponent]
        require(m==1,'query is an original-head divisor')
        return result
    moduli=[m for m,a in labels]
    coeff=Counter({m:3 for m in moduli})
    for i,d in enumerate(moduli):
        for e in moduli[i+1:]:
            coeff[lcm(d,e)]+=2
    prices={m:price(m) for m in coeff}
    potential={m:coeff[m]*prices[m] for m in coeff}
    total_potential=sum(potential.values(),F(0))
    require(total_potential==F(capacity['capacity_exact']) and len(coeff)==4660,'all E154 unary and pair prices')
    pure=sorted(m for m in moduli if sum(m%p==0 for p in P)==1)
    order=pure+sorted(set(coeff)-set(pure),key=lambda m:(-potential[m],m))
    require(len(pure)==32 and len(order)==len(set(order))==4660,'complete original query priority')

    memo={}
    query_states=0
    calls=0
    bin_terms=0
    def value(sid,m):
        nonlocal query_states,calls,bin_terms
        calls+=1
        if sid<0:
            return 0
        s=states[sid]
        if m==1:
            return s['survival']
        key=(sid,m)
        known=memo.get(key)
        if known is not None:
            return known
        if query_states>=LIMIT:
            raise Stop('2,000,000 nontrivial query-state budget')
        query_states+=1
        if query_states%1024==0:
            check_budget()
        if s['u']==0:
            factors=[]
            left=m
            for j,allowed in enumerate(s['allowed'],7):
                if left%P[j]==0:
                    left//=P[j]
                    factors.append(min(C[j],allowed))
                else:
                    factors.append(allowed)
            require(left==1,'only unread terminal query factors remain')
            answer=prod(factors)
        else:
            axis=s['axis']
            p=P[axis]
            if m%p:
                answer=sum(mass*value(child,m) for child,mass in s['edges'])
            else:
                power=1
                while m%p==0:
                    m//=p
                    power*=p
                if power not in s['bins']:
                    bins=[Counter() for _ in range(power)]
                    for x,mass,child in s['actual']:
                        if child>=0:
                            bins[x%power][child]+=mass
                    s['bins'][power]=tuple(tuple(b.items()) for b in bins)
                child_values={child:value(child,m) for child,mass in s['edges'] if child>=0}
                bins=s['bins'][power]
                answer=max((sum(mass*child_values[child] for child,mass in b) for b in bins),default=0)
                bin_terms+=sum(map(len,bins))
        require(0<=answer<=s['survival'],'relaxed query remains a subevent of full survival')
        memo[key]=answer
        return answer

    old_by={r['modulus']:list(map(F,r['restricted_upper'])) for r in old['records']}
    exact={r['modulus']:list(map(F,r['all_residue_masses'])) for r in literal['records']}
    require(states[root]['axis']==0 and P[0]==3,'actual policy starts with3')
    records=[]
    for m in sorted(x for x in coeff if x%9==0):
        check_budget();oldnum=value(root,m);left=m;power=1
        while left%3==0:left//=3;power*=3
        children={child:value(child,left) for child,mass in states[root]['edges'] if child>=0}
        bins=[sum(mass*children[child] for child,mass in b) for b in states[root]['bins'][power]]
        upper=[F(max(bins[r::9]),den[127]) for r in range(9)]
        require(all(upper[r]==0 for r in (0,3,4,6)),'first3 and pure9 forbidden prefixes have zero H mass')
        if m in exact:
            for r in range(9):
                actual=max(exact[m][r::9]);require(actual<=upper[r],'literal exact prefix bound');upper[r]=actual
        require([max(upper[r::3]) for r in range(3)]==old_by[m],'aggregates to old shared-root queries')
        records.append({'modulus':m,'restricted_upper':[str(x) for x in upper],'uses_exact_literal':m in exact})
    out={'schema':'actual64-first9-prefix-restricted-query-v1','status':'PASS','records':records,'queries':len(records),'states':query_states,'head_survival':str(h),'scope':'Same actual full survivor law, first9 prefix shared; later digits/coordinates remain history-relaxed. Aggregates exactly to first3-root query bounds.'}
    require(len(records)==1337 and [r['modulus'] for r in records if r['uses_exact_literal']]==[9],'all affected prefix queries and the one exact literal replacement')
    return ctx.finish(out)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
