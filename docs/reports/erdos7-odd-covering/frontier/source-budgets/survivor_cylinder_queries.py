"""Complete history-relaxed survivor-cylinder queries on the unchanged attained head law."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,lcm,prod
from pathlib import Path
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
_spec=importlib.util.spec_from_file_location('survivor_cylinder_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/survivor_cylinder_queries.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md', 'problem-details/63-squared-load-stoploss-continuation.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'certificates/source_norms/source-budgets/adaptive_core7_policy.json', 'certificates/source_norms/source-budgets/adaptive_core7.json', 'frontier/source-budgets/adaptive_core7.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    policy=ctx.fresh('certificates/source_norms/source-budgets/adaptive_core7_policy.json','frontier/source-budgets/adaptive_core7.py')
    optimum=ctx.fresh('certificates/source_norms/source-budgets/adaptive_core7.json','frontier/source-budgets/adaptive_core7.py')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','locked complete literal input')
    require(sha256(ctx.raw('certificates/source_norms/source-budgets/adaptive_core7_policy.json')).hexdigest()==optimum['policy_sha256'],'same complete actual policy logical bytes')
    START=time.monotonic();SECONDS=120;LIMIT=2_000_000
    class Stop(Exception):
        pass
    def check_budget():
        if time.monotonic()-START>=SECONDS:
            raise Stop('120-second total wall budget')

    P,H=data['prime_order'],data['heights']
    R=[list(map(F,r)) for r in data['profiles']]
    mods=[m for m,a in data['labels']]


    @lru_cache(None)
    def price(n):
        v=F(1)
        for p,row in zip(P,R):
            e=0
            while n%p==0:
                e+=1
                n//=p
            v*=row[e]
        if n!=1:
            raise ValueError('complete selected head supports')
        return v


    unary=sum(map(price,mods),F(0))
    pair=sum((price(lcm(d,e)) for i,d in enumerate(mods) for e in mods[i+1:]),F(0))
    capacity=3*unary+2*pair
    capacity={"capacity_exact":str(capacity)}
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
    require(len(pure)==32 and len(order)==len(set(order))==4660,'preregistered complete query priority')

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

    completed=[]
    delta=F(0)
    settled_potential=F(0)
    status='complete'
    reason=None
    try:
        for m in order:
            check_budget()
            bound=F(value(root,m),den[127])
            require(h/m<=bound<=prices[m],'pigeonhole lower bound and deterministic product cap bound')
            bounded=min(prices[m],bound)
            credit=coeff[m]*(prices[m]-bounded)
            delta+=credit
            settled_potential+=potential[m]
            completed.append({'modulus':m,'coefficient':coeff[m],'price':str(prices[m]),'survivor_max_lower':str(h/m),'survivor_max_upper':str(bounded),'upper_to_price':str(bounded/prices[m]),'credit':str(credit),'credit_decimal':float(credit)})
    except Stop as error:
        status='resource-stop'
        reason=str(error)
    remaining_potential=total_potential-settled_potential
    result={'schema':'full-survivor-cylinder-relaxed-policy-query-v1','status':status,'stop_reason':reason,'scope':'Same full H and actual Chapter64 law; history-dependent residue choices relax each fixed cylinder; this is an upper bound on each survivor marginal maximum, not its exact maximum. Uncompleted queries receive zero deficit credit.','limits':{'wall_seconds':SECONDS,'nontrivial_query_states':LIMIT},'preparation':prep,'head_survival':str(h),'query_moduli':len(order),'completed_queries':len(completed),'query_states':query_states,'cached_states':len(memo),'calls':calls,'bin_terms':bin_terms,'delta_lower':str(delta),'delta_lower_decimal':float(delta),'remaining_potential':str(remaining_potential),'remaining_potential_decimal':float(remaining_potential),'method_ceiling_if_remaining_masses_zero':str(delta+remaining_potential),'method_ceiling_decimal':float(delta+remaining_potential),'absolute_E154_capacity':str(total_potential),'records':completed}
    require(result['status']=='complete' and result['completed_queries']==4660 and result['remaining_potential']=='0','complete canonical query certificate')
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
