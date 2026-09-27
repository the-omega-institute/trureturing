#!/usr/bin/env python3
"""Exact original-label survivor DP and chordal overlap controls.

Standard-library arithmetic for report 433. Finite checks are not Lean
certification and do not establish positivity for arbitrary odd moduli.
"""

from fractions import Fraction as F
from itertools import combinations
from math import gcd,lcm
from functools import lru_cache
import json

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def chordal_peo(vertices, edges):
    remaining=set(vertices); order=[]
    while remaining:
        v=next((v for v in sorted(remaining) if all(tuple(sorted((a,b))) in edges for a,b in combinations([u for u in remaining if tuple(sorted((u,v))) in edges],2))),None)
        if v is None: return None
        order.append(v); remaining.remove(v)
    return order

def cliques(vertices,edges):
    for k in range(1,len(vertices)+1):
        found=False
        for c in combinations(vertices,k):
            if all(tuple(sorted(e)) in edges for e in combinations(c,2)):
                found=True
                yield c
        if not found:break

def bound(vertices,edges):
    return F(1)+sum(((-1)**len(c)*F(1,lcm(*c)) for c in cliques(vertices,edges)),F())

def peo_bound(vertices,edges,peo):
    total=F()
    for i,v in enumerate(peo):
        term=F(1,v)
        for u in peo[i+1:]:
            if tuple(sorted((u,v))) in edges: term*=1-F(1,u)
        total+=term
    return 1-total

def exact_dp(moduli, residues, start_d=1, verify_reachable=False):
    n=len(moduli)
    adj=[sum(1<<j for j in range(n) if j!=i and (residues[i]-residues[j])%gcd(moduli[i],moduli[j])==0) for i in range(n)]
    @lru_cache(None)
    def dp(mask,d):
        if not mask:return F(1,d)
        i=(mask&-mask).bit_length()-1; rest=mask&~(1<<i)
        return dp(rest,d)-dp(rest&adj[i],lcm(d,moduli[i]))
    value=dp((1<<n)-1,start_d)
    checked_histories=set()
    if verify_reachable:
        require(start_d==1, 'Physical history verification starts with empty history')
        period=lcm(*moduli)
        def check(mask,selected):
            key=(mask,selected)
            if key in checked_histories:return
            checked_histories.add(key)
            active=[j for j in range(n) if mask>>j&1]
            d=lcm(*(moduli[j] for j in selected))
            require(all(adj[i]>>j&1 for i,j in combinations(selected,2)), 'Selected history is a compatible clique')
            require(all(adj[i]>>j&1 for i in selected for j in active), 'Remaining vertices share the selected compatible history')
            physical=F(sum(all(x%moduli[j]==residues[j] for j in selected) and all(x%moduli[j]!=residues[j] for j in active) for x in range(period)),period)
            require(dp(mask,d)==physical, 'Reachable DP state equals its exact physical residual mass')
            require(dp(mask,d)>=0, 'Reachable DP state has nonnegative mass')
            if mask:
                i=(mask&-mask).bit_length()-1;rest=mask&~(1<<i)
                check(rest,selected)
                check(rest&adj[i],selected+(i,))
        check((1<<n)-1,())
    return value,dp.cache_info().currsize,len(checked_histories)

def maximum_coprime_forest(vertices):
    parent={m:m for m in vertices}
    def find(x):
        while parent[x]!=x:x=parent[x]
        return x
    edges=[]
    for a,b in sorted((e for e in combinations(vertices,2) if gcd(*e)==1),key=lambda e:F(1,e[0]*e[1]),reverse=True):
        ra,rb=find(a),find(b)
        if ra!=rb:parent[ra]=rb;edges.append((a,b))
    return edges

def main():
    m605=[5,11,55,121,605];r605=[0,0,1,2,3]
    e605={(5,11),(5,121)}
    s605=sum((F(1,m) for m in m605),F())
    f605=1-s605+sum((F(1,lcm(*e)) for e in e605),F())
    count605=sum(all(x%m!=r for m,r in zip(m605,r605)) for x in range(605))
    dp605,states605,physical_states605=exact_dp(m605,r605,verify_reachable=True)
    negative_dp,negative_states,_=exact_dp([3,9],[0,1],start_d=9)
    require(negative_dp==F(-1,9), "Unreachable arbitrary DP state has value -1/9")
    require(f605==dp605==F(count605,605)==F(424,605), 'f605==dp605==F(count605,605)==F(424,605)')

    m945=[m for m in range(2,946) if 945%m==0]
    user_forest={tuple(sorted(e)) for e in [(3,5),(3,7),(3,35),(5,9),(5,21),(5,27),(5,63),(5,189),(7,15),(7,45),(7,135)]}
    require(all(gcd(*e)==1 for e in user_forest), 'all(gcd(*e)==1 for e in user_forest)')
    require(chordal_peo(m945,user_forest), 'chordal_peo(m945,user_forest)')
    require(len(user_forest)==11, 'len(user_forest)==11')
    require(all(len(c)<=2 for c in cliques(m945,user_forest)), 'all(len(c)<=2 for c in cliques(m945,user_forest))')
    require(bound(m945,user_forest)==F(141,945), 'bound(m945,user_forest)==F(141,945)')
    optimal_forest945=maximum_coprime_forest(m945)
    require(bound(m945,set(optimal_forest945))==F(141,945), 'bound(m945,set(optimal_forest945))==F(141,945)')
    core=[3,5,7,9,27,35]
    core_edges=[e for e in combinations(core,2) if gcd(*e)==1]
    forced={e for e in combinations(m945,2) if gcd(*e)==1}
    bridges=forced-set(core_edges)
    require(bridges=={(5,21),(5,63),(5,189),(7,15),(7,45),(7,135)}, 'bridges=={(5,21),(5,63),(5,189),(7,15),(7,45),(7,135)}')
    require(len(core_edges)==10, 'len(core_edges)==10')
    best=None; optimizers=[]; chordal_count=0; tested_active=0
    for mask in range(1<<len(core_edges)):
        edges={e for i,e in enumerate(core_edges) if mask>>i&1}
        peo=chordal_peo(core,edges)
        if peo is None:continue
        chordal_count+=1
        # Check the clique Euler characteristic on every active core subset.
        for amask in range(1<<len(core)):
            active=[v for i,v in enumerate(core) if amask>>i&1]
            unseen=set(active);components=0
            while unseen:
                components+=1;stack=[unseen.pop()]
                while stack:
                    v=stack.pop();new={u for u in unseen if tuple(sorted((u,v))) in edges}
                    unseen-=new;stack.extend(new)
            chi=sum((-1)**(len(c)+1) for c in cliques(active,edges))
            require(chi==components, 'chi==components')
            tested_active+=1
        full=edges|bridges;value=bound(m945,full)
        full_peo=chordal_peo(m945,full)
        require(full_peo is not None, 'full_peo is not None')
        require(peo_bound(m945,full,full_peo)==value, 'peo_bound(m945,full,full_peo)==value')
        if best is None or value>best:best=value;optimizers=[(sorted(edges),full_peo)]
        elif value==best:optimizers.append((sorted(edges),full_peo))
    require(best==F(175,945), 'best==F(175,945)')
    # A realizable warning against substituting arbitrary cyclic H in the component identity.
    c4=[3,9,27,81];cycle={(3,9),(9,27),(27,81),(3,81)}
    require(chordal_peo(c4,cycle) is None, 'chordal_peo(c4,cycle) is None')
    require(sum((-1)**(len(c)+1) for c in cliques(c4,cycle))==0, 'sum((-1)**(len(c)+1) for c in cliques(c4,cycle))==0')
    require(all(0%m==0 for m in c4), 'all(0%m==0 for m in c4)')
    require(bound(c4,cycle)==F(55,81), 'bound(c4,cycle)==F(55,81)')
    require(F(sum(all(x%m for m in c4) for x in range(81)),81)==F(54,81), 'F(sum(all(x%m for m in c4) for x in range(81)),81)==F(54,81)')
    # Forest-only obstruction with a genuine surviving original residue.
    odd=list(range(3,30,2));S=sum((F(1,m) for m in odd),F());q=min(odd)
    ceiling=(1-F(1,q))*(1+F(1,q)-S)
    require(S>1+F(1,q) and ceiling<0, 'S>1+F(1,q) and ceiling<0')
    require(all(1%m!=0 for m in odd), 'all(1%m!=0 for m in odd)')
    # Kruskal maximum forest gives exact stronger numeric check on the same finite family.
    maxforest=maximum_coprime_forest(odd)
    maxforest_bound=1-S+sum((F(1,a*b) for a,b in maxforest),F())
    result={'605':{'S':str(s605),'forest_bound':str(f605),'survivor_count':count605,'DP_value':str(dp605),'DP_states':states605,'DP_physical_history_checks':physical_states605},'unreachable_negative_DP_control':{'moduli':[3,9],'residues':[0,1],'d':9,'value':str(negative_dp)},'945':{'moduli':m945,'S':str(sum((F(1,m) for m in m945),F())),'user_forest_bound':str(bound(m945,user_forest)),'maximum_coprime_forest_bound':str(bound(m945,set(optimal_forest945))),'core_edges':core_edges,'bridges':sorted(bridges),'core_graphs_examined':1024,'chordal_core_graphs':chordal_count,'induced_active_checks':tested_active,'maximum_forced_coprime_chordal_bound':str(best),'optimizer_count':len(optimizers),'optimal_core_edges':optimizers[0][0],'PEO':optimizers[0][1],'gap_to_repository_sharp191':str(F(191,945)-best)},'forest_obstruction':{'moduli':odd,'S':str(S),'S_decimal':float(S),'q':q,'forest_bound_ceiling':str(ceiling),'exact_best_forest_bound':str(maxforest_bound),'surviving_residue':1,'maximum_forest_edges':maxforest},'arithmetic_C4_warning':{'moduli':c4,'edges':sorted(cycle),'residues':[0]*4,'active_at_0':4,'components':1,'clique_Euler':0,'invalid_cycle_formula':str(bound(c4,cycle)),'actual_survival':'54/81'}}
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
