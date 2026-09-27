#!/usr/bin/env python3
"""Exact cut68 necessary profiles, private shapes and an actual partial source.

Standard library only. General source-to-law arguments are ordinary proofs
in Report449. A finite source control is not an original odd-covering
residual or a certificate of an outside-cofactor lift.
"""
from collections import defaultdict,deque
from fractions import Fraction as F
from itertools import combinations,combinations_with_replacement,product
from math import lcm
from pathlib import Path
import argparse
import json
N=(4,5,5,5); Q=(2,3,3,3)
def check(v,msg):
    if not v: raise RuntimeError(msg)
def ff(a,q,p): return p+(a-q)*((p+q-1)//q)
def lower_private(active,I,u):
    if u<=0:return 0
    return min(sum(ff(active[r],Q[r],p if r==j else max(p,u-p)) for r in I)
               for j in I for p in range((u+1)//2+1))

def verify():
    profiles=[]; mins={}; partial_min=999; checks=0
    for active in product(*(range(n+1) for n in N)):
        top=sum(min(3,n-a) for n,a in zip(N,active))
        I=[r for r in range(4) if active[r]>=Q[r]]
        for k in range(10):
            checks+=1
            if len(I)<2: Zmin=sum(active) if k==0 else 0
            else: Zmin=lower_private(active,I,max(0,9-k))
            if k==0: Zmin=max(Zmin,sum(active))
            if active==N: Zmin=max(Zmin,15-k)
            low=7*(top+k)+2*Zmin
            mins[len(I)]=min(mins.get(len(I),999),low)
            if len(I)==4 and active!=N: partial_min=min(partial_min,low)
            numerator=68-7*(top+k)
            if numerator>=0 and numerator%2==0 and numerator//2>=Zmin:
                profiles.append({'active':active,'top_units':top,'public_units':k,'private_units':numerator//2})
    expected=[{'active':(3,5,5,5),'top_units':1,'public_units':3,'private_units':20},
              {'active':N,'top_units':0,'public_units':4,'private_units':20}]
    check(profiles==expected,('all compatible profiles',profiles))
    # No k>=10: public cost alone is at least70/63.
    shape_result=[]
    for profile in profiles:
        active=profile['active']; total=profile['private_units']; u=9-profile['public_units']
        p_candidates=[]; shapes=set()
        for p in product(range(total+1),repeat=4):
            if any(p[i]+p[j]<u for i,j in combinations(range(4),2)):continue
            roots_min=[ff(active[r],Q[r],p[r]) for r in range(4)]
            base=sum(roots_min)
            if base>total:continue
            p_candidates.append((p,base))
            # The fifth slack coordinate allows unused private cost at inactive children.
            for slack in product(range(total-base+1),repeat=5):
                if sum(slack)!=total-base:continue
                if active==N and slack[4]:continue
                choices=[]
                for r in range(4):
                    cost=roots_min[r]+slack[r]
                    choices.append([z for z in combinations_with_replacement(range(cost+1),active[r])
                                    if sum(z)==cost and sum(z[:Q[r]])==p[r]])
                for z in product(*choices): shapes.add((z[0],)+tuple(sorted(z[1:]))+(slack[4],))
        shape_result.append({'profile':profile,'p_vectors':p_candidates,'shapes':sorted(shapes)})
    partial_shape=((1,2,2),(1,1,1,1,1),(1,1,1,1,1),(1,1,1,1,1),0)
    full_gap=((1,1,1,2),(1,1,1,1,1),(1,1,1,1,1),(1,1,1,1,1),0)
    full_full=((1,1,1,1),(1,1,1,1,1),(1,1,1,1,1),(1,1,1,1,2),0)
    check(shape_result[0]['p_vectors']==[((3,3,3,3),20)],shape_result[0])
    check(shape_result[0]['shapes']==[partial_shape],shape_result[0])
    check(shape_result[1]['p_vectors']==[((2,3,3,3),19)],shape_result[1])
    check(set(shape_result[1]['shapes'])=={full_gap,full_full},shape_result[1])

    # An actual source with the partial-active cut: active gap children have
    # {z}, two leaves, two leaves; its fourth actual child is deliberately rich.
    public={(0,j) for j in range(5)}
    source={(r,c):public|{(r,c)} for r in range(1,4) for c in range(5)}
    source[(0,0)]={(4,0)}
    source[(0,1)]={(4,1),(4,2)}
    source[(0,2)]={(4,3),(4,4)}
    source[(0,3)]=set(product(range(7),repeat=2))
    def tree(ys,arity):return sum(sum(g==col for g,j in ys)>=arity for col in range(7))>=arity
    projection=set().union(*source.values())
    check(tree(projection,5),'standalone')
    pair_checks=0
    for r,s in combinations(range(4),2):
        for rc in combinations(range(N[r]),Q[r]):
            for sc in combinations(range(N[s]),Q[s]):
                pair_checks+=1
                ys=set().union(*(source[(r,c)] for c in rc),*(source[(s,c)] for c in sc))
                check(tree(ys,3),('pair',r,s,rc,sc))
    original_checks=0
    for roots in combinations(range(5),3):
        for childsets in product(list(combinations(range(5),3)),repeat=3):
            original_checks+=1
            ys=set().union(*(source.get((r,c),set()) for r,cs in zip(roots,childsets) for c in cs))
            check(tree(ys,3),('original',roots,childsets))
    # Exact integral max flow on the actual-child network.
    graph=defaultdict(list)
    original_edges=[]
    edge_states=[]
    def edge(u,v,c):
        f=[v,c,None];b=[u,0,f];f[2]=b;graph[u].append(f);graph[v].append(b)
        original_edges.append((u,v,c))
        edge_states.append((u,v,c,f))
    for r in range(4):
        edge('s',('root',r),21)
        for c in range(N[r]):
            child=('child',r,c);edge(('root',r),child,7)
            ys=source[r,c]
            for g in sorted({g for g,j in ys}):edge(child,('private col',r,c,g),6)
            for g,j in sorted(ys):
                leaf=('private leaf',r,c,g,j)
                edge(('private col',r,c,g),leaf,2);edge(leaf,('public leaf',g,j),126)
    for g,j in sorted(projection):edge(('public leaf',g,j),('public col',g),7)
    for g in sorted({g for g,j in projection}):edge(('public col',g),'t',21)
    maximum=0
    while True:
        parents={'s':None};queue=deque(['s'])
        while queue and 't' not in parents:
            u=queue.popleft()
            for e in graph[u]:
                if e[1] and e[0] not in parents:parents[e[0]]=(u,e);queue.append(e[0])
        if 't' not in parents:break
        v='t';aug=10**9
        while v!='s':u,e=parents[v];aug=min(aug,e[1]);v=u
        v='t'
        while v!='s':u,e=parents[v];e[1]-=aug;e[2][1]+=aug;v=u
        maximum+=aug
    check(maximum==68,('actual minimum cut',maximum))
    # Verify the resulting flow against original capacities and node balances.
    balances=defaultdict(int)
    for u,v,c,state in edge_states:
        flow=c-state[1]
        check(0<=flow<=c,('original edge capacity',u,v,flow,c))
        balances[u]-=flow
        balances[v]+=flow
    check(balances['s']==-maximum and balances['t']==maximum,'terminal balance')
    check(all(b==0 for v,b in balances.items() if v not in ('s','t')),
          'internal flow conservation')
    # Residual-reachable nodes provide an independently returned minimum-cut profile.
    reachable=set(parents)
    cut_edges=[(u,v,c) for u,v,c in original_edges if u in reachable and v not in reachable]
    check(sum(c for u,v,c in cut_edges)==maximum,'returned flow/cut equality')
    cut_parts={'top':0,'private':0,'public':0,'bridge':0}
    for u,v,c in cut_edges:
        if u=='s' or u[0]=='root': kind='top'
        elif u[0]=='private leaf': kind='bridge'
        elif u[0] in ('public leaf','public col'): kind='public'
        else: kind='private'
        cut_parts[kind]+=c
    check(cut_parts=={'top':7,'private':40,'public':21,'bridge':0},
          ('actual cut decomposition',cut_parts))
    active=tuple(sum(('child',r,c) in reachable for c in range(N[r])) for r in range(4))
    check(active==(3,5,5,5),('actual active profile',active))
    crt=lambda x,y:x+25*((y-x)*pow(25,-1,49)%49)
    witness=[(r,c,(r,c)) for r in range(1,4) for c in range(5)]
    witness += [(0,0,(4,0)),(0,1,(4,1)),(0,2,(4,3))]
    for r,c,y in witness:check(y in source[r,c],('phantom',r,c,y))
    law={crt(r+5*c,g+7*j):F(1,18) for r,c,(g,j) in witness}
    check(len(law)==18 and sum(law.values())==1,'law')
    divs=sorted(5**a*7**b for a,b in product(range(3),repeat=2));caps={};cylinder_checks=0
    for d in divs:
        cap=max(sum((v for x,v in law.items() if x%d==a),F()) for a in range(d))
        target=F(1) if d==1 else F(5 if d in(5,7,35) else 1,18)
        check(cap<=target,('cap',d,cap,target));caps[d]=cap;cylinder_checks+=d
    envelope=sum(caps[lcm(d,e)] for d in divs for e in divs)
    check(envelope==F(79,9),'envelope')
    result={'necessary_profile_tests':checks,'minima_by_eligible':mins,'partial_four_min':partial_min,
            'compatible_cut68_profiles':profiles,'exact_private_shapes':shape_result,'p_vector_tests_per_profile':21**4,
            'actual_partial_source':{'points':sum(map(len,source.values())),'seven_projection_size':len(projection),
             'selected_pair_tests':pair_checks,'original_five_tree_tests':original_checks,'maximum_flow_over63':maximum,
             'original_network_edges':len(original_edges),
             'residual_min_cut_active_profile':active,'cut_edges':cut_edges,
         'cut_parts_over63':cut_parts,
         'fibres':[{'child':rc,'leaves':sorted(ys)} for rc,ys in sorted(source.items())],
         'law_residues':sorted(law),'law_atoms':len(law),'cylinder_checks':cylinder_checks,
             'ordered_lcm_pairs':81,'envelope':str(envelope),'caps':{str(d):str(v) for d,v in caps.items()}},
            'scope':'All necessary integer cut68 profiles and sorted private shapes; one actual partial-cut source and its selected actual law. General partial-cut support forcing is ordinary proof in companion text. The fully active support constructor is in height_two_cut68_actual_matching.py, with both general proofs in Report449. No original odd covering realization or outside-cofactor lift.'}
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'),
                        help='exact result path (default: sibling .json)')
    args=parser.parse_args()
    payload=json.dumps(verify(),indent=2)+'\n'
    args.output.write_text(payload,encoding='utf-8')
    print(payload,end='')


if __name__=='__main__':
    main()
