#!/usr/bin/env python3
"""Exact cut69 profile classification and an actual minimum-cut source.

Standard library only. Report449 contains the general actual-support proof
for all ten shapes. Neither the finite control nor that fixed-head theorem
supplies original odd-cover realization or an outside-cofactor lift.
"""
from collections import defaultdict, deque
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from functools import lru_cache
from math import lcm
from pathlib import Path
import argparse
import json

N=(4,5,5,5);Q=(2,3,3,3)
def ff(a,q,p):return p+(a-q)*((p+q-1)//q)
def lower(active,I,u):
    if u<=0:return 0
    return min(sum(ff(active[r],Q[r],p if r==j else max(p,u-p)) for r in I)
               for j in I for p in range((u+1)//2+1))

def verify_profiles():
    profiles=[]
    for active in product(*(range(n+1) for n in N)):
        top=sum(min(3,n-a) for n,a in zip(N,active)); I=[r for r in range(4) if active[r]>=Q[r]]
        for k in range(10):
            zmin=(sum(active) if k==0 else 0) if len(I)<2 else lower(active,I,max(0,9-k))
            if k==0:zmin=max(zmin,sum(active))
            if active==N:zmin=max(zmin,15-k)
            num=69-7*(top+k)
            if num>=0 and num%2==0 and num//2>=zmin:profiles.append(dict(active=active,top=top,k=k,Z=num//2))
    @lru_cache(None)
    def choices(a,q,p,cost):
        return tuple(z for z in combinations_with_replacement(range(cost+1),a) if sum(z)==cost and sum(z[:q])==p)
    result=[]
    for d in profiles:
        a=d['active'];z=d['Z'];u=max(0,9-d['k']);I=[r for r in range(4) if a[r]>=Q[r]]
        if len(I)!=4:raise RuntimeError(('need general eligible-shape enumeration',d))
        pv=[];shapes=set()
        for p in product(range(z+1),repeat=4):
            if any(p[i]+p[j]<u for i,j in combinations(range(4),2)):continue
            bases=[ff(a[r],Q[r],p[r]) for r in range(4)];base=sum(bases)
            if base>z:continue
            pv.append((p,base))
            for slack in product(range(z-base+1),repeat=5):
                if sum(slack)!=z-base or (a==N and slack[4]):continue
                zz=[choices(a[r],Q[r],p[r],bases[r]+slack[r]) for r in range(4)]
                for shape in product(*zz):
                    # Full-root permutations only if active profiles allow them.
                    canonical=(shape[0],)+tuple(sorted(shape[1:]))+(slack[4],)
                    shapes.add(canonical)
        result.append(dict(profile=d,p_vectors=pv,shapes=sorted(shapes)))
    out={'profile_count':len(profiles),'necessary_profile_tests':10800,'profiles_and_shapes':result,'scope':'Necessary minimum-cut integer profiles; not actual source realizability.'}
    if {(tuple(v['active']),v['top'],v['k'],v['Z']) for v in profiles}!={(N,0,3,24),(N,0,5,17)}:
        raise RuntimeError('unexpected necessary cut69 profiles')
    expected3={('0333','11111','11111','11111'),('1222','01222','11111','11111'),('1222','11111','11111','11113'),('1222','11111','11111','11122'),('1222','11111','11112','11112'),('1223','11111','11111','11112'),('1224','11111','11111','11111'),('1233','11111','11111','11111'),('2222','11111','11111','11112'),('2223','11111','11111','11111')}
    for item in result:
        shapes={tuple(''.join(map(str,row)) for row in z[:4]) for z in item['shapes']}
        if any(z[4] for z in item['shapes']):raise RuntimeError('inactive cost in full profile')
        if item['profile']['k']==3 and shapes!=expected3:raise RuntimeError('unexpected k3 shapes')
        if item['profile']['k']==5 and (len(shapes)!=3 or any(max(row)>2 for z in item['shapes'] for row in z[:4])):raise RuntimeError('unexpected k5 leaf shapes')
    return out

def verify_actual_source():
    count=0
    def check(v,msg):
        nonlocal count
        if not v:raise RuntimeError(msg)
        count+=1
    N=(4,5,5,5);Q=(2,3,3,3)
    G={(0,h) for h in range(5)}
    source={(r,c):G|{(r,c)} for r in range(1,4) for c in range(5)}
    source[(0,0)]=G.copy()
    for c,hs in enumerate(({0,1,2},{2,3,4},{0,3,4}),1):source[(0,c)]={(4,h) for h in hs}
    check(sum(map(len,source.values()))==104,'source cardinality')
    projection=set().union(*source.values())
    def tree(ys,k):return sum(sum(g==a for g,b in ys)>=k for a in range(7))>=k
    check(tree(projection,5),'actual standalone')
    pair_tests=0
    for r,s in combinations(range(4),2):
        for rc in combinations(range(N[r]),Q[r]):
            for sc in combinations(range(N[s]),Q[s]):
                pair_tests+=1
                ys=set().union(*(source[(r,c)] for c in rc),*(source[(s,c)] for c in sc))
                check(tree(ys,3),('pair',r,s,rc,sc))
    original_tests=0
    for roots in combinations(range(5),3):
        for children in product(tuple(combinations(range(5),3)),repeat=3):
            original_tests+=1
            ys=set().union(*(source.get((r,c),set()) for r,cc in zip(roots,children) for c in cc))
            check(tree(ys,3),('original',roots,children))
    net=defaultdict(list); edges=[]
    def edge(u,v,c):
        f=[v,c,None];b=[u,0,f];f[2]=b;net[u].append(f);net[v].append(b);edges.append((u,v,c,f))
    for r in range(4):
        edge('s',('root',r),21)
        for c in range(N[r]):
            child=('child',r,c);edge(('root',r),child,7)
            ys=source[r,c]
            for g in sorted({g for g,h in ys}):edge(child,('private col',r,c,g),6)
            for g,h in sorted(ys):
                leaf=('private leaf',r,c,g,h)
                edge(('private col',r,c,g),leaf,2);edge(leaf,('public leaf',g,h),126)
    for g,h in sorted(projection):edge(('public leaf',g,h),('public col',g),7)
    for g in sorted({g for g,h in projection}):edge(('public col',g),'t',21)
    flow=0
    while True:
        parents={'s':None};queue=deque(['s'])
        while queue and 't' not in parents:
            u=queue.popleft()
            for e in net[u]:
                if e[1] and e[0] not in parents:parents[e[0]]=(u,e);queue.append(e[0])
        if 't' not in parents:break
        v='t';aug=1000
        while v!='s':u,e=parents[v];aug=min(aug,e[1]);v=u
        v='t'
        while v!='s':u,e=parents[v];e[1]-=aug;e[2][1]+=aug;v=u
        flow+=aug
    check(flow==69,'maxflow')
    balance=defaultdict(int)
    for u,v,c,e in edges:
        f=c-e[1];check(0<=f<=c,('capacity',u,v,f,c));balance[u]-=f;balance[v]+=f
    check(balance['s']==-69 and balance['t']==69,'terminal balance')
    check(all(v==0 for n,v in balance.items() if n not in ('s','t')),'conservation')
    reachable=set(parents)
    cut=[(u,v,c) for u,v,c,e in edges if u in reachable and v not in reachable]
    check(sum(c for u,v,c in cut)==69,'dual cut')
    parts={'top':0,'private':0,'public':0,'bridge':0}
    for u,v,c in cut:
        if u=='s' or u[0]=='root':key='top'
        elif u[0]=='private leaf':key='bridge'
        elif u[0] in ('public leaf','public col'):key='public'
        else:key='private'
        parts[key]+=c
    check(parts=={'top':0,'private':48,'public':21,'bridge':0},('cutparts',parts))
    active=tuple(sum(('child',r,c) in reachable for c in range(N[r])) for r in range(4))
    check(active==N,'fully active cut')
    selected=[(r,c,(r,c)) for r in range(1,4) for c in range(5)] + [(0,1,(4,0)),(0,2,(4,2)),(0,3,(4,3))]
    for r,c,y in selected:check(y in source[r,c],('actual law',r,c,y))
    def crt(x,y):return x+25*((y-x)*pow(25,-1,49)%49)
    law={crt(r+5*c,g+7*h):Fraction(1,18) for r,c,(g,h) in selected}
    check(len(law)==18 and sum(law.values())==1,'normalized law')
    divs=sorted(5**a*7**b for a,b in product(range(3),repeat=2));caps={};cylinders=0
    for d in divs:
        masses=[sum((v for x,v in law.items() if x%d==a),Fraction()) for a in range(d)]
        target=Fraction(1) if d==1 else Fraction(5 if d in (5,7,35) else 1,18)
        check(max(masses)<=target,('cylinders',d));caps[d]=max(masses);cylinders+=len(masses)
    envelope=sum(caps[lcm(d,e)] for d,e in product(divs,repeat=2))
    check(envelope==Fraction(79,9),'envelope')
    result={'source_points':sum(map(len,source.values())),'projection_points':len(projection),'fibres':[{'child':rc,'leaves':sorted(ys)} for rc,ys in sorted(source.items())],
            'pair_tests':pair_tests,'original_five_tests':original_tests,'network_edges':len(edges),'flow_over63':flow,'cut_edges':cut,'cut_parts_over63':parts,'active_profile':active,
            'law_residues':sorted(law),'law_atoms':len(law),'cylinders_evaluated':cylinders,'caps':{str(d):str(v) for d,v in caps.items()},'ordered_lcm_envelope':str(envelope),'explicit_checks':count,
            'scope':'One actual literal height-two source with exact mincut69 and an actual uniform18 law. General ten-shape support forcing is the ordinary proof in companion text; no unrestricted odd-cover conclusion.'}
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    result={'classification':verify_profiles(),'actual_source':verify_actual_source()}
    payload=json.dumps(result,indent=2)+'\n'
    args.output.write_text(payload,encoding='utf-8')
    print(payload,end='')


if __name__=='__main__':main()
