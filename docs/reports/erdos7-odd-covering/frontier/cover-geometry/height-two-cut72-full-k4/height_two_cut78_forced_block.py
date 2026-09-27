#!/usr/bin/env python3
"""Exact same-source cut78 counterexample to block-mass rerouting.
All displayed flows have integral units1/63. The fixed-cut proof covers
all nonnegative real-valued maximum flows. This is a counterexample to
a proposed selection condition, not to the existence of a good law.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import lcm
import argparse
import json
from pathlib import Path

T=((2,2,2,0,0,0,0),(2,2,1,1,0,0,0),(2,0,0,0,0,0,0),(1,2,1,1,0,0,0),(0,1,1,0,0,0,0))
DIVS=(1,5,7,25,35,49,175,245,1225)
AXES=((1,1),(5,1),(1,7),(25,1),(5,7),(1,49),(25,7),(5,49),(25,49))
CAPS=(78,21,21,7,21,7,6,7,2)

def verify():
    checks=0
    def ck(p,msg):
        nonlocal checks
        checks+=1
        if not p: raise ArithmeticError(msg)
    source=set()
    occ=(tuple(range(5)),tuple(range(5)),tuple(range(5)),tuple(range(4)),())
    # All19 children have the full common column A=0.
    for r in range(4):
        for c in occ[r]:
            for h in range(7): source.add((r,c,0,h))
    # Root0 has all35 points of G=1, but no other column besides A.
    for c in occ[0]:
        for h in range(7): source.add((0,c,1,h))
    # Private leaves:6 at B=2,5 at C=3,7 at D=4.
    private={(1,c,2,c) for c in occ[1]}|{(1,0,2,5)}
    private|={(2,c,3,c) for c in occ[2]}
    for c,hs in enumerate(((0,),(1,2),(3,4),(5,6))):
        private|={(3,c,4,h) for h in hs}
    source|=private
    ck(len(source)==186,'186 actual points')
    ck(len(private)==18,'eighteen private leaves')
    actualocc=tuple(tuple(sorted({c for rr,c,g,h in source if rr==r})) for r in range(5))
    ck(actualocc==occ,'literal occupancy55540')
    def projection(selected):
        return {(g,h) for r,c,g,h in source if (r,c) in selected}
    def has_tree(proj,k):
        return sum(len({h for gg,h in proj if gg==g})>=k for g in range(7))>=k
    ck(has_tree({(g,h) for r,c,g,h in source},5),'standalone5-tree')
    selected_tests=0
    for r,s in combinations(range(4),2):
        for aa in combinations(occ[r],len(occ[r])-2):
            for bb in combinations(occ[s],len(occ[s])-2):
                ck(has_tree(projection({(r,c) for c in aa}|{(s,c) for c in bb}),3),'selected actual ternary tree')
                selected_tests+=1
    ck(selected_tests==480,'480 selected tests')
    literal_tests=0
    for r,s in combinations(range(4),2):
        for aa in combinations(range(5),3):
            for bb in combinations(range(5),3):
                ck(has_tree(projection({(r,c) for c in aa}|{(s,c) for c in bb}),3),'literal ternary tree')
                literal_tests+=1
    ck(literal_tests==600,'600 literal triple tests')
    # Ten root choices, and ten triples independently at each selected root.
    complete_tests=0
    for rr in combinations(range(5),3):
        for childchoices in product(tuple(combinations(range(5),3)),repeat=3):
            selected={(r,c) for r,cs in zip(rr,childchoices) for c in cs}
            ck(has_tree(projection(selected),3),'complete literal5-tree blocking')
            complete_tests+=1
    ck(complete_tests==10000,'10000 complete literal5-tree tests')
    S=('source',);sink=('sink',)
    caps={}
    def edge(u,v,n):
        ck((u,v) not in caps,'unique network edge')
        caps[u,v]=n
    for r in range(4):
        edge(S,('r',r),21)
        for c in occ[r]:
            edge(('r',r),('c',r,c),7)
            for g in range(7):
                edge(('c',r,c),('pg',r,c,g),6)
                for h in range(7):edge(('pg',r,c,g),('ph',r,c,g,h),2)
    for g in range(7):
        edge(('cg',g),sink,21)
        for h in range(7): edge(('ch',g,h),('cg',g),7)
    for r,c,g,h in source:edge(('ph',r,c,g,h),('ch',g,h),126)
    cut={S,('cg',0)}|{('ch',0,h) for h in range(7)}
    for r in (1,2,3):
        cut.add(('r',r))
        for c in occ[r]:
            cut.add(('c',r,c))
            for g in range(7):
                cut.add(('pg',r,c,g))
                for h in range(7):
                    if (r,c,g,h) not in private:cut.add(('ph',r,c,g,h))
    forward=[(u,v,n) for (u,v),n in caps.items() if u in cut and v not in cut]
    backward=[(u,v,n) for (u,v),n in caps.items() if u not in cut and v in cut]
    ck(sum(n for u,v,n in forward)==78,'exact cut78')
    ck(sorted(n for u,v,n in forward)==[2]*18+[21]*2,'cut inventory21+21+36')
    ck((S,('r',0),21) in forward,'root0 source edge is cut')
    # Every root0 off-G point crosses this cut backward.
    root0off=[p for p in source if p[0]==0 and p[2]!=1]
    ck(len(root0off)==35,'35 actual off-block points')
    for r,c,g,h in root0off:
        ck(('ph',r,c,g,h) not in cut and ('ch',g,h) in cut,'root0 off-block bridge is backward')
    for r,c,g,h in source:
        if r==0:ck(g in (0,1),'root0 only common andG')
    # Flow construction: root0/G carries T; all eighteen private points carry2;
    # A carries9 at root1,9 at root2,3 at gap3.
    bad={}
    for c,row in enumerate(T):
        for h,n in enumerate(row):
            if n:bad[0,c,1,h]=n
    bad.update({p:2 for p in private})
    common={(1,0,0,0):2,(1,0,0,5):1,
            (1,1,0,1):2,(1,2,0,2):2,(1,3,0,3):2,
            (2,0,0,0):2,(2,1,0,1):2,(2,2,0,2):2,(2,3,0,3):2,(2,4,0,4):1,
            (3,0,0,0):2,(3,0,0,6):1}
    ck(sum(common.values())==21,'common mass21')
    bad.update(common)
    # Different within-block law: same source, same block mass21.
    good={p:n for p,n in bad.items() if p[0]!=0}
    for c in range(5):
        for delta in range(4):good[0,c,1,(c+delta)%7]=1
    good[0,4,1,1]=1
    def verify_flow(atoms,name):
        ck(sum(atoms.values())==78,name+' integral total78')
        ck(set(atoms)<=source,name+' actual support')
        flow=defaultdict(int)
        for (r,c,g,h),n in atoms.items():
            ck(type(n)is int and n>=0,name+' nonnegative integer')
            path=(S,('r',r),('c',r,c),('pg',r,c,g),('ph',r,c,g,h),('ch',g,h),('cg',g),sink)
            for u,v in zip(path,path[1:]):flow[u,v]+=n
        balance=defaultdict(int)
        for (u,v),cap in caps.items():
            n=flow[u,v]
            ck(0<=n<=cap,name+' exact edge capacity')
            balance[u]-=n;balance[v]+=n
        ck(balance[S]==-78 and balance[sink]==78 and all(n==0 for v,n in balance.items() if v not in (S,sink)),name+' all-node conservation')
        ck(all(flow[u,v]==n for u,v,n in forward),name+' all forward cut edges saturated')
        ck(all(flow[u,v]==0 for u,v,n in backward),name+' zero flow on backward cut edges')
        block=sum(n for (r,c,g,h),n in atoms.items() if r==0 and g==1)
        ck(block==21,name+' forced block mass21')
        maxima=[];cylinders={};literal=0
        for d,(px,py),cap in zip(DIVS,AXES,CAPS):
            sums=defaultdict(int)
            for (r,c,g,h),n in atoms.items():sums[(r+5*c)%px,(g+7*h)%py]+=n
            for x in range(px):
                for y in range(py):
                    ck(sums[x,y]<=cap,name+' numerical cylinder cap')
                    literal+=1
            maxima.append(max(sums.values()));cylinders[d]=sums
        ck(literal==1767,name+'1767 literal cylinders')
        coeffs=(3,3,5,9,5,15,15,25)
        centres=[]
        for x in range(25):
            for y in range(49):
                values=[cylinders[d][x%px,y%py] for d,(px,py) in zip(DIVS[1:],AXES[1:])]
                K=sum(a*b for a,b in zip(coeffs,values))
                nsum=0
                for (r,c,g,h),n in atoms.items():
                    count=sum((r+5*c-x)%px==0 and (g+7*h-y)%py==0 for px,py in AXES[1:])
                    nsum+=n*(count*count+2*count)
                ck(nsum==K,name+' coherent coefficient expansion')
                ck(K<=625,name+' coherent charge bound')
                centres.append((K,x,y,values))
        maximum=max(k for k,x,y,v in centres)
        maxmap=dict(zip(DIVS,maxima))
        ordered_lcm_envelope=sum(maxmap[lcm(d,e)] for d in DIVS for e in DIVS)-78
        ck(ordered_lcm_envelope==sum(a*b for a,b in zip(coeffs,maxima[1:])),name+' complete81-pair envelope')
        return {'total_units':78,'forced_block_units':block,'max_cylinder_units':dict(zip(map(str,DIVS),maxima)),
                'maximum_coherent_charge':maximum,'maximizers':[[x,y,v] for k,x,y,v in centres if k==maximum],
                'nonunit_ordered_lcm_envelope':ordered_lcm_envelope,
                'all_layout_upper_from_cylinder_maxima':str(1+Fraction(ordered_lcm_envelope,78)),
                'all_layout_upper_using449':str(1+Fraction(max(maximum,622),78)),
                'atoms':[[*p,n] for p,n in sorted(atoms.items())]}
    badresult=verify_flow(bad,'bad')
    goodresult=verify_flow(good,'within_block_good')
    ck(badresult['maximum_coherent_charge']==625,'bad has625 coherent centre')
    ck(goodresult['maximum_coherent_charge']<=622,'within-block law removes625')
    ck(goodresult['nonunit_ordered_lcm_envelope']==565,'good81-pair envelope565')
    ck(Fraction(goodresult['all_layout_upper_from_cylinder_maxima'])==Fraction(643,78)<9,'goodGamma upper643/78 independently of449 phase bound')
    ck(Fraction(goodresult['all_layout_upper_using449'])<9,'same-source good law below9 using449 noncoherent estimate')
    # Direct exact formula for why rerouting is impossible for EVERY maxflow:
    # val(f)=sum_forward f - sum_backward f =78=capacity(cut).
    # Hence every forward cut edge is saturated, every backward edge has zero.
    # Root0 input=21; all of its A bridges are backward; hence its G block=21.
    return {'status':'PASS','checks':checks,'source_points':len(source),'occupancy':list(map(len,occ)),
            'selected_tests':selected_tests,'literal_tests':literal_tests,'complete_tree_tests':complete_tests,
            'network_edges':len(caps),'cut_units':78,'cut_forward_edges':[[list(u),list(v),n] for u,v,n in forward],
            'backward_edges_count':len(backward),'root0_off_block_backward_bridges':len(root0off),
            'conclusion':'Every value78 flow, even real-valued and without added old-child caps, has root0/G mass21. This refutes uniform block rerouting, not existence of a good law. An explicit integral good law changes only the mass distribution within the forced block.',
            'proof':'Flow-cut equality forces root0 source input21 and zero on every root0/A bridge because each crosses the same cut backward. Root0 supports only A and G.',
            'source':list(map(list,sorted(source))),'bad_flow':badresult,'good_flow':goodresult}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    payload=json.dumps(verify(),indent=2)+'\n'
    args.output.write_text(payload,encoding='utf-8')
    print(payload,end='')


if __name__=='__main__':main()
