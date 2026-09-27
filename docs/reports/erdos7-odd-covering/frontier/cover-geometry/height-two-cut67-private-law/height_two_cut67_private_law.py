#!/usr/bin/env python3
"""Exact cut67 shapes, Hall checks and an actual three-public-leaf source.

Standard library only. General actual-point forcing is the ordinary proof
in Report449. No original odd-covering realization or outside-cofactor
lift is inferred from the finite controls.
"""
from collections import defaultdict, deque
from fractions import Fraction as F
from itertools import product, combinations, combinations_with_replacement
from math import lcm
from pathlib import Path
import argparse
import json

N=(4,5,5,5)
Q=(2,3,3,3)
def fail_if(flag, data):
    if flag: raise RuntimeError(data)
def ff(n,q,p): return p+(n-q)*((p+q-1)//q)

def verify():
    # Full exhaustive p search: every least-q sum is at most the total cost 23.
    p_vectors=[]
    for p in product(range(24), repeat=4):
        if any(p[i]+p[j]<6 for i,j in combinations(range(4),2)): continue
        base=sum(ff(N[i],Q[i],p[i]) for i in range(4))
        if base<=23: p_vectors.append((p,base))
    fail_if(p_vectors!=[((3,3,3,3),22),((4,3,3,3),23)],p_vectors)

    # Enumerate every sorted child-cost vector, including the allocation of slack.
    shapes=set()
    for p,base in p_vectors:
        minima=[ff(N[i],Q[i],p[i]) for i in range(4)]
        for extra in product(range(24-base), repeat=4):
            if sum(extra)!=23-base: continue
            choices=[]
            for r in range(4):
                total=minima[r]+extra[r]
                choices.append([z for z in combinations_with_replacement(range(total+1),N[r])
                                if sum(z)==total and sum(z[:Q[r]])==p[r]])
            for costs in product(*choices):
                canonical=(costs[0],)+tuple(sorted(costs[1:]))
                shapes.add(canonical)
    A=((2,2,2,2),(1,1,1,1,1),(1,1,1,1,1),(1,1,1,1,1))
    B=((1,2,2,3),(1,1,1,1,1),(1,1,1,1,1),(1,1,1,1,1))
    C=((1,2,2,2),(1,1,1,1,1),(1,1,1,1,1),(1,1,1,1,2))
    fail_if(shapes!={A,B,C},shapes)

    # Hall A: abstract four-set families on an eight-element universe suffice,
    # since each set has size <=2 and hence total union has size <=8.
    def sdr(sets):
        def go(i,used):
            if i==len(sets): return ()
            for x in sorted(sets[i]-used):
                rest=go(i+1,used|{x})
                if rest is not None: return (x,)+rest
            return None
        return go(0,set())
    U=range(8)
    small=[frozenset(c) for k in range(3) for c in combinations(U,k)]
    hall_A_total=hall_A_admissible=0
    for sets in combinations_with_replacement(small,4):
        hall_A_total+=1
        if any(len(sets[i]|sets[j])<3 for i,j in combinations(range(4),2)): continue
        hall_A_admissible+=1
        fail_if(sdr(sets) is None,('Hall A',sets))

    # Hall B/C: three sets of size >=2 and first-two union >=3.
    # It is enough to choose any two elements of each; if the first two agree,
    # choose an alternative pair from one of them to retain union >=3.
    pairs=[frozenset(c) for c in combinations(range(6),2)]
    hall_BC_total=hall_BC_admissible=0
    for sets in product(pairs,repeat=3):
        hall_BC_total+=1
        if len(sets[0]|sets[1])<3: continue
        hall_BC_admissible+=1
        fail_if(sdr(sets) is None,('Hall B/C',sets))

    # Every actual law uses one point at each chosen child, no seven leaf twice,
    # clean full-root columns are disjoint from each other and from all gap points.
    # The canonical patterns below check numerical CRT labels, not source forcing.
    crt=lambda x,y: x+25*((y-x)*pow(25,-1,49)%49)
    divs=sorted(5**a*7**b for a,b in product(range(3),repeat=2))

    def check_law(occupancy):
        atom_count=sum(occupancy)
        law={crt(r+5*c,(r+1)+7*c):F(1,atom_count)
             for r,n in enumerate(occupancy) for c in range(n)}
        fail_if(len(law)!=atom_count or sum(law.values())!=1,'law atom count')
        caps={}
        cylinders=0
        for d in divs:
            masses=[sum((v for x,v in law.items() if x%d==a),F()) for a in range(d)]
            cylinders+=d
            caps[d]=max(masses)
            target=F(1) if d==1 else F(5 if d in(5,7,35) else 1,atom_count)
            fail_if(caps[d]!=target,('caps',occupancy,d,caps[d],target))
        envelope=sum(caps[lcm(d,e)] for d in divs for e in divs)
        target=F(1)+F(140,atom_count)
        fail_if(envelope!=target or envelope>=9,('envelope',occupancy,envelope))
        return {'occupancy':occupancy,'atoms':atom_count,'cylinder_checks':cylinders,
                'ordered_lcm_pairs':81,'caps':{str(d):str(caps[d]) for d in divs},
                'envelope':str(envelope),'margin':str(9-envelope)}
    law_AB=check_law((4,5,5,5))
    law_C=check_law((4,5,5,4))
    fail_if(law_AB['envelope']!='159/19' or law_C['envelope']!='79/9','exact bounds')

    # An ACTUAL source with a public three-leaf cut and a private prefix at B's
    # cost-three gap child. Public column 0 has only three actual leaves; the
    # standalone five-ary tree uses columns 1,2,3,4,5 instead.
    source={}
    public={(0,j) for j in range(3)}
    for r in range(1,4):
        for c in range(5): source[(r,c)]=public|{(r,c)}
    source[(0,0)]={(4,0)}
    source[(0,1)]={(4,1),(4,2)}
    source[(0,2)]={(4,3),(4,4)}
    source[(0,3)]={(5,j) for j in range(5)}
    projection=set().union(*source.values())
    def tree(ys,arity):
        return sum(sum(g==col for g,digit in ys)>=arity for col in range(7))>=arity
    fail_if(not tree(projection,5),'standalone actual tree')
    selected_tests=0
    for r,s in combinations(range(4),2):
        for rc in combinations(range(N[r]),Q[r]):
            for sc in combinations(range(N[s]),Q[s]):
                selected_tests+=1
                ys=set().union(*(source[(r,c)] for c in rc),*(source[(s,c)] for c in sc))
                fail_if(not tree(ys,3),('literal pair test',r,s,rc,sc))
    # Also all literal complete ternary five-trees, including the empty root and
    # the gap's empty child. This implies blocking every complete five-ary seven-tree.
    original_five_tests=0
    for roots in combinations(range(5),3):
        for childsets in product(list(combinations(range(5),3)),repeat=3):
            original_five_tests+=1
            ys=set().union(*(source.get((r,c),set())
                             for r,children in zip(roots,childsets) for c in children))
            fail_if(not tree(ys,3),('original literal test',roots,childsets))

    # Exact integral max flow, all capacities in units 1/63. Absent prefix nodes
    # have no source-sink path and are safely omitted.
    class Flow:
        def __init__(self): self.g=defaultdict(list)
        def add(self,u,v,c):
            f=[v,c,None]; b=[u,0,f]; f[2]=b
            self.g[u].append(f); self.g[v].append(b)
        def maximum(self,s,t):
            total=0
            while True:
                parent={s:None}; queue=deque([s])
                while queue and t not in parent:
                    u=queue.popleft()
                    for edge in self.g[u]:
                        v,c,rev=edge
                        if c>0 and v not in parent:
                            parent[v]=(u,edge); queue.append(v)
                if t not in parent: return total
                aug=10**9; v=t
                while v!=s:
                    u,e=parent[v]; aug=min(aug,e[1]); v=u
                v=t
                while v!=s:
                    u,e=parent[v]; e[1]-=aug; e[2][1]+=aug; v=u
                total+=aug
    net=Flow()
    for r in range(4):
        net.add('s',('root',r),21)
        for c in range(N[r]):
            child=('child',r,c)
            net.add(('root',r),child,7)
            ys=source[(r,c)]
            for g in {g for g,digit in ys}: net.add(child,('private col',r,c,g),6)
            for g,digit in ys:
                leaf=('private leaf',r,c,g,digit)
                net.add(('private col',r,c,g),leaf,2)
                net.add(leaf,('public leaf',g,digit),126)
    for g,digit in projection: net.add(('public leaf',g,digit),('public col',g),7)
    for g in {g for g,digit in projection}: net.add(('public col',g),'t',21)
    maximum=net.maximum('s','t')
    fail_if(maximum!=67,('public-leaf source min cut',maximum))
    # A law on this actual source includes all 15 full clean points and one at
    # every gap child, including a point in column5 distinct from the others.
    witness=[(r,c,(r,c)) for r in range(1,4) for c in range(5)]
    witness += [(0,0,(4,0)),(0,1,(4,1)),(0,2,(4,3)),(0,3,(5,0))]
    actual_law={crt(r+5*c,g+7*d):F(1,19) for r,c,(g,d) in witness}
    for r,c,y in witness: fail_if(y not in source[(r,c)],('phantom',r,c,y))
    for d in divs:
        cap=max(sum((v for x,v in actual_law.items() if x%d==a),F()) for a in range(d))
        target=F(1) if d==1 else F(5 if d in(5,7,35) else 1,19)
        fail_if(cap>target,('actual source law cap',d,cap,target))

    result={'p_vectors':p_vectors,'private_shapes':{'A':A,'B':B,'C':C},
            'p_vector_tests':24**4,'cost3_edge_types':['three leaf edges','one first-prefix edge'],
            'Hall_A_family_tests':hall_A_total,'Hall_A_admissible':hall_A_admissible,
            'Hall_BC_family_tests':hall_BC_total,'Hall_BC_admissible':hall_BC_admissible,
            'A_B_uniform_law':law_AB,'C_uniform_law':law_C,
            'public_three_leaf_actual_source':{'actual_points':sum(map(len,source.values())),
                 'seven_projection_size':len(projection),'public_column_actual_leaves':3,
                 'standalone_columns':[1,2,3,4,5],'selected_pair_tests':selected_tests,
                 'original_ternary_five_tests':original_five_tests,'max_flow_numerator_over63':maximum,
                 'witness_law_atoms':len(actual_law)},
            'scope':'Cost-shape and Hall enumeration, exact CRT law caps, plus one actual source with all literal tests and exact min cut. General actual-leaf and column forcing is proved in companion text, not inferred from these fixtures. No original odd covering realization or outside-cofactor lift is asserted.'}
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
