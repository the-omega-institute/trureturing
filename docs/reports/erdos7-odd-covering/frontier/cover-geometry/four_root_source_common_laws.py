"""Exact arithmetic certificates for two height-two actual-source classes.
Standard library only; all checks active under -O. No optimization or source-family enumeration is used in these certificates.
"""
from fractions import Fraction as F
from itertools import product,combinations
from pathlib import Path
import importlib.util,json
BASE=Path(__file__).resolve().parent
def load(name):
    s=importlib.util.spec_from_file_location(name,BASE/(name+'.py'))
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
root=load('root_rectangle_second_moment');rf=load('three_robust_roots_common_law')

def require(x,msg):
    if not x:raise ValueError(msg)

WEIGHTS={
 'A':(3,3,2,2,2,2,3,3),
 'B':(4,3,4,3,4,3,4),
 'C':(4,3,3,3,3,3,3),
 'D':(4,3,3,3,3,3,3),
 'F':(1,1,1,1,1,1,1),
 'cycle4':(1,1,1,1,1,1,1,1),
 'triangle_full':(1,1,1,1,1,1,1,1,1),
 'two_triples':(1,1,1,1,1,1,1,1,1),
 'singleton_triangle':(4,3,3,3,3,3,3),
 'A_shared':(4,3,3,2,2,3,3,3),
}
EXPECTED={'A':F(301,60),'B':F(382,75),'C':F(5),'D':F(5),
          'F':F(100,21),'cycle4':F(14,3),'triangle_full':F(46,9),
          'two_triples':F(46,9),'singleton_triangle':F(5),'A_shared':F(117,23)}
PTS=tuple((r,a,y) for r in range(1,5) for a in range(5) for y in range(7))
ROOT_PHASES=tuple(product(range(7),range(1,5),range(1,5),range(7)))
LABELS=(1,5,25,7,35,175)

def crt(x,m,y):
    inverse={5:3,25:2}[m]
    out=x+m*((y-x)*inverse%7)
    require(out%m==x and out%7==y and 0<=out<7*m,'CRT')
    return out

def exact_layout_maximum(w):
    best=-1;win=None
    for c0,p1,m1,c1 in ROOT_PHASES:
        loads=[1+(y==c0)+(r==p1)+((r,y)==(m1,c1)) for r,a,y in PTS]
        base=sum(l*l*n for l,n in zip(loads,w))
        gains=[(2*l+1)*n for l,n in zip(loads,w)]
        pure=[sum(gains[7*a:7*a+7]) for a in range(20)]
        order=sorted(range(20),key=lambda a:pure[a]);first,second=order[-1],order[-2]
        for mixed in range(140):
            leaf=mixed//7;other=first if first!=leaf else second
            same=pure[leaf]+2*w[mixed]
            value=base+gains[mixed]+max(same,pure[other])
            if value>best:
                best=value;win=(c0,p1,m1,c1,leaf if same>=pure[other] else other,mixed)
    c0,p1,m1,c1,pure,mixed=win
    r,a,_=PTS[7*pure];u,v,y=PTS[mixed]
    phases=(0,p1,r+5*a,c0,crt(m1,5,c1),crt(u+5*v,25,y))
    literal=sum(n*sum(crt(r+5*a,25,y)%d==b for d,b in zip(LABELS,phases))**2
                for (r,a,y),n in zip(PTS,w))
    require(literal==best,'attaining layout agrees with all six literal CRT labels')
    return best,phases

def matching_or_robust():
    matching=[rf.cap_bound(mask,4,1,1) for mask in range(16)]
    envelope=[max(a,b) for a,b in zip(matching,rf.ENVELOPE)]
    results=[]
    for allocation in product(range(4),repeat=4):
        masks=tuple(sum(1<<j for j in range(4) if allocation[j]==r) for r in range(4))
        value=sum(envelope[mask] for mask in masks)
        require(value<=18,'four-root local-mask budget')
        results.append((value,masks))
    require(len(results)==256 and max(v for v,m in results)==18,'sharp envelope maximum')
    return dict(matching4_mask_bounds=list(map(str,matching)),
                common_mask_bounds=list(map(str,envelope)),allocations=len(results),
                maximum_sum='18',common_law_bound='9/2',
                attaining_masks=[m for v,m in results if v==18])

def shared_child_rectangles():
    results=[]
    require(WEIGHTS.keys()==root.TEMPLATES.keys(),'every existing minimal root type covered')
    for name,rows in root.TEMPLATES.items():
        require(all(rows) and all((a|b).bit_count()>=3 for a,b in combinations(rows,2)),
                'the actual four row column sets satisfy RB5')
        edges=root.edges(rows);nums=WEIGHTS[name];N=sum(nums)
        require(len(nums)==len(edges) and all(type(n)is int and n>0 for n in nums),'supported positive law')
        masses=dict(zip(edges,nums))
        w=[masses.get((r-1,y),0) if a<3 else 0 for r,a,y in PTS]
        require(sum(w)==3*N,'single supported law uniform on the three children')
        for E in combinations(range(7),2):
            good=sum(any(rows[r]>>y&1 for y in range(7) if y not in E) for r in range(4))
            require(good>=3,'all 21 original product-tree column tests')
        best,phases=exact_layout_maximum(w);value=F(best,3*N)
        require(value==EXPECTED[name]<=F(46,9),'exact complete original-label bound')
        results.append(dict(name=name,root_edge_order=edges,integer_weights=nums,
                            root_denominator=N,full_law_denominator=3*N,
                            exact_maximum=str(value),attaining_phases=phases))
    return dict(laws=results,old_root_layouts_per_law=784,mixed_point_choices_per_layout=140,
                pure_leaf_choices_per_layout=20,full_phase_choices_per_law=2195200,
                law_point_evaluations_in_attaining_CRT_checks=1400,
                common_law_bound='46/9')

MATCHING_PATTERNS=(
    ((1,3,4,5),(9,24,30,35),F(143,28)),
    ((1,4,4,4),(1,4,4,4),F(66,13)),
    ((2,2,4,5),(3,3,5,6),F(1723,340)),
    ((2,3,3,5),(3,4,4,6),F(859,170)),
    ((2,3,4,4),(2,3,4,4),F(66,13)),
    ((3,3,3,4),(1,1,1,1),F(245,48)),
)

def prescribed_matching_sizes():
    results=[]
    for sizes,weights,expected in MATCHING_PATTERNS:
        denominator=sum(weights)
        def local(mask,n):
            c=1+(mask&1);t=1+((mask>>1)&1)
            e=(mask>>2)&1;f=(mask>>3)&1
            return F((c+t+e+f)**2+(n-1)*c*c,n)
        maximum=F(0)
        for allocation in product(range(4),repeat=4):
            masks=[sum(1<<j for j in range(4) if allocation[j]==r) for r in range(4)]
            value=sum(F(weights[r],denominator)*local(masks[r],sizes[r]) for r in range(4))
            maximum=max(maximum,value)
        require(maximum==expected<=F(46,9),'prescribed matching-size common-law bound')
        results.append(dict(matching_sizes=sizes,root_mass_numerators=weights,
                            root_mass_denominator=denominator,mask_bound=str(maximum)))
    return results

def outside_earlier_selection_control():
    rows=(
        (set(),{0,3},{0,2},set(),{0,4,6}),
        ({3},{3,5},set(),{5},{1}),
        ({6},set(),{6},{4},set()),
        ({2,6},set(),{1},{0},{0,1}),
    )
    bad=[];match_sizes=[]
    for neighbourhoods in rows:
        bad.append({E for E in combinations(range(7),2)
                    if sum(bool(ys-set(E)) for ys in neighbourhoods)<3})
        best=0
        for assignment in product(range(-1,7),repeat=5):
            chosen=[(a,y) for a,y in enumerate(assignment) if y>=0]
            if len({y for a,y in chosen})!=len(chosen):continue
            if all(y in neighbourhoods[a] for a,y in chosen):best=max(best,len(chosen))
        match_sizes.append(best)
    require(sum(len(ys) for rr in rows for ys in rr)==21,'boundary source cardinality')
    require(all(bad) and all(a.isdisjoint(b) for a,b in combinations(bad,2)),
            'source meets all product-tree tests but no root is robust')
    require(len(set().union(*(ys for rr in rows for ys in rr)))==7,'seven actual columns')
    require(match_sizes==[3,3,2,3],'exact boundary-source matching ranks')
    sorted_sizes=sorted(match_sizes)
    require(not any(all(n>=needed for n,needed in zip(sorted_sizes,sizes))
                    for sizes,weights,bound in MATCHING_PATTERNS),'outside six matching criteria')
    require(not any(set.intersection(*(rows[1][a] for a in aset))
                    for aset in combinations(range(5),3)),'second root has no three-child rectangle')
    require(all(len(ys)<=1 for ys in rows[2]),'third root has no two-neighbour child')
    centers=[(r,y) for r,rr in enumerate(rows) for y in range(7)
             if sum(y in ys for ys in rr)>=3]
    require(centers==[(0,0)],'only possible selected three-child column')
    require(all(any(match_sizes[j]<3 for j in range(4) if j!=r) for r,y in centers),
            'outside the singleton-column and three-matching criterion')
    return dict(source_rows=[[sorted(ys) for ys in rr] for rr in rows],
                bad_pairs=[sorted(b) for b in bad],matching_sizes=match_sizes,
                points=21,columns=7,scope='outside the earlier criteria; the eleven-point flow criterion does apply')

if __name__=='__main__':
    print(json.dumps(dict(matching_or_robust=matching_or_robust(),
                          prescribed_matching_sizes=prescribed_matching_sizes(),
                          outside_earlier_selection_control=outside_earlier_selection_control(),
                          shared_child_rectangles=shared_child_rectangles()),indent=2))
