#!/usr/bin/env python3
"""A supported common law for four roots with three non-singleton child fibres.
Uses exact original degree-two pair ownership, not ownership of selected pairs.
Standard library; no checks disappear under -O. Output is JSON on stdout.
"""
from collections import Counter, deque
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import json
import runpy

LABELS=(1,5,25,7,35,175)

def require(ok,message):
    if not ok:raise ValueError(message)

def normalize(rows,root_digits,child_digits):
    require(len(rows)==4,'four source roots')
    require(len(root_digits)==4 and len(set(root_digits))==4 and all(type(r)is int and r in range(5) for r in root_digits),'four distinct actual root digits')
    if child_digits is None:child_digits=((0,1,2),)*4
    require(len(child_digits)==4,'four actual child-digit lists')
    norm=[]
    for row,digits in zip(rows,child_digits):
        require(len(row)==3,'three selected active children per root')
        require(len(digits)==3 and len(set(digits))==3 and all(type(a)is int and a in range(5) for a in digits),'three distinct actual child digits in each root')
        out=[]
        for neighborhood in row:
            require(2<=len(neighborhood)<=7 and len(set(neighborhood))==len(neighborhood),'each actual neighborhood has at least two distinct columns')
            require(all(type(y)is int and y in range(7) for y in neighborhood),'actual seven columns')
            out.append(tuple(sorted(neighborhood)))
        norm.append(tuple(out))
    norm=tuple(norm)
    bad=tuple({N for N in row if len(N)==2} for row in norm)
    require(all(bad[r].isdisjoint(bad[s]) for r,s in combinations(range(4),2)),'original degree-two pair sets are disjoint between roots')
    return norm,tuple(root_digits),tuple(tuple(a) for a in child_digits)

def select_by_flow(rows):
    """Integral source->child(2)->column(1)->sink(8) network."""
    graph={};src=('source',);sink=('sink',)
    def edge(u,v,c):
        graph.setdefault(u,{})[v]=c;graph.setdefault(v,{})[u]=0
    for r,row in enumerate(rows):
        for a,N in enumerate(row):
            leaf=('leaf',r,a);edge(src,leaf,2)
            for y in N:edge(leaf,('column',y),1)
    for y in range(7):edge(('column',y),sink,8)
    flow=0
    while True:
        parent={src:None};queue=deque([src])
        while queue and sink not in parent:
            u=queue.popleft()
            for v,c in graph[u].items():
                if c and v not in parent:parent[v]=u;queue.append(v)
        if sink not in parent:break
        v=sink
        while parent[v] is not None:
            u=parent[v];graph[u][v]-=1;graph[v][u]+=1;v=u
        flow+=1
    selected=tuple(tuple(tuple(y for y in N if graph[('leaf',r,a)][('column',y)]==0) for a,N in enumerate(row)) for r,row in enumerate(rows))
    return flow,selected

def cut_audit(rows):
    values=[]
    for mask in range(128):
        U={y for y in range(7) if mask>>y&1}
        cap=8*len(U)+sum(min(2,len(set(N)-U)) for row in rows for N in row)
        values.append(cap)
    return min(values),tuple(min(values[mask] for mask in range(128) if mask.bit_count()==k) for k in range(8))

def construct_common_law(rows,root_digits=(1,2,3,4),child_digits=None):
    rows,root_digits,child_digits=normalize(rows,root_digits,child_digits)
    pair_degree=Counter(y for row in rows for N in row if len(N)==2 for y in N)
    s=max(pair_degree.values(),default=0)
    if s<=8:
        mode='flow_uniform';flow,selected=select_by_flow(rows)
        require(flow==24,'the exact-pair cut condition supplies flow 24')
        require(all(len(pair)==2 for row in selected for pair in row),'the flow selects two actual points at every child')
        q=2;k=h=exception=1;center=None;cases=None
    else:
        center=min(y for y in pair_degree if pair_degree[y]==s)
        require(sum(d>=9 for d in pair_degree.values())==1,'the high exact-pair column is unique')
        selected=tuple(tuple(N if len(N)==2 and center in N else tuple(y for y in N if y!=center)[:2] for N in row) for row in rows)
        require(all(len(pair)==2 for row in selected for pair in row),'every exceptional child has two actual noncenter neighbors')
        require(sum(center in pair for row in selected for pair in row)==s,'selected center incidence equals original exact-pair degree')
        k,h,exception=(9,11,10) if s==9 else (4,6,5)
        q=k+h;mode='degree_nine' if s==9 else 'heavy'
        for y in range(7):
            if y!=center:
                require(sum(any(len(N)==2 and set(N)=={center,y} for N in row) for row in rows)<=1,'each original spoke endpoint belongs to one root')
        cases=({'b=d=center':1163,'b=center,d=private':1121,'b=private,d=center':1049,'b=d=private':1171,'b,d=distinct_private':1083} if s==9 else
               {'b=d=center':594,'b=center,d=private':592,'b=private,d=center':514,'b=d=private':596,'b,d=distinct_private':548})
    weights={}
    for r,row,pairs,digits in zip(root_digits,rows,selected,child_digits):
        for a,N,pair in zip(digits,row,pairs):
            require(set(pair)<=set(N),'selection remains in the original neighborhood')
            for y in pair:
                weights[r,a,y]=1 if center is None else k if y==center else h if center in pair else exception
    denominator=12*q
    require(len(weights)==24 and all(w>0 for w in weights.values()) and sum(weights.values())==denominator,'24 supported positive atoms with exact total mass')
    roots=Counter();leaves=Counter();columns=Counter();root_columns=Counter()
    for (r,a,y),w in weights.items():
        roots[r]+=w;leaves[r,a]+=w;columns[y]+=w;root_columns[r,y]+=w
    require(set(roots.values())=={3*q} and set(leaves.values())=={q},'root and child masses are fixed simultaneously')
    if center is None:
        require(max(columns.values())<=8 and max(root_columns.values())<=3 and max(weights.values())==1,'all simultaneous uniform-law cell caps')
        coefficients=Counter(lcm(m,n) for m,n in product(LABELS,repeat=2))
        require(coefficients=={1:1,5:3,25:5,7:3,35:9,175:15},'all 36 ordered original-label intersections')
        bound=F(24+3*6+5*2+3*8+9*3+15,24)
        require(bound==F(59,12),'uniform common-law bound')
    else:
        center_cap=9 if s==9 else 12;exceptions=3 if s==9 else 2
        for y in range(7):
            require(columns[y]<=(center_cap*k if y==center else 3*h+exceptions*exception),'shared global-column mass')
            require(all(root_columns[r,y]<=(3*k if y==center else 3*h) for r in root_digits),'root-column masses')
            require(all(w<=(k if y==center else h) for (r,a,z),w in weights.items() if z==y),'point masses')
        for (bc,dc,equal),expected in zip(((1,1,1),(1,0,0),(0,1,0),(0,0,1),(0,0,0)),cases.values()):
            Cb=center_cap*k if bc else 3*h+exceptions*exception
            Db=3*k if bc else 3*h;Dd=3*k if dc else 3*h;Mb=k if bc else h;Md=k if dc else h
            computed=26*q+3*Cb+5*Dd+2*Db+2*Mb+2*Md+2*equal*Dd+(11 if equal else 9)*h
            require(computed==expected,'five-case bound retains one common global-seven phase')
        bound=F(max(cases.values()),denominator)
    require(bound<=F(149,30)<5,'uniform theorem bound')
    return dict(rows=rows,selected_pairs=selected,root_digits=root_digits,child_digits=child_digits,weights=weights,denominator=denominator,mode=mode,center=center,max_exact_pair_degree=s,bound=bound,cases=cases)

FIXTURES={
 'one_robust_root_27_points':(((0,1),(0,3),(1,4)),((0,2),)*3,((1,2),)*3,((0,1,2),)*3),
 'four_robust_roots_38_points':(((0,1,2),)*3,((0,1,2),)*3,((0,1,2),)*3,((0,1,2,3,4),(0,1,2),(0,1,2))),
 'mixed_degree_nine_repeated_selected_pair':(((0,1),)*3,((0,2),)*3,((0,3),(0,3),(0,1,4)),((0,4),(1,4),(0,1,2))),
 'mixed_heavy_repeated_selected_pair':(((0,1),)*3,((0,2),)*3,((0,3),(0,3),(0,1,4)),((0,4),(0,4),(1,4))),
 'heavy_rule_attains_bound':(((0,1),)*3,((0,2),)*3,((0,3),(0,3),(1,4)),((0,4),(0,4),(1,5))),
 'three_column_full_source':(((0,1,2),)*3,)*4,
}

def run_controls(exact_gamma):
    results=[]
    for name,rows in FIXTURES.items():
        law=construct_common_law(rows)
        flow,_=select_by_flow(rows);cut,by_size=cut_audit(rows)
        require(flow==cut==min(24,32-law['max_exact_pair_degree']),'exact integral-flow and all-cut formula')
        selected=law['selected_pairs']
        disjoint=all(set(selected[r]).isdisjoint(selected[s]) for r,s in combinations(range(4),2))
        if 'repeated_selected_pair' in name:require(not disjoint,'selected exception-pair reuse is accepted')
        phase=exact_gamma(law)
        if name=='heavy_rule_attains_bound':require(F(phase['exact_gamma'])==F(149,30),'sharpness for this prescribed constructor')
        results.append(dict(name=name,source_points=sum(len(N) for row in rows for N in row),projection=len({y for row in rows for N in row for y in N}),mode=law['mode'],exact_pair_degree=law['max_exact_pair_degree'],flow=flow,minimum_cut_by_size=by_size,selected_pair_sets_disjoint=disjoint,selected_pairs=selected,weights=[[*point,w] for point,w in sorted(law['weights'].items())],denominator=law['denominator'],bound=str(law['bound']),**phase))
    # An actual coordinate permutation preserves each original cylinder family.
    rows=FIXTURES['mixed_heavy_repeated_selected_pair']
    transported=construct_common_law(rows,root_digits=(4,0,3,1),child_digits=((4,2,0),(1,4,3),(2,1,4),(3,0,2)))
    transported_phase=exact_gamma(transported)
    base=next(r for r in results if r['name']=='mixed_heavy_repeated_selected_pair')
    require(transported_phase['exact_gamma']==base['exact_gamma'],'actual root and separate within-root child permutations preserve the complete maximum')
    bad=(((0,1),)*3,((0,1),)*3,((0,2,3),)*3,((0,2,3),)*3)
    rejected=False
    try:construct_common_law(bad)
    except ValueError:rejected=True
    require(rejected,'original pair ownership violation is rejected')
    # The already established Chapter09 calculation needs actual residual provenance.
    C=F(149,30);B5=F(29,24);lam=F(119,960);lift=(C*B5-lam)/(1-lam)
    require(lift==F(16927,2523)<9,'existing conditional five-height arithmetic for H5=2')
    return dict(universal_bound='149/30',scope='four selected roots, three selected children each, neighborhoods of any size at least two, original exact-pair sets disjoint across roots',fixtures=results,actual_digit_transport_control=transported_phase,original_pair_ownership_rejection=True,conditional_five_height_bound=str(lift),conditional_height_scope='requires an actual distinct-label residual at Q0=175; five extension only')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pair-checker',type=Path,default=Path(__file__).with_name('pair_source_common_law.py'),help='existing report-434 checker supplying exact_gamma for finite controls')
    args=parser.parse_args()
    existing=runpy.run_path(str(args.pair_checker))
    print(json.dumps(run_controls(existing['exact_gamma']),indent=2))
if __name__=='__main__':main()
