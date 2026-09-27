#!/usr/bin/env python3
"""General cap-six strong-support flow for a three-point separated weak root.
No rectangle hypothesis on the strong roots. The actual 18-point flow is required.
"""
from collections import deque, Counter
from itertools import product, combinations
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json


def need(ok,msg):
    if not ok:
        raise AssertionError(msg)


def weak_kernel(mask,h):
    p,m,e,f=mask;t=1+p+h+m
    return 4*((t+e+f)**2+2*t*t)


def strong_kernel(mask,n):
    p,m,e,f=mask;t=1+p
    return 3*(6*t*t+(2*t+1)*(n+3*m+2*e+f)
              +2*(m*n+(e+f)*int(n>0)+m*e+m*f+e*f))


def select_points(weak_columns,strong_rows,root_digits=(1,2,3,4),child_digits=None):
    need(len(root_digits)==4 and len(set(root_digits))==4 and
         all(type(r)is int and 0<=r<5 for r in root_digits),'actual four roots')
    if child_digits is None:
        child_digits=((0,1,2),)*4
    need(len(child_digits)==4 and all(len(ds)==3 and len(set(ds))==3 and
         all(type(a)is int and 0<=a<5 for a in ds) for ds in child_digits),'actual distinct children')
    need(len(weak_columns)==3 and all(type(y)is int and 0<=y<7 for y in weak_columns),'three weak columns')
    need(len(strong_rows)==3 and all(len(row)==3 for row in strong_rows),'three strong roots each three children')
    need(all(len(ns)==len(set(ns)) and all(type(y)is int and 0<=y<7 for y in ns)
             for row in strong_rows for ns in row),'literal strong neighborhoods')
    U=set(weak_columns);graph={};original=[];point_edges=[]
    def edge(u,v,c):
        graph.setdefault(u,{})[v]=c;graph.setdefault(v,{}).setdefault(u,0)
        original.append((u,v,c))
    for r,ds,row in zip(root_digits[1:],child_digits[1:],strong_rows):
        for a,ns in zip(ds,row):
            leaf=('leaf',r,a);edge(('s',),leaf,2)
            for y in ns:
                if y not in U:
                    edge(leaf,('col',y),1);point_edges.append((r,a,y))
    for y in range(7):
        edge(('col',y),('t',),6)
    value=0
    while True:
        prev={('s',):None};q=deque([('s',)])
        while q and ('t',) not in prev:
            u=q.popleft()
            for v,c in graph[u].items():
                if c>0 and v not in prev:
                    prev[v]=u;q.append(v)
        if ('t',) not in prev:
            cut=sum(c for u,v,c in original if u in prev and v not in prev)
            need(cut==value,'integral flow/cut agreement')
            break
        v=('t',)
        while prev[v] is not None:
            u=prev[v];graph[u][v]-=1;graph[v][u]+=1;v=u
        value+=1
    points=[p for p in point_edges if graph[('leaf',p[0],p[1])][('col',p[2])]==0]
    need(len(points)==value,'point extraction')
    if value<18:
        return dict(flow=value,selected=points,cut=cut,feasible=False)
    need(Counter((r,a) for r,a,y in points)=={(r,a):2 for r,ds in zip(root_digits[1:],child_digits[1:]) for a in ds},'two points per strong child')
    need(max(Counter(y for r,a,y in points).values())<=6,'global strong column cap six')
    weights={(root_digits[0],a,y):4 for a,y in zip(child_digits[0],weak_columns)}
    weights.update({p:3 for p in points})
    need(len(weights)==21 and sum(weights.values())==66,'actual supported probability')
    return dict(flow=value,feasible=True,weights=weights,denominator=66,
                root_digits=root_digits,child_digits=child_digits,bound=F(5),
                weak_columns=tuple(weak_columns),selected_strong=points)


def source_bad(rows):
    return [{p for p in combinations(range(7),2)
             if sum(bool(set(ns)-set(p)) for ns in row)<3} for row in rows]


def exact_checker():
    p=Path(__file__).with_name('pair_source_common_law.py')
    need(p.is_file(),'preceding exact_gamma oracle available')
    spec=importlib.util.spec_from_file_location('preceding_pair_law',p)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module.exact_gamma


def main():
    profile_results=[]
    for hit in (1,0):
        ns_values=[(0,0,0)] if hit else [ns for ns in product(range(4),repeat=3) if sum(ns)<=6]
        best=-1;witness=None;count=0
        for allocation in product(range(4),repeat=4):
            masks=[tuple(int(allocation[j]==r) for j in range(4)) for r in range(4)]
            for ns in ns_values:
                value=weak_kernel(masks[0],hit)+sum(strong_kernel(masks[r+1],ns[r]) for r in range(3))
                count+=1
                if value>best:
                    best=value;witness=(allocation,ns)
        need(best==(326 if hit else 330),'general shared-column profile bound')
        profile_results.append(dict(weak_hit=hit,numerator=best,witness=witness,finite_checks=count))
    strong_rows=(((0,1),(0,2),(0,1)),((0,3),(1,3),(0,3)),((1,2),(2,3),(1,2)))
    checker=exact_checker();consumers=[]
    for weak_columns in ((4,5,6),(4,4,4)):
        law=select_points(weak_columns,strong_rows,root_digits=(4,1,3,0),
                          child_digits=((4,0,2),(3,1,4),(2,0,3),(1,4,0)))
        need(law['feasible'],'actual 18-point strong flow')
        rows=tuple((y,) for y in weak_columns),*strong_rows
        bad=source_bad(rows)
        need(all(bad[r].isdisjoint(bad[s]) for r,s in combinations(range(4),2)),'original source admissible')
        need(len({y for row in rows for ns in row for y in ns})>=5,'original five-column projection')
        need(all(len(set(row))>1 for row in strong_rows),'strong roots are not rectangular pair blocks')
        column_counts=Counter(y for r,a,y in law['selected_strong'])
        need(tuple(column_counts[y] for y in range(4))==(5,5,4,4),'reported actual strong column counts')
        checked=checker(law)
        consumers.append(dict(weak_columns=weak_columns,strong_rows=strong_rows,
                             roots=law['root_digits'],children=law['child_digits'],
                             flow=law['flow'],selected=law['selected_strong'],
                             strong_column_counts=dict(sorted(column_counts.items())),
                             weights=[(*p,w) for p,w in sorted(law['weights'].items())],
                             denominator=66,general_bound='5',**checked))
    failure_rows=(((0,1,2),)*3,((3,4),)*3,((3,5),)*3)
    failure_weak=(0,1,2)
    failed=select_points(failure_weak,failure_rows)
    rows=tuple((y,) for y in failure_weak),*failure_rows
    bad=source_bad(rows)
    need(all(bad[r].isdisjoint(bad[s]) for r,s in combinations(range(4),2)),'failed extraction is still an admissible source')
    need(len({y for row in rows for ns in row for y in ns})==6,'six source columns')
    need(sum(not b for b in bad)==1,'one robust root only')
    need(not failed['feasible'] and failed['flow']==12,'outside-U extraction genuinely fails')
    print(json.dumps(dict(bound='5',profiles=profile_results,consumers=consumers,
                          extraction_boundary=dict(weak=failure_weak,strong=failure_rows,
                              points=sum(len(ns) for row in rows for ns in row),bad=[sorted(b) for b in bad],
                              maxflow=failed['flow'],robust_roots=1,
                              scope='Only the separated extraction is refuted, not source-law existence.')),indent=2))


if __name__=='__main__':
    main()
