#!/usr/bin/env python3
"""Exact scalar certificate and actual original-label joint-law fixtures."""
from fractions import Fraction as F
from itertools import product
from collections import deque
from math import prod
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys
sys.dont_write_bytecode = True


CERTIFICATE = 'certificates/source_norms/cover-geometry/incidence_unicyclic.json'
SOURCES = ('certificate_io.py', 'problem-details/48-incidence-forests-with-arbitrary-original-heights.md', 'problem-details/49-incidence-pseudoforests-with-arbitrary-original-heights.md', '../../../Library/Arith/balister2018covering.md')


def require(ok,msg):
    if not ok: raise ValueError(msg)


def d(p): return 1-F(1,p-1)-F(4*p,3*(p-1)*(p*p-1))
def b(p): return 1/((p-1)*d(p))


S=sum((b(p)**2 for p in (5,7,11,13)),F(0))+(1/d(15))**2*(F(1,196)+F(1,28))
require(S==F(11181700024618215281126396,45205949340120622379111289)<F(1,4), 'complete odd-prime square bound')
require(d(15)==F(723,784), 'monotone tail density at 15')
case_bounds={
    'no3':F(1,4),
    'cycle3_has5':F(18,17)*(b(5)+b(7))+F(1,4),
    'cycle3_no5':2*(b(7)+b(11))+F(1,4),
    'double_cycle3_5':2*F(18,17)*b(5),
    'double_cycle3_large':4*b(7),
    'path3_has5':F(18,17)*b(5)+F(3,8),
    'path3_no5':2*b(7)+F(3,8),
}
require(all(x<F(9,10) for x in case_bounds.values()), 'all exhaustive scalar core cases')


def label(ex,res):
    require(set(ex)==set(res),'complete original CRT residues')
    return dict(ex=ex,res=res,d=prod(p**e for p,e in ex.items()))


def analyze(name,heights,labels):
    P=sorted(heights)
    X={p:range(p**heights[p]) for p in P}
    period=prod(len(X[p]) for p in P)
    require(len({z['d'] for z in labels})==len(labels),'distinct original moduli')
    pure={p:[] for p in P}; groups={}
    for z in labels:
        require(all(1<=e<=heights[p] for p,e in z['ex'].items()),'complete original heights')
        s=tuple(sorted(z['ex']))
        if len(s)==1:pure[s[0]].append(z)
        else:groups.setdefault(s,[]).append(z)
    graph={('p',p):set() for p in P}
    for s in groups:
        graph['s',s]={('p',p) for p in s}
        for p in s:graph['p',p].add(('s',s))
    visited=set(); todo=[next(iter(graph))]
    while todo:
        v=todo.pop()
        if v in visited:continue
        visited.add(v);todo.extend(graph[v]-visited)
    require(len(visited)==len(graph),'connected fixture')
    edge_count=sum(map(len,graph.values()))//2
    require(edge_count-len(graph)+1==1,'exactly one incidence cycle')
    alive=set(graph);degree={v:len(graph[v]) for v in graph}
    leaves=deque(v for v in graph if degree[v]<=1)
    while leaves:
        v=leaves.popleft()
        if v not in alive:continue
        alive.remove(v)
        for w in graph[v]&alive:
            degree[w]-=1
            if degree[w]<=1:leaves.append(w)
    require(alive and all(len(graph[v]&alive)==2 for v in alive),'literal unique cycle')
    retained=set(alive);meeting=None
    if 3 in P and ('p',3) not in retained:
        queue=deque([('p',3)]);prev={('p',3):None}
        while queue:
            v=queue.popleft()
            if v in retained:
                meeting=v;break
            for w in graph[v]:
                if w not in prev:prev[w]=v;queue.append(w)
        require(meeting is not None,'3 path reaches core')
        v=meeting
        while v is not None:retained.add(v);v=prev[v]
    K=sorted(v[1] for v in retained if v[0]=='p')
    core={v[1] for v in retained if v[0]=='s'}
    child={p:[] for p in P};parent={};seen=set()

    def orient(p,incoming=None):
        require(p not in seen,'each prime introduced once');seen.add(p)
        for _,s in graph['p',p]:
            if s in core or s==incoming:continue
            require(s not in parent,'unique parent support')
            parent[s]=p;T=tuple(r for r in s if r!=p)
            child[p].append((s,T))
            for r in T:orient(r,s)
    for p in K:orient(p)
    for s in core:
        for r in s:
            if r not in K:orient(r,s)
    require(seen==set(P),'complete off-core orientation')
    domains={};allowed={};exception={}

    def matches(z,point,coords=None):
        return all(point[p]%p**z['ex'][p]==z['res'][p]
                   for p in (z['ex'] if coords is None else coords))

    def build(p):
        if p in domains:return
        forbidden=set()
        for s,T in child[p]:
            for r in T:build(r)
            c=prod(F(1,r-1) for r in T);D=prod(r-3 for r in T)
            B=set()
            for x in X[p]:
                point={p:x}
                active=[z for z in groups[s] if matches(z,point,[p])]
                L=sum((prod(F(1,r**z['ex'][r]) for r in T) for z in active),F(0))
                if L>=(D-F(1,4))*c:B.add(x);continue
                count=0
                for vals in product(*(domains[r] for r in T)):
                    point.update(zip(T,vals))
                    count+=not any(matches(z,point) for z in active)
                require(F(count,prod(len(X[r]) for r in T))>c/4,'hanging simultaneous volume')
                allowed[s,(x,)]=count
            exception[s]=B;forbidden|=B
        domains[p]={x for x in X[p]
                    if x not in forbidden and not any(matches(z,{p:x}) for z in pure[p])}
        require(F(len(domains[p]),len(X[p]))>=(F(1,4) if p==3 else d(p)), 'actual pruned domain')
    for p in P:build(p)
    if 3 in K and 5 in K:
        require(F(len(domains[3]),len(X[3]))>=F(17,36),'missing-five domain refund')
    core_points=list(product(*(domains[p] for p in K)))
    bad_core={s:set() for s in core};good=[];core_fee=F(0)
    for s in core:
        C=tuple(p for p in s if p in K);T=tuple(p for p in s if p not in K)
        require(len(C) in (2,3),'all retained-support shapes explicit')
        core_fee+=prod(F(1,(p-1))*F(len(X[p]),len(domains[p])) for p in C)/(prod(r-3 for r in T)-F(1,4) if T else 1)
        for cv in product(*(domains[p] for p in C)):
            point=dict(zip(C,cv));active=[z for z in groups[s] if matches(z,point,C)]
            if not T:
                if active:bad_core[s].add(cv)
                continue
            c=prod(F(1,r-1) for r in T);D=prod(r-3 for r in T)
            L=sum((prod(F(1,r**z['ex'][r]) for r in T) for z in active),F(0))
            if L>=(D-F(1,4))*c:bad_core[s].add(cv);continue
            count=0
            for vals in product(*(domains[r] for r in T)):
                point.update(zip(T,vals));count+=not any(matches(z,point) for z in active)
            require(F(count,prod(len(X[r]) for r in T))>c/4,'core simultaneous private volume')
            allowed[s,cv]=count
    for vals in core_points:
        point=dict(zip(K,vals))
        if all(tuple(point[p] for p in s if p in K) not in bad_core[s] for s in core):
            good.append(vals)
    good=set(good)
    actual_loss=1-F(len(good),len(core_points))
    require(actual_loss<=core_fee<F(9,10),'same actual core union and all-group budget')
    bound=10*4**(len(K)+len(groups))*prod(p-1 for p in P if p not in K)
    mass=F(0);maxdensity=F(0);safe_count=generated=0
    for vals in product(*(X[p] for p in P)):
        point=dict(zip(P,vals));safe=not any(matches(z,point) for z in labels)
        safe_count+=safe
        if not safe or not all(point[p] in domains[p] for p in P):continue
        if tuple(point[p] for p in K) not in good:continue
        prob=F(1,len(good))
        for s in groups:
            if s in core:
                C=tuple(p for p in s if p in K)
                if len(C)==len(s):continue
                key=tuple(point[p] for p in C)
            else:key=(point[parent[s]],)
            prob/=allowed[s,key]
        mass+=prob;generated+=1;maxdensity=max(maxdensity,period*prob)
    require(mass==1,'full generated joint probability normalized')
    require(maxdensity<=bound and F(safe_count,period)>=F(1,bound),'uniform complete Haar density')
    return dict(name=name,period=period,labels=len(labels),core_primes=K,
                cycle_prime_count=sum(v[0]=='p' for v in alive),
                path_meets=None if meeting is None else meeting[0],
                max_original_rank=max(map(len,groups)),
                retained_support_ranks=sorted(len(set(s)&set(K)) for s in core),
                original_survivors=safe_count,generated_points=generated,
                core_source_points=len(core_points),good_core_points=len(good),
                actual_core_loss=str(actual_loss),same_source_union_bound=str(core_fee),
                full_probability=str(mass),maximum_density=str(maxdensity),bound=bound)



def calculate(base):
    P=[3,5,7,11,13]
    first=[label({p:1},{p:0}) for p in P]
    first += [label({3:a,5:1},{3:1,5:1}) for a in (1,2)]
    first += [label({3:a,5:1,7:1,11:1},{3:1,5:2,7:1,11:1}) for a in (1,2)]
    first += [label({11:1,13:1},{11:2,13:3})]
    second=[label({p:1},{p:0}) for p in P]
    second += [label({3:1,5:1,7:1},{3:1,5:1,7:1}),
               label({5:1,7:1,11:1,13:1},{5:2,7:2,11:1,13:1})]
    result=dict(result='PASS',scope='Exact scalar inequalities and actual-family checks; general proof is separate.',
                square_sum=str(S),scalar_cases={k:str(v) for k,v in case_bounds.items()},
                cases=[analyze('two_shared_primes_rank_four_and_hanging_edge',{3:2,5:1,7:1,11:1,13:1},first),
                       analyze('ternary_path_meets_cycle_support_vertex',{p:1 for p in P},second)])
    result['schema'] = 'incidence-unicyclic-v1'
    result['source_sha256'] = {p:hashlib.sha256((base/p).read_bytes()).hexdigest() for p in SOURCES}
    result['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('incidence_certificate_io',args.base/'certificate_io.py')
    require(spec is not None and spec.loader is not None, 'readable certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact incidence certificate replay')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
