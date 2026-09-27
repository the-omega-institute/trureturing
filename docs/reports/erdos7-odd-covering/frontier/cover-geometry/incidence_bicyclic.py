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


CERTIFICATE = 'certificates/source_norms/cover-geometry/incidence_bicyclic.json'
SOURCES = ('certificate_io.py', 'problem-details/48-incidence-forests-with-arbitrary-original-heights.md', 'problem-details/49-incidence-pseudoforests-with-arbitrary-original-heights.md', 'problem-details/51-incidence-bicyclic-components-with-arbitrary-original-heights.md', '../../../Library/Arith/balister2018covering.md')


def require(ok,msg):
    if not ok: raise ValueError(msg)


def d(p): return 1-F(1,p-1)-F(4*p,3*(p-1)*(p*p-1))
def b(p): return 1/((p-1)*d(p))


S=sum((b(p)**2 for p in (5,7,11,13)),F(0))+(1/d(15))**2*(F(1,196)+F(1,28))
require(S==F(11181700024618215281126396,45205949340120622379111289)<F(1,4), 'complete odd-prime square bound')
require(d(15)==F(723,784), 'monotone tail density at 15')
B3=F(18,17)
small=(5,7,11,13,17)
f=lambda x:B3*x-x*x/2
fs=[f(b(p)) for p in small]
require(all(fs[i]>fs[i+1] for i in range(4)), 'ordered pure-pair charges')
require(F(288,7225)<fs[-1], 'private-group adjusted charge')
require((b(5)**2+b(7)**2)/34<fs[-1], 'higher-rank retained adjusted charge')
case_bounds={'no3':F(1,4)+b(5)**2}
for degree in range(1,5):
    case_bounds['five_nonleaf_d'+str(degree)]=F(1,4)+F(4-degree,2)*b(5)**2+sum(fs[:degree])
for degree in range(1,6):
    case_bounds['five_leaf_d'+str(degree)]=F(1,4)-b(5)**2/2+F(5-degree,2)*b(7)**2+sum(fs[:degree])
require(all(x<F(49,50) for x in case_bounds.values()), 'all bicyclic core cases')
require(all(fs[i]>b(5)**2/2 for i in (1,2,3)), 'nonleaf degree monotonicity')
require(all(fs[i]>b(7)**2/2 for i in (1,2,3,4)), 'leaf degree monotonicity')


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
    require(edge_count-len(graph)+1==2,'exactly two independent incidence cycles')
    alive=set(graph);degree={v:len(graph[v]) for v in graph}
    leaves=deque(v for v in graph if degree[v]<=1)
    while leaves:
        v=leaves.popleft()
        if v not in alive:continue
        alive.remove(v)
        for w in graph[v]&alive:
            degree[w]-=1
            if degree[w]<=1:leaves.append(w)
    require(alive and all(len(graph[v]&alive)>=2 for v in alive),'literal nonempty two-core')
    retained=set(alive);meetings={}
    for terminal in ((3,5) if 3 in P else ()):
        if terminal not in P or ('p',terminal) in retained:continue
        queue=deque([('p',terminal)]);prev={('p',terminal):None};meeting=None
        while queue:
            v=queue.popleft()
            if v in retained:
                meeting=v;break
            for w in graph[v]:
                if w not in prev:prev[w]=v;queue.append(w)
        require(meeting is not None,'small-prime path reaches retained core')
        meetings[str(terminal)]=meeting[0]
        v=meeting
        while v is not None:retained.add(v);v=prev[v]
    rd={v:len(graph[v]&retained) for v in retained}
    require(sum(rd.values())-2*len(retained)==2,'exact bicyclic Euler excess')
    require(all(n>=2 or v in {('p',3),('p',5)} for v,n in rd.items()),'only terminal small primes may be leaves')
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
    if 3 in K:
        require(F(len(domains[3]),len(X[3]))>=F(17,36),'missing-five domain refund')
    core_points=list(product(*(domains[p] for p in K)))
    bad_core={s:set() for s in core};good=[];core_fee=F(0)
    for s in core:
        C=tuple(p for p in s if p in K);T=tuple(p for p in s if p not in K)
        require(len(C)>=2,'all retained-support shapes explicit')
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
    require(actual_loss<=core_fee<F(49,50),'same actual core union and all-group budget')
    bound=50*4**(len(K)+len(groups))*prod(p-1 for p in P if p not in K)
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
                two_core_prime_count=sum(v[0]=='p' for v in alive),
                path_meetings=meetings,retained_prime_degrees={str(p):rd['p',p] for p in K},
                max_original_rank=max(map(len,groups)),
                retained_support_ranks=sorted(len(set(s)&set(K)) for s in core),
                original_survivors=safe_count,generated_points=generated,
                core_source_points=len(core_points),good_core_points=len(good),
                actual_core_loss=str(actual_loss),same_source_union_bound=str(core_fee),
                full_probability=str(mass),maximum_density=str(maxdensity),bound=bound)



def calculate(base):
    P=[3,5,7,11,13]
    theta=[label({p:1},{p:0}) for p in P]
    theta += [label({p:1 for p in E},{p:1 for p in E}) for E in ((3,5),(3,5,7),(3,5,11,13))]
    branch=[label({p:1},{p:0}) for p in P]
    branch += [label({p:1 for p in E},{p:1 for p in E}) for E in ((3,7,11,13),(7,11),(7,13),(3,5))]
    P6=[3,5,7,11,13,17]
    figure=[label({p:1},{p:0}) for p in P6]
    figure += [label({p:1 for p in E},{p:1 for p in E}) for E in ((3,7),(7,11),(11,3),(3,13),(13,17),(17,3),(3,5))]
    no3primes=[5,7,11,13,17]
    no3=[label({p:1},{p:0}) for p in no3primes]
    no3 += [label({p:1 for p in E},{p:1 for p in E}) for E in ((5,7),(5,7,11),(5,7,13,17))]
    barbell=[label({p:1},{p:0}) for p in P6]
    barbell += [label({p:1 for p in E},{p:1 for p in E}) for E in ((3,5),(3,5,7),(5,11),(11,13),(11,13,17))]
    result=dict(result='PASS',scope='Exact scalar inequalities and actual-family checks; general proof is separate.',
                square_sum=str(S),scalar_cases={k:str(v) for k,v in case_bounds.items()},
                cases=[analyze('theta_three_distinct_supports_same_pair',{p:1 for p in P},theta),
                       analyze('small_prime_path_meets_branched_support',{p:1 for p in P},branch),
                       analyze('figure_eight_with_five_leaf_and_degree_five_root',{p:1 for p in P6},figure),
                       analyze('theta_without_three',{p:1 for p in no3primes},no3),
                       analyze('barbell_with_private_children',{p:1 for p in P6},barbell)])
    result['schema'] = 'incidence-bicyclic-v1'
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
