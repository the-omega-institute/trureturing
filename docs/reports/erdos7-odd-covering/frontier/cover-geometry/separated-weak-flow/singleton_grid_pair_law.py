#!/usr/bin/env python3
"""Uniform actual law on weak matching U, one 3xU grid and two external pair blocks.
General affine proof plus exact shared-phase checks; no source-law optimization.
"""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
import importlib.util
import json


def need(ok,msg):
    if not ok:
        raise AssertionError(msg)


def kernel(kind,mask,h):
    p,m,e,f=mask;t=1+p;c=h+m
    if kind=='weak':
        return (t+c+e+f)**2+2*t*t
    if kind=='grid':
        return (t+c+e+f)**2+2*(t+c)**2+2*(t+e)**2+4*t*t
    need(kind=='pair','known root block')
    return (t+c+e+f)**2+2*(t+c)**2+(t+e)**2+2*t*t


def affine(kind,h):
    if kind=='weak':
        return 3+3*h,(12+2*h,6+2*h,6+2*h,6+2*h)
    if kind=='grid':
        return 9+9*h,(34+6*h,14+6*h,14+2*h,6+2*h)
    need(kind=='pair','known root block')
    return 6+9*h,(24+6*h,14+6*h,10+2*h,6+2*h)


def direct_local(kind,mask,h):
    p,m,e,f=mask
    points=([(a,a) for a in range(3)] if kind=='weak'
            else [(a,y) for a in range(3) for y in range(3 if kind=='grid' else 2)])
    cols=sorted({y for a,y in points});b=0 if h else -1
    return max(sum((1+p+(y==b)+m*(y==d)+e*(a==ea)+f*((a,y)==fp))**2 for a,y in points)
               for d,ea,fp in product(cols,range(3),points))


def construct_law(weak_columns,grid_neighborhoods,pair_columns,
                  root_digits=(1,2,3,4),child_digits=None):
    need(len(weak_columns)==3 and len(set(weak_columns))==3 and
         all(type(y)is int and 0<=y<7 for y in weak_columns),'three different weak columns')
    need(len(root_digits)==4 and len(set(root_digits))==4 and
         all(type(r)is int and 0<=r<5 for r in root_digits),'four actual root digits')
    if child_digits is None:
        child_digits=((0,1,2),)*4
    need(len(child_digits)==4 and all(len(ds)==3 and len(set(ds))==3 and
         all(type(a)is int and 0<=a<5 for a in ds) for ds in child_digits),'three actual children per root')
    U=set(weak_columns)
    need(len(grid_neighborhoods)==3 and all(len(ns)==len(set(ns)) and
         all(type(y)is int and 0<=y<7 for y in ns) and U<=set(ns)
         for ns in grid_neighborhoods),'actual grid children contain U')
    need(len(pair_columns)==2,'two external pair blocks')
    pairs=[]
    for pair in pair_columns:
        need(len(pair)==2 and len(set(pair))==2 and all(type(y)is int and 0<=y<7 for y in pair),'two actual columns')
        need(U.isdisjoint(pair),'external pair avoids U')
        pairs.append(tuple(sorted(pair)))
    need(pairs[0]!=pairs[1],'distinct external pairs')
    weights={(root_digits[0],a,y):1 for a,y in zip(child_digits[0],weak_columns)}
    weights.update({(root_digits[1],a,y):1 for a in child_digits[1] for y in weak_columns})
    for r,ds,pair in zip(root_digits[2:],child_digits[2:],pairs):
        weights.update({(r,a,y):1 for a in ds for y in pair})
    need(len(weights)==24 and sum(weights.values())==24,'one actual uniform law')
    return dict(weights=weights,denominator=24,bound=F(5),root_digits=root_digits,
                child_digits=child_digits,weak_columns=tuple(weak_columns),pair_columns=tuple(pairs))


def oracle():
    path=Path(__file__).with_name('pair_source_common_law.py')
    need(path.is_file(),'existing original-phase checker available')
    spec=importlib.util.spec_from_file_location('pair_law',path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module.exact_gamma


def main():
    kinds=('weak','grid','pair')
    for kind,h,mask in product(kinds,(0,1),product((0,1),repeat=4)):
        value=kernel(kind,mask,h)
        need(value==direct_local(kind,mask,h),'closed kernel equals complete local phase maximum')
        base,prices=affine(kind,h)
        need(value<=base+sum(a*b for a,b in zip(mask,prices)),'root affine bound')
    profiles=[]
    for inU in (1,0):
        hits=(inU,inU,1-inU,1-inU);types=('weak','grid','pair','pair')
        bases,prices=zip(*(affine(kind,h) for kind,h in zip(types,hits)))
        common=tuple(max(row[j] for row in prices) for j in range(4))
        affine_bound=sum(bases)+sum(common)
        need(affine_bound==(120 if inU else 118),'ordinary affine bound')
        best=-1;arg=None
        for allocation in product(range(4),repeat=4):
            masks=[tuple(int(allocation[j]==r) for j in range(4)) for r in range(4)]
            value=sum(kernel(kind,mask,h) for kind,mask,h in zip(types,masks,hits))
            if value>best:
                best,arg=value,allocation
        need(best==(120 if inU else 112),'exact shared-column mask maximum')
        profiles.append(dict(inU=inU,bases=bases,common_prices=common,affine_bound=affine_bound,exact_max=best,allocation=arg))
    check=oracle();consumers=[]
    for pairs,roots,children in [(((3,4),(3,5)),(1,2,3,4),((0,1,2),)*4),
                               (((3,4),(5,6)),(4,0,3,1),((3,1,4),(2,4,0),(1,0,3),(4,2,1)))]:
        law=construct_law((0,1,2),((0,1,2),)*3,pairs,roots,children)
        checked=check(law)
        need(F(checked['exact_gamma'])==5,'uniform law value five is attained')
        rows=[[(y,) for y in (0,1,2)],[(0,1,2)]*3,[pairs[0]]*3,[pairs[1]]*3]
        bad=[{p for p in combinations(range(7),2) if sum(bool(set(ns)-set(p)) for ns in row)<3} for row in rows]
        need(all(bad[r].isdisjoint(bad[s]) for r,s in combinations(range(4),2)),'original admissible source')
        need(sum(not b for b in bad)==1,'one robust root')
        need(len({y for row in rows for ns in row for y in ns})>=6,'six or seven columns')
        consumers.append(dict(pair_columns=pairs,root_digits=roots,child_digits=children,
                              points=[(*p,w) for p,w in sorted(law['weights'].items())],bad_pairs=[sorted(b) for b in bad],
                              bound='5',**checked))
    print(json.dumps(dict(general_bound='5',ordinary_affine_proof=profiles,actual_consumers=consumers),indent=2))


if __name__=='__main__':
    main()
