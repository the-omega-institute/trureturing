#!/usr/bin/env python3
"""Shared-column certificate for one singleton block and three distinct pair blocks.
Exact finite label-allocation kernels; unrestricted original residues retained.
Also checks a dual obstruction to deleting two weak-root children.
"""
from fractions import Fraction as F
from itertools import product, combinations
from collections import Counter
import importlib.util
from pathlib import Path
import json


def need(ok, message):
    if not ok:
        raise AssertionError(message)


MODULI = (1,5,25,7,35,175)


def weak(mask, hit, z):
    p,m,e,f = mask
    t = 1+p+hit+m
    return z*((t+e+f)**2+2*t*t)


def strong(mask, hit, u, v):
    p,m,e,f = mask
    weights = (u,v)
    best = 0
    for d in (0,1):
        ts = [1+p+(hit==y)+m*(d==y) for y in (0,1)]
        value = (3*sum(w*t*t for w,t in zip(weights,ts))
                 +e*sum(w*(2*t+1) for w,t in zip(weights,ts))
                 +f*max(w*(2*(t+e)+1) for w,t in zip(weights,ts)))
        best = max(best,value)
    return best


def direct_strong(mask, hit, u, v):
    p,m,e,f = mask
    return max(sum((u if y==0 else v)*
                   (1+p+(hit==y)+m*(d==y)+e*(a==ea)+f*((a,y)==(fa,fy)))**2
                   for a in range(3) for y in range(2))
               for d,ea,fa,fy in product(range(2),range(3),range(3),range(2)))


def direct_weak(mask, hit, z):
    p,m,e,f = mask
    return max(sum(z*(1+p+hit+m+e*(a==ea)+f*(a==fa))**2 for a in range(3))
               for ea,fa in product(range(3),repeat=2))


def profile_max(z, weights, hitweak, hits):
    best, witness = -1, None
    for allocation in product(range(4),repeat=4):
        masks = [tuple(int(allocation[j]==r) for j in range(4)) for r in range(4)]
        value = weak(masks[0],hitweak,z)+sum(strong(masks[r+1],hits[r],*weights) for r in range(3))
        if value > best:
            best,witness=value,allocation
    return dict(numerator=best,allocation=witness)


def crt(point):
    r,a,y = point
    x=r+5*a
    return x+25*((y-x)*2%7)


def dual_deleted_weak_children():
    # All four roots have exactly three active children.  The original
    # source includes two points at its last weak child to reach five columns.
    rows=(((3,),(3,),(3,4)),((0,1),)*3,((0,2),)*3,((1,2),)*3)
    source=[(r,a,y) for r,row in enumerate(rows,1) for a,ns in enumerate(row) for y in ns]
    pairs=tuple(combinations(range(7),2))
    bad=[{p for p in pairs if sum(bool(set(ns)-set(p)) for ns in row)<3} for row in rows]
    need(all(bad[r].isdisjoint(bad[s]) for r,s in combinations(range(4),2)), 'original source condition')
    need(len(source)==22 and len({y for r,a,y in source})==5,'22 actual points and five columns')
    strong_points=[p for p in source if p[0]!=1]
    weakpoint=(1,0,3)
    retained=[weakpoint]+strong_points
    def price(z,q):
        x,center=crt(z),crt(q)
        return sum(x%m==center%m for m in MODULI)**2
    strong_average=[F(sum(price(z,q) for q in strong_points),18) for z in retained]
    weak_prices=[price(z,weakpoint) for z in retained]
    need(strong_average==[F(1)]+[F(53,9)]*18,'strong-centered average')
    need(weak_prices==[36]+[1]*18,'weak-centered layout')
    mixing=F(44,359)
    dual=[mixing*a+(1-mixing)*b for a,b in zip(weak_prices,strong_average)]
    need(set(dual)=={F(1899,359)},'constant pointwise layout dual')
    need(F(1899,359)-F(46,9)==F(577,3231)>0,'strict recipe obstruction')
    return dict(source=source,retained=retained,weak_layout_probability=str(mixing),
                each_strong_layout_probability=str((1-mixing)/18),
                pointwise_dual=str(dual[0]),gap_above_target=str(F(577,3231)),
                scope='Only laws discarding the other two weak children are refuted.')



def construct_common_law(weak_columns, strong_pairs, root_digits=(1,2,3,4), child_digits=None):
    """One supported law; root 0 is weak, the other roots have pair blocks."""
    need(len(root_digits)==4 and len(set(root_digits))==4 and
         all(type(r) is int and 0<=r<5 for r in root_digits), 'four actual root digits')
    if child_digits is None:
        child_digits=((0,1,2),)*4
    need(len(child_digits)==4 and all(len(ds)==3 and len(set(ds))==3 and
         all(type(a) is int and 0<=a<5 for a in ds) for ds in child_digits), 'actual child digits')
    need(len(weak_columns)==3 and all(type(y) is int and 0<=y<7 for y in weak_columns), 'three actual weak columns')
    need(len(strong_pairs)==3, 'three strong pair blocks')
    pairs=[]
    for pair in strong_pairs:
        need(len(pair)==2 and len(set(pair))==2 and
             all(type(y) is int and 0<=y<7 for y in pair), 'two actual columns in each pair')
        pairs.append(tuple(sorted(pair)))
    need(len(set(pairs))==3, 'distinct strong pairs')
    need(not set(weak_columns)&set(y for pair in pairs for y in pair), 'weak footprint separated from strong columns')
    degree=Counter(y for pair in pairs for y in pair)
    star=max(degree.values())==3
    center=next((y for y,d in degree.items() if d==3),None)
    z=6 if star else 4
    weights={(root_digits[0],a,y):z for a,y in zip(child_digits[0],weak_columns)}
    for r,ds,pair in zip(root_digits[1:],child_digits[1:],pairs):
        for a in ds:
            for y in pair:
                weights[r,a,y]=(4 if y==center else 5) if star else 3
    denominator=99 if star else 66
    need(len(weights)==21 and sum(weights.values())==denominator, 'one normalized 21-point law')
    return dict(weights=weights,denominator=denominator,root_digits=root_digits,
                child_digits=child_digits,weak_columns=tuple(weak_columns),strong_pairs=tuple(pairs),
                mode='star' if star else 'maximum_degree_at_most_two',center=center,
                bound=F(167,33) if star else F(5))


def source_consumer(law):
    source=tuple(law['weights'])
    bad=[]
    for r in law['root_digits']:
        ds=sorted({a for rr,a,y in source if rr==r})
        rows=[{y for rr,aa,y in source if rr==r and aa==a} for a in ds]
        bad.append({p for p in combinations(range(7),2) if sum(bool(ns-set(p)) for ns in rows)<3})
    need(all(bad[r].isdisjoint(bad[s]) for r,s in combinations(range(4),2)), 'actual source bad graphs disjoint')
    need(len({y for r,a,y in source})>=5, 'actual five-column projection')
    weak_r=law['root_digits'][0]
    weak_neighborhoods=[{y for r,aa,y in source if r==weak_r and aa==a} for a in law['child_digits'][0]]
    need(not set.intersection(*weak_neighborhoods), 'weak common-column intersection is empty')
    # Reuse the preceding constructor's exact common-b/root-mask oracle,
    # which reconstructs and checks one literal original phase vector.
    module_path=Path(__file__).with_name('pair_source_common_law.py')
    need(module_path.is_file(), 'preceding exact_gamma implementation available')
    spec=importlib.util.spec_from_file_location('preceding_pair_law',module_path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    checked=module.exact_gamma(law)
    need(F(checked['exact_gamma'])==law['bound'], 'dispersed-weak consumer attains prescribed-law bound')
    return dict(root_digits=law['root_digits'],child_digits=law['child_digits'],
                weak_columns=law['weak_columns'],strong_pairs=law['strong_pairs'],
                mode=law['mode'],denominator=law['denominator'],bound=str(law['bound']),
                points=[(*p,w) for p,w in sorted(law['weights'].items())],
                bad_pairs=[sorted(bs) for bs in bad],**checked)


def main():
    for weights,z in [((3,3),4),((4,5),6)]:
        for mask in product((0,1),repeat=4):
            for hit in (-1,0,1):
                need(strong(mask,hit,*weights)==direct_strong(mask,hit,*weights),'closed strong kernel equals all local phases')
            for hit in (0,1):
                need(weak(mask,hit,z)==direct_weak(mask,hit,z),'closed weak kernel equals all local phases')
    degree2=[profile_max(4,(3,3),1,(-1,-1,-1)),profile_max(4,(3,3),0,(0,0,-1))]
    star=[profile_max(6,(4,5),1,(-1,-1,-1)),profile_max(6,(4,5),0,(0,0,0)),profile_max(6,(4,5),0,(1,-1,-1))]
    need([p['numerator'] for p in degree2]==[326,330],'degree-at-most-two profiles')
    need([p['numerator'] for p in star]==[489,501,480],'star profiles')
    need(F(330,66)==5 and F(501,99)==F(167,33),'profile bounds')
    need(F(46,9)-F(167,33)==F(5,99)>0,'universal strict margin')
    consumers=[source_consumer(construct_common_law((3,4,5),((0,1),(0,2),(1,2)))),
               source_consumer(construct_common_law((4,5,6),((0,1),(0,2),(0,3)),
                   root_digits=(4,2,0,1),child_digits=((4,0,2),(1,4,3),(2,0,4),(3,1,0))))]
    print(json.dumps(dict(actual_dispersed_weak_consumers=consumers,degree_at_most_two=dict(weights=dict(weak=4,strong_each=3),denominator=66,profiles=degree2,bound='5'),
                          star=dict(weights=dict(weak=6,strong_center=4,strong_private=5),denominator=99,profiles=star,bound='167/33'),
                          no_single_weak_point_recipe=dual_deleted_weak_children()),indent=2))


if __name__=='__main__':
    main()
