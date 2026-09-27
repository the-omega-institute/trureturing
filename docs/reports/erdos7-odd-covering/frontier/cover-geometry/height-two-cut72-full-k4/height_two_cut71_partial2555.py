#!/usr/bin/env python3
"""Exact actual2555 cut71 controls for the weighted public/private law.

Both sorted private shapes, finite/whole public cuts, and a whole private
cost3 are exercised. The support theorem is ordinary mathematics in449;
these finite controls do not establish unrestricted odd noncoverage.
"""
from collections import defaultdict
from fractions import Fraction as Q
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import json

N = (4, 5, 5, 5)
DIVISORS = (1, 5, 7, 25, 35, 49, 175, 245, 1225)
CAPS = tuple(map(Q, (1,))) + (Q(18,55), Q(13,55), Q(6,55), Q(13,55),
                              Q(13,165), Q(3,55), Q(13,275), Q(13,275))


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load_module(path, name):
    spec = spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'existing helper module')
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def weighted_cut_checks():
    A, B, W = (15,25,25,25), (15,39,39,39), 65
    slacks = [[], [], []]
    for size in range(5):
        for subset in combinations(range(4), size):
            outside = sum(A[r] for r in range(4) if r not in subset)
            if size <= 1:
                slacks[0].append(Q(outside-W,275))
            else:
                slacks[1].append((outside + sum(Q(B[r],2) for r in subset)-W)/275)
                for omitted in subset:
                    slacks[2].append(Q(outside + sum(B[r] for r in subset if r != omitted)-W,275))
    require(tuple(map(len,slacks)) == (5,11,28), 'all44 weighted cuts')
    require(tuple(map(min,slacks)) == (0,Q(1,275),0), 'exact cut slacks')
    return {'family_sizes':list(map(len,slacks)), 'minimum_slacks':list(map(str,map(min,slacks)))}


def template(shape, whole_public, whole_private):
    require(shape in ('03','12') and (not whole_private or shape=='03'), 'private shape')
    active = (2,5,5,5)
    rowleaves = ({0,1},{1,2},{2,3},{3,4}) if whole_public else ({0,1},{1,2},{0,2},{0,1,2})
    require(all(len(rowleaves[r] | rowleaves[s]) >= 3 for r,s in combinations(range(4),2)), 'actual public pair union')
    private = {(r,c):{(r,c)} for r in (1,2,3) for c in range(5)}
    if shape=='03':
        private[0,0] = set()
        private[0,1] = {(4,h) for h in range(7 if whole_private else 3)}
    else:
        private[0,0], private[0,1] = {(4,0)}, {(4,1),(4,2)}
    fibres = {(r,c):({(0,h) for h in rowleaves[r]} | private[r,c]
                       if c<active[r] else set(product(range(7),repeat=2)))
              for r in range(4) for c in range(N[r])}
    source = {(r,c,g,h) for (r,c), ys in fibres.items() for g,h in ys}
    return {'name':shape+('_public_whole' if whole_public else '_public_finite')+('_private_whole' if whole_private else ''),
            'active_counts':active, 'public_columns':(0,) if whole_public else (),
            'public_leaves':() if whole_public else ((0,0),(0,1),(0,2)),
            'private':private, 'fibres':fibres, 'source':source,
            'whole_private':{(0,1)} if whole_private else set(),
            'rowleaves':rowleaves}


def law_for(item, dinic):
    # Scale the public law by825: total195, root45/75, root-leaf15/39,
    # and public-leaf65. This is ONE flow using the actual pair projections.
    graph = dinic(13)
    refs = {}
    for r in range(4):
        graph.add(11,r,45 if r==0 else 75)
        for h in sorted(item['rowleaves'][r]):
            refs[r,h] = graph.add(r,4+h,15 if r==0 else 39)
    for h in range(7):
        graph.add(4+h,12,65)
    require(graph.flow(11,12,195)==195, 'one supported weighted public flow')
    public = {point:Q(cap-graph.g[u][j][1],825) for point,(u,j,cap) in refs.items()}
    require(sum(public.values())==Q(65,275), 'public total')
    for r in range(4):
        require(sum(v for (rr,h),v in public.items() if rr==r) <= Q(15 if r==0 else 25,275), 'public root budget')
    for h in range(7):
        require(sum(v for (r,hh),v in public.items() if hh==h) <= Q(65,825), 'public leaf budget')
    require(all(v<=Q(15 if r==0 else 39,825) for (r,h),v in public.items()), 'public joint budget')
    law = defaultdict(Q)
    for (r,h),v in public.items():
        choices = [(0,1)] if r==0 else list(combinations(range(5),3))
        # Row projections in these fixtures are invariant under restrictions.
        # Marginal averaging equals averaging the full ten-cubed product.
        for cs in choices:
            point = (r,min(cs),0,h)
            require(point in item['source'], 'actual selected public owner')
            law[point] += v / len(choices)
    for r in (1,2,3):
        for c in range(5):
            law[r,c,r,c] += Q(13,275)
    private_gap = sorted((0,c,g,h) for c in (0,1) for g,h in item['private'][0,c])[:3]
    require(len(private_gap)==3 and len({p[2:] for p in private_gap})==3, 'three actual private gap leaves')
    for point in private_gap:
        law[point] += Q(5,275)
    return {p:v for p,v in law.items() if v}, [[r,h,str(v)] for (r,h),v in sorted(public.items()) if v]


def check_law(item, law):
    require(set(law)<=item['source'] and all(v>0 for v in law.values()) and sum(law.values())==1, 'single actual probability')
    require(all(not (r==0 and c>=2) for r,c,g,h in law), 'inactive children retained in source only')
    def crt(p):
        r,c,g,h = p
        x,y = r+5*c,g+7*h
        return x+25*((y-x)*pow(25,-1,49)%49)
    maxima, total = {},0
    for d,cap in zip(DIVISORS,CAPS):
        masses = defaultdict(Q)
        for point,v in law.items():
            masses[crt(point)%d] += v
        for a in range(d):
            require(masses[a]<=cap, 'original numerical cylinder cap')
            total+=1
        maxima[d]=max(masses.values())
    upper = sum(maxima[lcm(d,e)] for d,e in product(DIVISORS,repeat=2))
    capmap=dict(zip(DIVISORS,CAPS))
    theoretical=sum(capmap[lcm(d,e)] for d,e in product(DIVISORS,repeat=2))
    require(total==1767 and upper<=theoretical==Q(127,15)<9, 'all81 ordered LCM pairs')
    return {'atoms':[[*p,str(v)] for p,v in sorted(law.items())], 'cylinders_checked':total,
            'ordered_pairs':81, 'cylinder_maxima':{str(d):str(v) for d,v in maxima.items()},
            'measured_lcm_upper':str(upper), 'theoretical_lcm_upper':str(theoretical)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-module', type=Path, default=Path(__file__).with_name('height_two_cut71_actual_sources.py'))
    parser.add_argument('--base-module', type=Path, default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    helper=load_module(args.source_module,'_cut71_actual_sources')
    dinic=load_module(args.base_module,'_cut71_existing_dinic').Dinic
    controls=[]
    for whole_public in (False,True):
        for shape,whole_private in (('03',False),('03',True),('12',False)):
            item=template(shape,whole_public,whole_private)
            law, public=law_for(item,dinic)
            controls.append({'name':item['name'], 'source_points':len(item['source']),
                             'source':sorted(item['source']), 'whole_private':sorted(item['whole_private']),
                             'public_columns':item['public_columns'], 'public_leaves':item['public_leaves'],
                             'public_flow':public, **helper.literal_checks(item),
                             'network':helper.actual_network(item,dinic), 'law':check_law(item,law)})
    require(len(controls)==6, 'six mixed-law controls')
    out={'weighted_cuts':weighted_cut_checks(), 'controls':controls,
         'scope':'Six actual2555 cut71 controls; both private shapes and finite/whole public/private cuts. Exact finite witnesses and weighted-cut checks, not the universal support proof or an unrestricted odd-covering result. No Lean verification.'}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({c['name']:{'points':c['source_points'],'gamma':c['law']['measured_lcm_upper']} for c in controls}))


if __name__=='__main__':
    main()
