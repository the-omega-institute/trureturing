#!/usr/bin/env python3
"""One actual common law for the RC74 double-row response construction.

The complete source and original flows are reused from the GE74 fixture JSON.
This checks one actual realization and all1225 coherent centers. Noncoherent
queries use the proved TB.4 bound587 rather than a new exhaustive enumeration.
"""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import hashlib
import json
import runpy


def req(ok,msg):
    if not ok:raise ValueError(msg)


def margins(atom):
    a=defaultdict(Q);b=defaultdict(Q);d=defaultdict(Q)
    r=defaultdict(Q);c=defaultdict(Q);whole_child=defaultdict(Q);whole_fine=defaultdict(Q)
    for (rr,i,g,j),m in atom.items():
        a[rr]+=m;b[g]+=m;d[rr,g]+=m;r[rr,i,g]+=m;c[rr,g,j]+=m
        whole_child[rr,i]+=m;whole_fine[g,j]+=m
    return a,b,d,r,c,whole_child,whole_fine


def charges(atom):
    a,b,d,r,c,whole_child,whole_fine=margins(atom)
    out={}
    for rr,i,g,j in product(range(5),range(5),range(7),range(7)):
        ri=r[rr,i,g];cj=c[rr,g,j]
        z=whole_child[rr,i]-ri;y=whole_fine[g,j]-cj
        out[rr,i,g,j]=3*a[rr]+3*b[g]+9*d[rr,g]+20*ri+20*cj+25*atom.get((rr,i,g,j),Q())+5*z+5*y
    req(len(out)==1225,'every coherent numerical center')
    return out


def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('--fixture-json',type=Path,required=True)
    p.add_argument('--network-helper',type=Path,required=True)
    p.add_argument('--source-helper',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    raw=args.fixture_json.read_bytes();data=json.loads(raw)
    source={(row['root'],row['child']):set(map(tuple,row['whole_fibre']))for row in data['source']}
    atom=lambda name:{tuple(row['point']):Q(row['mass'])for row in data[name]}
    f0=atom('initial_flow');g=atom('both_entries_flow')
    network=runpy.run_path(str(args.network_helper))
    checker=runpy.run_path(str(args.source_helper))['source_checks']
    points={(rr,i,gg,j)for(rr,i),hs in source.items()for gg,j in hs}
    children,pairs,mono=checker(points)
    edges,trails=network['paths'](source)
    reduced_row=(('C',0,2),('P',0,2,0))
    def check(flow,row_cap):
        load=defaultdict(Q)
        for pt,m in flow.items():
            req(pt in points and m>=0,'same actual source and nonnegative atom')
            for e in trails[pt]:load[e]+=m
        req(sum(flow.values())==74,'one mass74 flow')
        for e,cap in edges.items():
            bound=Q(37,2)if e[0]==('S',)else row_cap if e==reduced_row else cap
            req(load[e]<=bound,'all original and designated capacities')
        req(all(load[(('S',),('R',rr))]==Q(37,2)for rr in range(4)),'all balanced roots')
        return load
    lf=check(f0,Q(6));lg=check(g,Q(5))
    def cut_side(node):
        if node[0] in ('S','R','C','P'):return True
        if node[0]=='L':return node[3] in (0,1)
        if node[0] in ('F','G'):return node[1] in (0,1)
        return False
    cut=[e for e in edges if cut_side(e[0])and not cut_side(e[1])]
    req(sum(edges[e]for e in cut)==74 and all(lf[e]==edges[e]for e in cut),
        'same actual original flow/cut maximum74')
    req(all(lf[e]==0 for e in edges if not cut_side(e[0])and cut_side(e[1])),
        'zero original backward-cut flow')
    req(lf[reduced_row]==6 and lg[reduced_row]==5,'actual full-network rowcap response')
    req(all(v!=Q(37,2)for v in margins(f0)[2].values()),'baseline needs no H185 replacement')
    req(all(v!=Q(37,2)for v in margins(g)[2].values()),'response H185 mixture is identical here')
    bad_support=any(len(set().union(*({h for gg,h in source.get((0,i),())if gg==0}for i in cs)))<=2
                    for cs in combinations(range(5),3))
    req(bad_support,'selected entire actual support T3bad')
    cf=charges(f0);cg=charges(g)
    bad=[q for q,K in cf.items()if K>Q(1183,2)]
    req(bad==[(0,2,0,0),(0,2,0,1)]and all(cf[q]==593 for q in bad),'exact baseline bad set')
    w=Q(15,149);base=1-w
    mixed={pt:base*f0.get(pt,Q())+w*g.get(pt,Q())for pt in points}
    lm=check(mixed,Q(6));cm=charges(mixed)
    req(all(cm[q]==base*cf[q]+w*cg[q]for q in cm),'all1225 query functionals linear on ONE mixture')
    exact=max(cm.values())
    req(exact==Q(87697,149),'actual all-coherent maximum')
    universal=Q(592)-Q(7,149)
    req(exact<universal<592,'actual and universal strict bounds')
    numerical_gamma=1+max(exact,Q(587))/74
    req(numerical_gamma==Q(98723,11026)<Q(99227,11026)<9,'actual common-law query envelope')
    out=dict(status='PASS',scope='One complete actual maximum74 source and one common rational law; all1225 coherent centers checked. Noncoherent587 is reused from TB.4. Not a universal source enumeration or Lean verification.',
             fixture_sha256=hashlib.sha256(raw).hexdigest(),original_maximum=74,actual_points=len(points),
             live_edges=len(edges),original_pair_checks=pairs,coherent_queries=len(cm),
             initial_bad_queries=[dict(center=q,K=str(cf[q]))for q in bad],
             designated_row_before=str(lf[reduced_row]),designated_row_response=str(lg[reduced_row]),
             base_weight=str(base),response_weight=str(w),
             initial_max_K=str(max(cf.values())),response_max_K=str(max(cg.values())),
             common_max_coherent_K=str(exact),reused_noncoherent_bound='587',
             actual_common_envelope=str(numerical_gamma),universal_bound='99227/11026',
             mixed_law=[dict(point=pt,mass=str(m))for pt,m in sorted(mixed.items())if m],
             maximizing_coherent_centers=[list(q)for q,K in cm.items()if K==exact])
    args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k!='mixed_law'}))


if __name__=='__main__':main()
