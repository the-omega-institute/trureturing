#!/usr/bin/env python3
"""Exact development checks; these do not claim universal kernel validation."""
from __future__ import annotations
import argparse, copy, itertools, json, random
from fractions import Fraction as F
from pathlib import Path
import check_real_x_arc_constellation as a


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('centers',type=Path)
    p.add_argument('--cover-reports',required=True,type=Path)
    p.add_argument('--output',required=True,type=Path)
    args=p.parse_args();args.output.unlink(missing_ok=True)
    xs=a.read_centers(args.centers); A,B,bounds,same=a.relations(xs)
    cliques,sets,_=a.audit_partners(A,B)
    reports=[json.loads((args.cover_reports/f'chart_{i:02d}.json').read_text()) for i in range(32)]
    a.audit_cover(reports)
    rng=random.Random(502820260906)
    checks=0
    for _ in range(1200):
        i,j=rng.randrange(60),rng.randrange(60)
        t,ts=xs[i][rng.randrange(5)];s,ss=xs[j][rng.randrange(5)]
        lo,hi=a.relative_arc(t,ts,s,ss,a.RADIUS)
        g=F(rng.randrange(-100,101),17),F(rng.randrange(-100,101),19)
        lower,upper=a.projection(lo,hi,g)
        for q in range(5):
            u=t+a.RADIUS*F(rng.randrange(-1000,1001),1000)
            v=s+a.RADIUS*F(rng.randrange(-1000,1001),1000)
            z=a.mul(a.conj(a.cayley(u,ts)),a.cayley(v,ss))
            a.require(a.cross(lo,z)>=0 and a.cross(z,hi)>=0,'wedge membership failure')
            cap=a.add(lo,hi)
            a.require(a.dot(cap,z)>=1+a.dot(lo,hi),'cap failure')
            a.require(lower<=a.dot(g,z)<=upper,'projection containment failure')
            checks+=1
    pairchecks=0
    cache={(i,j):(F(l),F(h)) for i,j,l,h in bounds}
    for _ in range(600):
        i,j=sorted((rng.randrange(60),rng.randrange(60))); z=(F(1),F(0))
        for (t,ts),(s,ss) in zip(xs[i],xs[j]):
            u=t+a.RADIUS*F(rng.randrange(-1000,1001),1000)
            v=s+a.RADIUS*F(rng.randrange(-1000,1001),1000)
            z=a.add(z,a.mul(a.conj(a.cayley(u,ts)),a.cayley(v,ss)))
        lo,hi=cache[i,j];q=a.dot(z,z)/36
        a.require(lo<=q<=hi,'whole-vector containment failure');pairchecks+=1
    tests=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,TypeError,IndexError):tests.append(name)
        else:raise RuntimeError('corruption accepted: '+name)
    lo,hi=a.relative_arc(*xs[0][0],*xs[1][0],a.RADIUS)
    reject('reversed_arc',lambda:a.arc_upper(hi,lo,(F(1),F(0))))
    reject('nonunit_endpoint',lambda:a.arc_upper((lo[0]*2,lo[1]*2),hi,(F(1),F(0))))
    reject('negative_radius',lambda:a.relative_arc(F(0),1,F(0),1,F(-1,16)))
    reject('invalid_phase_sign',lambda:a.cayley(F(0),0))
    reject('negative_sqrt',lambda:a.sqrt_upper(F(-1)))
    c=cliques[0]; BB=B.copy()
    for v in c:BB[v]|=3
    reject('two_partner_labels',lambda:a.audit_partners(A,BB))
    reject('missing_chart',lambda:a.audit_cover(reports[:-1]))
    for key,value in [('pending',1),('unresolved',1),('epsilon_bits',6),('guard_radius_bits',5),('tube_uniqueness_checked',True)]:
        rr=copy.deepcopy(reports);rr[0][key]=value
        reject('bad_'+key,lambda rr=rr:a.audit_cover(rr))
    import networkx as nx
    graph=nx.Graph();graph.add_nodes_from(range(60));graph.add_edges_from((i,j) for i in range(60) for j in range(i+1,60) if A[i]>>j&1)
    maximal=list(nx.find_cliques(graph))
    independent={tuple(sorted(s)) for c in maximal if len(c)>=6 for s in itertools.combinations(c,6)}
    a.require(independent==set(cliques),'independent clique enumeration mismatch')
    result={'status':'PASS','rational_arc_sample_checks':checks,'rational_whole_overlap_samples':pairchecks,
       'rejected_corruptions':tests,'independent_enumeration':{'maximal_cliques':len(maximal),'six_cliques':len(cliques),'method':'NetworkX maximal cliques and six-subsets'},
       'development_checks_only':True,'lean_kernel_verified':False}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
