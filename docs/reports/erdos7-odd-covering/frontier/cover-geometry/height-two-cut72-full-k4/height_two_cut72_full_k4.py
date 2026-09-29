#!/usr/bin/env python3
"""Exact actual-source controls for all22 full cut72/public4/private22 shapes.

These are construction controls accompanying ordinary source proofs. They do
not exhaust actual sources or constitute Lean or odd-covering verification.
"""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
from pathlib import Path
import argparse
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    spec=spec_from_file_location('_cut72_full_k4_support',path)
    require(spec is not None and spec.loader is not None,'support module')
    mod=module_from_spec(spec);spec.loader.exec_module(mod)
    return mod


def templates(base, shapes):
    out=[]
    for index,shape in enumerate(shapes,1):
        rows=shape.split('/')
        yroot=next((r for r in range(1,4) if rows[r].startswith('011')),0)
        # Four private root columns are distinct. The public extra leaf belongs
        # to the gap column unless a full zero root needs its public completion.
        yg=yroot+1
        for whole in ((False,True) if '3' in shape else (False,)):
            private={};wholechildren=set()
            for r,row in enumerate(rows):
                cursor=0;modulus=6 if r==yroot else 7
                for c,digit in enumerate(row):
                    cost=int(digit)
                    hs={(cursor+j)%modulus for j in range(cost)}
                    require(len(hs)==cost,'private cost at finite child')
                    cursor+=cost
                    if whole and cost==3:
                        hs=set(range(7));wholechildren.add((r,c))
                    private[r,c]={(r+1,h) for h in hs}
            public={(0,h) for h in range(7)}|{(yg,6)}
            fibres={child:public|private[child] for child in base.CHILDREN}
            out.append(dict(name='fullk4_%02d'%index+('_whole' if whole else '_finite'),shape=shape,
                            active=base.N,public_columns=(0,),public_leaves=((yg,6),),private=private,
                            whole_private=wholechildren,fibres=fibres,
                            source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys},
                            cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1))))
    # Additional T controls exercise its K-dominant branch, including one
    # genuine outlier in the gap column and the all-five-in-K subcase.
    for outlier in (False,True):
        private={(0,0):{(4,0)}}
        edges=((1,2),(1,3),(2,3)) if outlier else((1,2),(2,3),(3,4))
        private.update({(0,c):{(4,h) for h in edge} for c,edge in enumerate(edges,1)})
        private.update({(1,c):{(4,4)} if outlier and c==4 else{(1,c)} for c in range(5)})
        private.update({(r,c):{(r,c)} for r in(2,3) for c in range(5)})
        public={(0,h) for h in range(7)}|{(1,6)}
        fibres={child:public|private[child] for child in base.CHILDREN}
        out.append(dict(name='T_K_dominant_'+('outlier' if outlier else 'pure'),
                        shape='1222/11111/11111/11111',active=base.N,public_columns=(0,),
                        public_leaves=((1,6),),private=private,whole_private=set(),fibres=fibres,
                        source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys},
                        cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1))))
    return out


def network(item,base,dinic):
    caps={};start=('source',);finish=('sink',)
    def add(u,v,cap):
        require((u,v) not in caps,'unique network arc');caps[u,v]=cap
    for r,n in enumerate(base.N):
        add(start,('r',r),21)
        for c in range(n):
            add(('r',r),('c',r,c),7)
            for g in range(7):
                add(('c',r,c),('pg',r,c,g),6)
                for h in range(7):add(('pg',r,c,g),('ph',r,c,g,h),2)
    for g in range(7):
        add(('cg',g),finish,21)
        for h in range(7):add(('ch',g,h),('cg',g),7)
    for p in sorted(item['source']):add(('ph',*p),('ch',*p[2:]),126)
    value,flow,side=base.solve_network(caps,start,finish,1000,dinic)
    require(value==72,item['name']+': actual maxflow72, got '+str(value))
    mincut=[(u,v,c) for (u,v),c in caps.items() if u in side and v not in side]
    require(sum(c for u,v,c in mincut)==72,'computed mincut72')
    explicit={start}
    for g in item['public_columns']:
        explicit.add(('cg',g));explicit.update(('ch',g,h) for h in range(7))
    explicit.update(('ch',g,h) for g,h in item['public_leaves'])
    for r,a in enumerate(item['active']):
        if a:explicit.add(('r',r))
        for c in range(a):
            explicit.add(('c',r,c))
            whole_cols={g for g,h in item['private'][r,c]} if (r,c) in item['whole_private'] else set()
            require(len(whole_cols)<=1,'private whole prefix is one column')
            for g in range(7):
                if g in whole_cols:continue
                explicit.add(('pg',r,c,g))
                explicit.update(('ph',r,c,g,h) for h in range(7) if(g,h) not in item['private'][r,c])
    cut=[(u,v,c) for (u,v),c in caps.items() if u in explicit and v not in explicit]
    require(not any(u[0]=='ph' for u,v,c in cut),'no actual bridge crosses prescribed cut')
    require(sum(c for u,v,c in cut)==72,'prescribed cut72')
    require(all(flow[u,v]==c for u,v,c in cut),'forward prescribed cut saturation')
    require(all(flow[u,v]==0 for u,v in caps if u not in explicit and v in explicit),'zero backward prescribed cut flow')
    atoms=[[*u[1:],f] for (u,v),f in flow.items() if u[0]=='ph' and v[0]=='ch' and f]
    return dict(maximum_flow=value,minimum_cut=72,edge_count=len(caps),
                prescribed_cut=[[list(u),list(v),c] for u,v,c in cut],
                computed_minimum_cut=[[list(u),list(v),c] for u,v,c in mincut],actual_flow_atoms=atoms)


def selected_law(item,base,dinic):
    caps={};start=('selector source',);finish=('selector sink',)
    for child in sorted(base.CHILDREN):caps[start,('child',*child)]=1
    for p in sorted(item['source']):caps[('child',*p[:2]),('leaf',*p[2:])]=1
    for g,h in sorted({p[2:] for p in item['source']}):caps[('leaf',g,h),('column',g)]=1
    for g in range(7):caps[('column',g),finish]=5
    value,flow,side=base.solve_network(caps,start,finish,18,dinic)
    require(value==18,'actual owner/leaf/column selector18')
    pts=[(*u[1:],*v[1:]) for(u,v),f in flow.items() if u[0]=='child' and v[0]=='leaf' and f]
    require(len(pts)==len(set(pts))==len({p[:2] for p in pts})==len({p[2:] for p in pts})==18,
            'eighteen distinct actual owners and labels')
    require(set(pts)<=item['source'],'selected points actual at their owners')
    require(max(Counter(p[2] for p in pts).values())<=5,'selected column cap5')
    return {p:Q(1,18) for p in pts}


@lru_cache(None)
def compositions(n,k):
    if k==1:return((n,),)
    return tuple((v,)+tail for v in range(n+1) for tail in compositions(n-v,k-1))


def column_pattern_checks():
    # Coordinate0 is K=col(y), coordinate6 is the public whole column G.
    patterns=compositions(5,7)
    triples=[{tuple(t.count(j) for j in range(7)) for t in combinations(
        [j for j,n in enumerate(p) for _ in range(n)],3)} for p in patterns]
    def admissible(p):
        return p[0]>=4 or (p[0]==p[6]==0 and max(p[1:6])==5)
    def ok(i,j):
        return all(sum(x+y+(c==0)>=3 for c,(x,y) in enumerate(zip(a,b)) if c!=6)>=2
                   for a in triples[i] for b in triples[j])
    adj=[set() for p in patterns]
    for i in range(len(patterns)):
        for j in range(i,len(patterns)):
            if ok(i,j):
                require(admissible(patterns[i]) and admissible(patterns[j]),'pair column classification')
                adj[i].add(j);adj[j].add(i)
    cliques=0
    for i in range(len(patterns)):
        for j in adj[i]:
            if j<i:continue
            for k in adj[i]&adj[j]:
                if k<j:continue
                cliques+=1
                pp=[patterns[t] for t in(i,j,k)]
                require(sum(p[0]>=4 for p in pp)<=1,'at most one K-dominant family')
                pure=[p for p in pp if p[0]<4]
                require(len({p.index(5) for p in pure})==len(pure),'pure columns differ')
    require((len(patterns),sum(map(len,adj)),cliques)==(462,90,80),'column classification check counts')
    return dict(patterns=462,directed_compatible_pairs=90,compatible_three_family_multisets=80)


def inventory_checks(shapes):
    require(len(shapes)==len(set(shapes))==22,'all22 k4/Z22 shapes')
    rows=[]
    for shape in shapes:
        parts=shape.split('/');costs=[int(c) for part in parts for c in part]
        require(tuple(map(len,parts))==(4,5,5,5),'nineteen actual child owners')
        require(sum(costs)==22 and costs.count(0)<=1,'finite occurrence lemma hypotheses')
        rows.append(dict(shape=shape,private_occurrences=sum(costs),public_occurrences=4,
                         candidate_occurrences=26,zero_private_owners=costs.count(0),actual_tree_leaves=25))
    bounds=['33/4','173/21','1214/139','3473/393','643/72','1603/195','79/9','26/3']
    require(max(map(Q,bounds))==Q(643,72),'all fourteen profile-family envelope maximum')
    return dict(finite_occurrence_hypotheses=rows,family_bounds=bounds,maximum_family_bound='643/72',gap_below_nine='5/72')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--profiles',type=Path,default=Path(__file__).with_name('height_two_cut72_profiles.json'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module);dinic=base.load_dinic(args.dinic_module)
    shapes=json.loads(args.profiles.read_text())['shapes']['4555_k4_Z22']
    inventory=inventory_checks(shapes);patterns=column_pattern_checks();controls=[]
    for item in templates(base,shapes):
        literal=base.literal_checks(item);net=network(item,base,dinic);law=selected_law(item,base,dinic)
        rec=dict(name=item['name'],shape=item['shape'],source_points=len(item['source']),source=sorted(item['source']),
                 public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                 private=[[*child,sorted(ys)] for child,ys in sorted(item['private'].items())],
                 whole_private_children=sorted(item['whole_private']),selected_points=sorted(law),
                 **literal,network=net,law=base.check_law(item,law))
        controls.append(rec)
        print(json.dumps(dict(name=rec['name'],points=rec['source_points'],minimum_cut=rec['network']['minimum_cut'],
                              gamma=rec['law']['gamma_envelope'],universal_gamma=rec['law']['universal_gamma'])),flush=True)
    require(sum(x['name'].startswith('fullk4_') and not x['whole_private_children'] for x in controls)==22,'all finite private shapes')
    require(sum(bool(x['whole_private_children']) for x in controls)==8,'all eight whole private variants')
    require(len(controls)==32,'thirty-two actual controls')
    out=dict(scope='Thirty-two actual cut72 controls for all22 whole-public k4/Z22 shapes, their eight cost3 whole-private variants, and two K-dominant T variants. Finite public4/all-private-finite occurrence hypotheses are checked for all22 shapes. Exact construction controls, not exhaustive actual-source search, Lean verification, or unrestricted odd covering.',
             inventory=inventory,column_pattern_checks=patterns,controls=controls)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
