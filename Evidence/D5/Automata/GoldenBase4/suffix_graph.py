"""Power-only common-suffix incompatibility certificates, no inferred labels."""
from collections import defaultdict
import json
from pathlib import Path
import networkx as nx
from verify21 import zeck,oracle


def graphs(count):
    weights=[1,2]
    while weights[-1] <= 1 << (2*(count-1)): weights.append(weights[-1]+weights[-2])
    data=[(i,zeck(1 << (2*i),weights),oracle(1 << (2*i))) for i in range(count)]
    # Labels only for powers and the published start-zero-output anchor.
    data.append((-1,'',0))
    bysuffix=defaultdict(list)
    for n,w,d in data:
        for k in range(len(w)+1):
            p=w[:len(w)-k]; s=w[len(w)-k:]
            bysuffix[s].append((n,p,d))
    gs=[nx.Graph(),nx.Graph()]
    for s,rows in bysuffix.items():
        for i,(ni,p,di) in enumerate(rows):
            for nj,q,dj in rows[i+1:]:
                if di==dj or p==q:continue
                ti=int(p.endswith('1')); tj=int(q.endswith('1'))
                if ti==tj:gs[ti].add_edge(p,q,suffix=s,power_pair=(ni,nj),digits=(di,dj))
    return gs


def maximum_clique(G):
    # Exact branch-and-bound maximum clique with greedy coloring (Tomita style).
    adj={v:set(G[v]) for v in G}; best=[]
    def color_sort(P):
        remaining=set(P); order=[]; bounds=[]; color=0
        while remaining:
            color+=1; available=set(remaining)
            while available:
                v=max(available,key=lambda v:len(adj[v]&remaining))
                order.append(v);bounds.append(color)
                remaining.remove(v);available.remove(v);available-=adj[v]
        return order,bounds
    calls=0
    def expand(C,P):
        nonlocal best,calls
        calls+=1
        order,bounds=color_sort(P)
        for i in range(len(order)-1,-1,-1):
            if len(C)+bounds[i] <= len(best):return
            v=order[i];q=P&adj[v]
            if q:expand(C+[v],q)
            elif len(C)+1>len(best):best=C+[v]
            P.remove(v)
    expand([],set(G))
    return best,calls

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--count',type=int,default=79);a=ap.parse_args()
    result={'power_count':a.count,'uses_start_zero_anchor':True,'types':[]}
    for typ,g in zip(('R','T'),graphs(a.count)):
        clique,calls=maximum_clique(g)
        colors=nx.coloring.greedy_color(g,strategy='saturation_largest_first')
        assert all(colors[u]!=colors[v] for u,v in g.edges)
        entry={'type':typ,'vertices':len(g),'edges':g.number_of_edges(),'maximum_clique_size':len(clique),
               'clique':clique,'search_calls':calls,
               'proper_coloring':colors,'coloring_upper_bound':1+max(colors.values()),
               'witnesses':[{'left':u,'right':v,**g[u][v]} for i,u in enumerate(clique) for v in clique[i+1:]]}
        result['types'].append(entry)
        print(typ,len(g),g.number_of_edges(),'clique',len(clique),'calls',calls,flush=True)
    result['combined_clique_lower_bound']=sum(t['maximum_clique_size'] for t in result['types'])
    p=Path(__file__).resolve().parent/f'suffix_graph_{a.count}.json'
    p.write_text(json.dumps(result,indent=2)+'\n')
