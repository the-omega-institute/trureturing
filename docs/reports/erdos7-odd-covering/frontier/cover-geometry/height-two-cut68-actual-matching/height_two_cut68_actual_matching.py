#!/usr/bin/env python3
"""Construct 18 actual matches from the cut68 hypotheses; stdlib only.
Optional positional JSON input keys: children, private, fibres, public_column,
public_leaf, standalone. children are distinct [r,c]; other sets are [g,h].
Without input run sharp and full-19 actual-source controls. These satisfy
the weak containment/standalone premises; literal product blocking and
minimum cut68 are not asserted for them. General proofs are in Report449.
"""
import json
import argparse
from pathlib import Path
from collections import Counter, deque
from fractions import Fraction
from itertools import product

CHECKS = 0

def check(value, message):
    global CHECKS
    if not value:
        raise ValueError(message)
    CHECKS += 1


def solve(data):
    def pair(value, bound):
        return (isinstance(value, (list, tuple)) and len(value) == 2
                and all(type(x) is int and 0 <= x < bound for x in value))

    check(all(pair(x, 5) for x in data['children']), 'children must be integer digit pairs')
    check(all(pair(y, 7) for row in data['private']+data['fibres'] for y in row),
          'seven leaves must be integer digit pairs')
    check(type(data['public_column']) is int and 0 <= data['public_column'] < 7
          and pair(data['public_leaf'], 7), 'public data must be integer digits')
    check(all((type(k) is int and 0 <= k < 7)
              or (type(k) is str and k in tuple(map(str, range(7))))
              for k in data['standalone']), 'standalone keys must be integer columns')
    check(all(pair(y, 7) for row in data['standalone'].values() for y in row),
          'standalone leaves must be integer digit pairs')
    children = [tuple(x) for x in data['children']]
    private = [{tuple(y) for y in row} for row in data['private']]
    fibres = [{tuple(y) for y in row} for row in data['fibres']]
    g = data['public_column']
    star = tuple(data['public_leaf'])
    tree = {int(k): {tuple(y) for y in row} for k, row in data['standalone'].items()}
    check(len(children) == len(set(children)) == len(private) == len(fibres) == 19,
          '19 distinct actual children required')
    check(all(0 <= r < 5 and 0 <= c < 5 for r,c in children), 'invalid child')
    check(0 <= g < 7 and all(0 <= t < 7 for t in star), 'invalid public data')
    check(sorted(map(len, private)) == [1]*18+[2], 'private sizes must total20')
    check(all(fibres), 'an actual child must be nonempty')
    check(all(all(0 <= a < 7 and 0 <= b < 7 for a,b in row)
              for row in private+fibres), 'invalid seven leaf')
    public = {(g,h) for h in range(7)} | {star}
    check(all(f <= public | s for f,s in zip(fibres,private)), 'cut containment')
    check(len(tree) == 5 and all(len(row)==5 for row in tree.values()), 'five-ary tree')
    check(all(0 <= col < 7 and all(y[0]==col and 0<=y[1]<7 for y in row)
              for col,row in tree.items()), 'invalid standalone columns')
    actual_union = set().union(*fibres)
    tree_leaves = set().union(*tree.values())
    check(len(tree_leaves)==25 and tree_leaves <= actual_union, 'tree must be actual')
    outside = actual_union - {(g,h) for h in range(7)}
    check(len(outside)<=21, 'outside candidate bound')
    check(g in tree, '25 outside tree leaves would exceed21 candidates')
    query = tree_leaves - public
    check(len(query) in (19,20), 'external actual nonpublic tree leaves')
    owners = {y:[i for i,f in enumerate(fibres) if y in f] for y in query}
    check(all(owners.values()), 'each tree leaf has an actual supplier')
    check(all(y in private[i] for y, ii in owners.items() for i in ii),
          'actual supplier edge must be its private candidate')
    degrees = Counter(i for ii in owners.values() for i in ii)
    double = next(i for i,s in enumerate(private) if len(s)==2)
    check(all(d <= (2 if i==double else 1) for i,d in degrees.items()), 'degree bound')
    # Select one actual supplier per right leaf, then one leaf per supplier.
    # Only double can appear twice, so at most one right leaf is discarded.
    selected_by_child = {}
    for y in sorted(query):
        selected_by_child.setdefault(min(owners[y]), y)
    check(len(selected_by_child)>=len(query)-1>=18, 'matching lower bound')
    selected = sorted(selected_by_child.items())[:18]
    check(len(selected)==18 and len({y for _,y in selected})==18, 'distinct matching')
    check(all(y in fibres[i] for i,y in selected), 'selected edges must be actual')
    check(max(Counter(y[0] for _,y in selected).values())<=5, 'column cap')
    # Literal CRT readouts of this one actual 18-point law.
    residues=[]
    for i,(a,b) in selected:
        r,c = children[i]
        x5 = r+5*c
        x7 = a+7*b
        residues.append(x5+25*(((x7-x5)*pow(25,-1,49))%49))
    check(len(set(residues))==18, 'distinct literal CRT points')
    moduli = (5,7,25,35,49,175,245,1225)
    weights = (3,3,5,9,5,15,15,25)
    expected_counts = (5,5,1,5,1,1,1,1)
    maxima = [max(Counter(z%d for z in residues).values()) for d in moduli]
    check(all(a<=b for a,b in zip(maxima,expected_counts)), 'all cylinder caps')
    envelope = 1+sum(Fraction(w*c,18) for w,c in zip(weights,maxima))
    check(envelope<=Fraction(79,9)<9, 'same-law ordered-LCM envelope')
    return {'selected': [[list(children[i]),list(y)] for i,y in selected],
            'query_leaf_count':len(query), 'supplier_degree_max':max(degrees.values()),
            'column_counts':dict(sorted(Counter(y[0] for _,y in selected).items())),
            'cylinder_maxima_counts':dict(zip(moduli,maxima)),
            'ordered_lcm_envelope':str(envelope), 'universal_bound':'79/9'}


def full_actual_flow(data):
    # Independent exact source-child-leaf-column-sink network, including public points.
    fibres = [{tuple(y) for y in row} for row in data['fibres']]
    leaves = sorted(set().union(*fibres))
    columns = sorted({y[0] for y in leaves})
    names = [('source',)] + [('child',i) for i in range(19)]
    names += [('leaf',)+y for y in leaves]+[('column',g) for g in columns]+[('sink',)]
    index = {name:i for i,name in enumerate(names)}
    graph=[[] for _ in names]
    original=[]
    def edge(a,b,c):
        u,v=index[a],index[b]
        graph[u].append([v,len(graph[v]),c])
        graph[v].append([u,len(graph[u])-1,0])
        original.append((u,v,c))
    for i,row in enumerate(fibres):
        edge(('source',),('child',i),1)
        for y in row: edge(('child',i),('leaf',)+y,100)
    for y in leaves: edge(('leaf',)+y,('column',y[0]),1)
    for g in columns: edge(('column',g),('sink',),5)
    source,sink=index[('source',)],index[('sink',)]
    total=0
    while True:
        parent={source:None}
        queue=deque([source])
        while queue and sink not in parent:
            u=queue.popleft()
            for j,(v,_,cap) in enumerate(graph[u]):
                if cap and v not in parent:
                    parent[v]=(u,j)
                    queue.append(v)
        if sink not in parent: break
        flow=100
        v=sink
        while v!=source:
            u,j=parent[v]
            flow=min(flow,graph[u][j][2]); v=u
        v=sink
        while v!=source:
            u,j=parent[v]
            rev=graph[u][j][1]
            graph[u][j][2]-=flow
            graph[v][rev][2]+=flow
            v=u
        total+=flow
    reachable=set(parent)
    cut=[(names[u],names[v],cap) for u,v,cap in original if u in reachable and v not in reachable]
    check(sum(c for _,_,c in cut)==total, 'independent maxflow/mincut equality')
    check(total>=18, 'full actual source matching lower bound')
    return {'value':total,'cut':cut}


def control(sharp):
    children=[(0,c) for c in range(4)]+[(r,c) for r in range(1,4) for c in range(5)]
    tree={g:{(g,h) for h in range(5)} for g in range(5)}
    star=(1,0)
    outside=sorted(set().union(*(tree[g] for g in range(1,5))))
    if sharp:
        x=[y for y in outside if y!=star]
        private=[{x[0]},{x[0]}]+[{y} for y in x[1:17]]+[{x[17],x[18]}]
    else:
        private=[{y} for y in outside[:18]]+[set(outside[18:])]
    fibres=[set(row) for row in private]
    fibres[-1] |= tree[0] | {star}
    return {'children':children,'private':[sorted(s) for s in private],
            'fibres':[sorted(s) for s in fibres], 'public_column':0,
            'public_leaf':star,'standalone':{g:sorted(s) for g,s in tree.items()}}


def main():
    global CHECKS
    CHECKS = 0
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path,help='optional literal source JSON')
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'),
                        help='exact result path (default: sibling .json)')
    args=parser.parse_args()
    if args.input is not None:
        with args.input.open(encoding='utf-8') as stream: data=json.load(stream)
        result={'construction':solve(data),'full_actual_network':full_actual_flow(data)}
    else:
        result={}
        for name,sharp in [('sharp18',True),('full19',False)]:
            data=control(sharp)
            construction=solve(data)
            network=full_actual_flow(data)
            check(network['value']==(18 if sharp else 19), 'control optimum')
            result[name]={'input':data,'construction':construction,'full_actual_network':network,
                          'scope':'Common actual F satisfies weak standalone/cut hypotheses; no root-pair blocking claim.'}
        # A candidate leaf unbacked by F must fail input validation.
        bad=control(True)
        lost=tuple(bad['standalone'][4][4])
        bad['fibres']=[[y for y in row if tuple(y)!=lost] for row in bad['fibres']]
        try:
            solve(bad)
        except ValueError as exc:
            check(str(exc)=='tree must be actual', 'negative control rejection reason')
            result['unbacked_tree_control']={'rejected':True,'reason':str(exc)}
        else:
            raise ValueError('unbacked standalone leaf accepted')
        # Noninteger coordinates cannot represent literal numerical cylinders.
        bad=control(True)
        bad['children'][0]=(0.5,0)
        try:
            solve(bad)
        except ValueError as exc:
            check(str(exc)=='children must be integer digit pairs',
                  'noninteger control rejection reason')
            result['noninteger_control']={'rejected':True,'reason':str(exc)}
        else:
            raise ValueError('noninteger child accepted')
    result['checks']=CHECKS
    payload=json.dumps(result,indent=2)+'\n'
    args.output.write_text(payload,encoding='utf-8')
    print(payload,end='')

if __name__=='__main__': main()
