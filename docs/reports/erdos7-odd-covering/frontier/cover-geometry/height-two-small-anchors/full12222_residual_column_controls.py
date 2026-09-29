#!/usr/bin/env python3
"""Finite column classification for P3 plus two disjoint edges.

Only explicit finite sets are examined; no filesystem input or traversal.
"""
import argparse
from itertools import combinations, product
from fractions import Fraction as Q
from math import lcm
import json

D = (1,5,7,25,35,49,175,245,1225)
ROOT_D = tuple(d for d in D if d % 5 == 0)
COL_D = tuple(d for d in D if d % 7 == 0)


def require(condition,message):
    if not condition:
        raise RuntimeError(message)


def distinct_owner_labels(fibres, labels, number):
    for owners in combinations(range(5),number):
        def visit(i,used):
            if i == number:
                return True
            return any(visit(i+1,used|{v}) for v in fibres[owners[i]] & labels - used)
        if visit(0,set()):
            return True
    return False


def column_classification():
    fibres = [{0},{1,2},{1,3},{4,5},{6,7}]
    triples = [(owners,set().union(*(fibres[i] for i in owners)))
               for owners in combinations(range(5),3)]
    counts = {}
    residual = []
    rows = []
    for tail in product((0,1),repeat=7):
        columns = (0,)+tail
        parts = [{v for v,c in enumerate(columns) if c == k} for k in (0,1)]
        reason = None
        witness = None
        for owners,F in triples:
            if len({columns[v] for v in F}) == 1:
                reason,witness = 'whole_monochromatic',list(owners)
                break
        if reason is None:
            for column,labels in enumerate(parts):
                supplier = 'column_five_labels' if len(labels) >= 5 else (
                    'column_four_owners' if distinct_owner_labels(fibres,labels,4) else None)
                if supplier is None:
                    continue
                for owners,F in triples:
                    if len(F-labels) <= 1:
                        reason,witness = supplier,{'column':column,'owners':list(owners)}
                        break
                if reason:
                    break
        if reason is None and all(distinct_owner_labels(fibres,p,4) for p in parts):
            for owners,F in triples:
                if len(F) == 5 and sorted(len(F & p) for p in parts) == [2,3]:
                    reason,witness = 'two_columns_four_owner_points',list(owners)
                    break
        if reason is None and all(len(p)==4 for p in parts):
            anchors=[]
            for labels in parts:
                choices=[list(owners) for owners,F in triples if len(F-labels)<=1]
                if choices:
                    anchors.append(choices[0])
            if len(anchors)==2:
                reason,witness='two_column_punctures_eight_labels',anchors
        if reason is None:
            residual.append(list(columns))
            reason = 'OPEN'
        counts[reason] = counts.get(reason,0)+1
        rows.append({'columns':list(columns),'supplier':reason,'witness':witness})
    return {'layouts':len(rows),'counts':counts,'residuals':residual,'rows':rows}


def coarse_certificate(name,pure,root_only,combined,denominator,weights):
    ri = {d:i for i,d in enumerate(ROOT_D)}
    ci = {d:i for i,d in enumerate(COL_D)}
    pairs = [(lcm(d,e),ri.get(d,-1),ri.get(e,-1),ci.get(d,-1),ci.get(e,-1))
             for d in D for e in D]
    maximum = -1
    maxima = []
    count = 0
    for roots in product((0,1),repeat=6):
        rp = [(m,roots[a] if a>=0 else roots[b] if b>=0 else -1,c,d)
              for m,a,b,c,d in pairs if a<0 or b<0 or roots[a]==roots[b]]
        for cols in product(range(3),repeat=6):
            z = 0
            for m,r,a,b in rp:
                if a>=0 and b>=0 and cols[a]!=cols[b]:
                    continue
                c = cols[a] if a>=0 else cols[b] if b>=0 else -1
                z += denominator if m==1 else pure[m][c] if r<0 else root_only[m][r] if c<0 else combined[m][r][c]
            count += 1
            if z>maximum:
                maximum,maxima = z,[]
            if z==maximum:
                maxima.append({'roots':list(roots),'columns':list(cols)})
    return {'name':name,'layouts':count,'maximum':str(Q(maximum,denominator)),
            'maximizers':maxima,'weights':weights}


def four_by_four():
    return coarse_certificate('two_columns_four_owner_points',
        {7:(600,1005,1395),49:(150,600,465)},
        {5:(620,1140),25:(372,285)},
        {35:((0,155,465),(600,540,0)),175:((0,93,279),(150,135,0)),
         245:((0,155,155),(150,135,0)),1225:((0,93,93),(150,135,0))},
        3000,['31/50','1/5','9/50'])


def two_column_punctures():
    # Units 1/800; lambda=(3/8)psi_H+(3/8)psi_J, pi=eta/4.
    return coarse_certificate('two_column_punctures_eight_labels',
        {7:(280,280,360),49:(85,85,120)},
        {5:(200,200),25:(120,50)},
        {35:((60,60,120),(100,100,0)),175:((36,36,72),(50,50,0)),
         245:((20,20,40),(25,25,0)),1225:((12,12,24),(25,25,0))},
        800,['3/8','3/8','1/4'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True)
    args = parser.parse_args()
    classification = column_classification()
    certificate = four_by_four()
    dual = two_column_punctures()
    require(classification['layouts']==128,'incomplete column classification')
    require(classification['counts']=={'whole_monochromatic':44,'column_five_labels':50,
        'column_four_owners':12,'two_columns_four_owner_points':12,
        'two_column_punctures_eight_labels':10},'unexpected classification counts')
    require(classification['residuals']==[],'unhandled column layout')
    require(certificate['layouts']==46656 and dual['layouts']==46656,'incomplete query enumeration')
    require(certificate['maximum']=='35/4' and dual['maximum']=='44/5','query maximum changed')
    result = {'status':'PASS','classification':classification,'four_by_four':certificate,'dual_puncture':dual,
              'scope':'Necessary column layouts and exact common-query interface; source constructions require their separate proofs.'}
    with open(args.output,'w',encoding='utf-8') as stream:
        json.dump(result,stream,indent=2,sort_keys=True)
        stream.write('\n')
    print(json.dumps({'status':'PASS','counts':classification['counts'],'residuals':classification['residuals'],
                      'query_maximum':certificate['maximum'],'dual_maximum':dual['maximum'],
                      'dual_maximizers':dual['maximizers']}))


if __name__ == '__main__':
    main()
