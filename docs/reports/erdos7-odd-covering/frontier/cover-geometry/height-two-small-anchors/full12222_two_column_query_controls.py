#!/usr/bin/env python3
"""Exact candidate queries for the remaining disjoint-double two-column types.

Reads no input files, writes only --output, and performs no traversal.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
import json
from math import lcm
from pathlib import Path

D = (1,5,7,25,35,49,175,245,1225)
ROOT_D = tuple(d for d in D if d%5 == 0)
COL_D = tuple(d for d in D if d%7 == 0)
CATS = ('H','J','other')
PAIRS = [(d,e,lcm(d,e),1 if d == e else 2)
         for k,d in enumerate(D) for e in D[k:]]


def require(condition,message):
    if not condition:
        raise ValueError(message)


def two_components(n,w,expected):
    p = dict(zip(D,map(Q,('1','1/3','3/5','1/5','1/5','1/5','3/25','1/15','1/25'))))
    e = {d:(Q(1) if d in (1,5,7,35) else Q(2,n) if d in (25,175) else Q(1,n)) for d in D}
    rows = []
    for bits in product((0,1),repeat=8):
        selected = {1}|{d for d,b in zip(D[1:],bits) if b}
        complementary = {1}|(set(D)-selected)
        left,right = Q(0),Q(0)
        for d,f,m,mult in PAIRS:
            if d in selected and f in selected: left += mult*p[m]
            if d in complementary and f in complementary: right += mult*e[m]
        rows.append({'bits':list(bits),'bound':str(w*left+(1-w)*right)})
    maximum = max(Q(row['bound']) for row in rows)
    require(maximum == expected,'unexpected two-component maximum')
    return {'n':n,'weight':str(w),'layout_count':256,'maximum':str(maximum),
            'maximizers':[r['bits'] for r in rows if Q(r['bound']) == maximum],
            'all_bounds':rows}


def h4j5():
    w,h,j = Q(31,50),Q(1,5),Q(9,50)
    pure = {(1,None):Q(1)}
    other_root = {(5,None):w/3,(25,None):w/5}
    at_r = {(5,None):h+j,(25,None):max(h/4+j/5,2*j/5)}
    for c in CATS:
        pure[7,c] = {'H':h,'J':w/4+j,'other':3*w/4}[c]
        pure[49,c] = {'H':h/4,'J':w/4+j/5,'other':w/4}[c]
        other_root[35,c] = {'H':Q(0),'J':w/12,'other':w/4}[c]
        other_root[175,c] = {'H':Q(0),'J':w/20,'other':3*w/20}[c]
        other_root[245,c] = Q(0) if c == 'H' else w/12
        other_root[1225,c] = Q(0) if c == 'H' else w/20
        at_r[35,c] = {'H':h,'J':j,'other':Q(0)}[c]
        at_r[175,c] = {'H':h/4,'J':2*j/5,'other':Q(0)}[c]
        at_r[245,c] = {'H':h/4,'J':j/5,'other':Q(0)}[c]
        at_r[1225,c] = at_r[245,c]
    scale = lcm(*(v.denominator for table in (pure,other_root,at_r) for v in table.values()))
    pure,other_root,at_r = [{key:int(scale*v) for key,v in table.items()}
                          for table in (pure,other_root,at_r)]
    all_values,maximizers,maximum = [],[],-1
    coherent = {}
    for rb in product((0,1),repeat=6):
        roots = dict(zip(ROOT_D,rb))
        values = []
        for cb in product(CATS,repeat=6):
            cols = dict(zip(COL_D,cb))
            score = 0
            for d,e,m,mult in PAIRS:
                rd,re = roots.get(d),roots.get(e)
                cd,ce = cols.get(d),cols.get(e)
                if rd is not None and re is not None and rd != re: continue
                if cd is not None and ce is not None and cd != ce: continue
                r = rd if rd is not None else re
                c = cd if cd is not None else ce
                table = pure if r is None else (at_r if r else other_root)
                score += mult*table[m,c]
            values.append(score)
            layout = {'root_bits':list(rb),'column_categories':list(cb)}
            if score > maximum: maximum,maximizers = score,[layout]
            elif score == maximum: maximizers.append(layout)
            if len(set(rb)) == len(set(cb)) == 1:
                coherent[str(rb[0])+':'+cb[0]] = str(Q(score,scale))
        all_values.append(values)
    require(sum(map(len,all_values)) == 46656,'all46656 layouts')
    require(coherent['0:other'] == '35/4','all-other coherent layout')
    require(coherent['1:H'] == '797/100','all-R/H coherent layout')
    require(coherent['1:J'] == '867/100','all-R/J coherent layout')
    return {'weights':{'psi':str(w),'eta_H':str(h),'eta_J':str(j)},
            'safe_all_J_psi_fine_cap':'1/4','layout_count':46656,'maximum':str(Q(maximum,scale)),
            'strictly_below_nine':maximum < 9*scale,'maximizers':maximizers,
            'denominator':scale,'coherent_extremes':coherent,
            'all_bound_numerators_root_major':all_values}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    two = [two_components(5,Q(40,53),Q(469,53)),
           two_components(6,Q(875,1187),Q(10287,1187))]
    three = h4j5()
    result = {'status':'PASS','divisors':list(D),'root_divisors':list(ROOT_D),
              'column_divisors':list(COL_D),'column_categories':list(CATS),
              'two_component_cases':two,'H4_J5_case':three,'layout_count':47168,
              'scope':'Exact conditional cap relaxation, not actual source enumeration or a source counterexample.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','layout_count':47168,
                      'two_component_maxima':[c['maximum'] for c in two],
                      'H4_J5_maximum':three['maximum'],'H4_J5_maximizers':three['maximizers'],
                      'H4_J5_strictly_below_nine':three['strictly_below_nine']}))


if __name__ == '__main__':
    main()
