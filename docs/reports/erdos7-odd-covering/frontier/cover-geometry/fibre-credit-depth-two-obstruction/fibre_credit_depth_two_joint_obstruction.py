#!/usr/bin/env python3
"""Consume an exact dual excluding the complete joint-moment scalar gate."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


def need(ok,msg):
    if not ok:raise RuntimeError(msg)


def calculate(witnesses):
    data=json.loads(witnesses.read_text())
    actual=[(3,0),(9,1),(5,0),(7,0),(15,11),(45,2),
            (21,1),(63,58),(35,3),(105,74),(315,187)]
    originals=data['originals']
    need(all(type(m) is int and type(a) is int and m>1 and m%2 and 0<=a<m
             for m,a in originals),'literal integer numerical originals')
    need(len(originals)==11 and sorted(map(tuple,originals))==sorted(actual),
         'the declared actual opposite-root head, with no duplicate label')
    rows=[x for x in range(315) if all(x%m!=a for m,a in originals)]
    need(len(rows)==75,'actual75-row head support')
    beta=F(data['beta']);need(beta==F(1,19),'declared all-order coefficient1/19')
    budgets={3**j*5**e*7**f:(F(5,4) if e else 1)*(F(7,6) if f else 1)-1
             for j,e,f in product(range(3),range(2),range(2))}
    spent=defaultdict(F);layout_spent=F(0);scores={x:F(0) for x in rows}
    finite_scores={x:F(0) for x in rows};centres=[]
    height=5;period=9*5**height*7**height
    finite_factor={q:1+sum((F(2*e+1,q**(e-1)) for e in range(1,height+1)),F(0)) for q in (5,7)}
    identities=set();counts=defaultdict(int)
    for term in data['weights']:
        kind=term['kind'];args=term['arguments'];w=F(term['weight'])
        need(w>0,'strictly positive rational dual weights')
        ident=(kind,*args)
        need(ident not in identities,'each dual witness occurs once');identities.add(ident)
        counts[kind]+=1
        if kind=='cylinder':
            need(len(args)==2,'cylinder arity')
            m,a=args
            need(type(m) is int and type(a) is int and m in budgets and 0<=a<m,
                 'literal first-cylinder type and phase')
            need(any(x%m==a for x in rows),'cylinder has actual supported rows')
            spent[m]+=w
            for x in rows:
                scores[x]+=w*int(x%m==a)
                finite_scores[x]+=w*int(x%m==a)
        elif kind=='coherent':
            need(len(args)==1 and type(args[0]) is int and 0<=args[0]<315,
                 'one actual coherent first anchor')
            a=args[0];layout_spent+=w
            centre=sum(r*(period//m)*pow(period//m,-1,m)
                       for m,r in ((9,a%9),(5**height,a%5),(7**height,a%7)))%period
            slots=[3**j*5**e*7**f for j,e,f in product(range(3),range(height+1),range(height+1))]
            need(len(slots)==len(set(slots))==108 and centre%315==a,
                 'one literal CRT centre for all108 distinct numerical slots')
            need(centre%(5**height)==a%5 and centre%(7**height)==a%7,
                 'all later digits of the shared finite centre are zero')
            centres.append(dict(first_anchor=a,full_anchor=centre))
            for x in rows:
                J=1+int(x%3==a%3)+int(x%9==a%9)
                value=J*J*(F(43,8) if x%5==a%5 else 1)*(F(44,9) if x%7==a%7 else 1)
                scores[x]+=w*value
                finite_scores[x]+=w*J*J*(finite_factor[5] if x%5==a%5 else 1)*(finite_factor[7] if x%7==a%7 else 1)
        else:raise RuntimeError('unsupported joint-layout witness')
    need(all(spent[m]<=b for m,b in budgets.items()),'each complete deep-cylinder budget')
    need(layout_spent<=beta,'one shared joint-moment budget')
    minimum=min(scores.values())
    need(minimum>1,'strict rowwise obstruction at every actual head atom')
    need(F(data['minimum'])==minimum,'claimed lower is the exact reconstructed minimum')
    finite_minimum=min(finite_scores.values())
    need(finite_minimum>1,'actual finite-height5 shared layouts already obstruct the gate')
    geometric=[]
    for q,limit in ((5,F(43,8)),(7,F(44,9))):
        previous=F(0)
        for h in range(1,9):
            pair=sum((F(1,q**(max(e,f)-1)) if e or f else F(1)
                      for e,f in product(range(h+1),repeat=2)),F(0))
            # When exactly one exponent is zero the same maximum formula applies.
            diagonal=1+sum((F(2*e+1,q**(e-1)) for e in range(1,h+1)),F(0))
            tail=F(q, q-1)**2 * F((2*h+3)*(q-1)+2,q**(h+1))
            need(pair==diagonal and previous<diagonal<limit,
                 'finite numerical-exponent pair count and monotone complete limit')
            need(limit-diagonal==tail,'complete geometric pair tail')
            geometric.append(dict(prime=q,height=h,finite_square=str(diagonal),tail=str(tail)))
            previous=diagonal
    return dict(scope='One literal75-row head. Every head probability p is allowed. '
                      'Prefix-Haar nonternary digits, complete deep union debit, '
                      'and the exact full-height shared-layout moment Gamma_star. '
                      'The scalar gate fails for beta>=1/19; no claim against other debits or sources.',
                originals=originals,head_rows=rows,beta=str(beta),
                cylinder_budget_use={str(m):dict(used=str(spent[m]),budget=str(b)) for m,b in sorted(budgets.items())},
                joint_budget_use=str(layout_spent),witness_counts=dict(counts),
                minimum=str(minimum),strict_margin=str(minimum-1),
                rowwise_lower={str(x):str(scores[x]) for x in rows},geometric_checks=geometric,
                finite_witness=dict(height=height,period=period,numerical_slots=108,
                                    centres=centres,minimum=str(finite_minimum),
                                    margin=str(finite_minimum-1)))


def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--witnesses',type=Path,default=Path(__file__).resolve().with_name('fibre_credit_depth_two_joint_obstruction_witnesses.json'))
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate(args.witnesses)))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
        need(retained==result,'retained result agrees with the exact dual reconstruction')
        print(rendered,end='')
    else:args.output.write_text(rendered)


if __name__=='__main__':main()
