#!/usr/bin/env python3
"""Exact common-label capacities for the eleven head cofactors of315."""
from itertools import combinations
from fractions import Fraction as F
from math import gcd,lcm
from pathlib import Path
import json


def need(ok,msg):
 if not ok:raise RuntimeError(msg)


def crt_pair(c,a,q,b):
 return (a+c*((b-a)*pow(c,-1,q)%q))%(c*q)


def calculate():
 C=tuple(c for c in range(2,316) if 315%c==0)
 need(C==(3,5,7,9,15,21,35,45,63,105,315),'eleven literal cofactor slots')
 pair={d:sum(d%c==0 for c in C) for d in range(1,315)}
 need(max(pair.values())==7 and [d for d,v in pair.items() if v==7]==[105,210],
      'only two distinct-row differences can share seven cofactor phases')
 triple_caps=[]
 for a in range(105):
  rows=(a,a+105,a+210)
  cap=sum(max(sum(x%c==r for x in rows) for r in range(c)) for c in C)
  need(cap==25,'three rows in one105-fiber have at most25 total active incidences')
  triple_caps.append(cap)
 moments={}
 for r in range(1,12):
  coefficients={}
  for subset in combinations(C,r):
   d=lcm(*subset);coefficients[d]=coefficients.get(d,0)+1
  moments[str(r)]={str(d):n for d,n in sorted(coefficients.items())}
  need(sum(coefficients.values())==len(list(combinations(C,r))),'every original-label subset counted once')
 examples=[]
 pure=((3,0),(9,1),(5,0),(7,0))
 heads=(pure+((15,11),(45,2),(21,1),(63,58),(35,3),(105,74),(315,187)),
        pure+((15,1),(45,22),(21,1),(63,16),(35,3),(105,74),(315,47)))
 for head,size in zip(heads,(75,85)):
  need(len({m for m,a in head})==11 and sum(all(x%m!=a for m,a in head) for x in range(315))==size,
       'literal eleven-original actual head support')
 for name in ('one_dead_row','two_nine_rows'):
  phases={c:4 for c in C}
  if name=='two_nine_rows':
   for c in (63,315):phases[c]=214%c
  low=[c for c in C if 105%c==0]
  roots={c:i+1 for i,c in enumerate(low)}
  roots.update({9:8,45:9,63:8,315:9})
  if name=='one_dead_row':roots={c:1+i%10 for i,c in enumerate(C)}
  originals=[dict(a=crt_pair(c,phases[c],11,roots[c]),m=11*c) for c in C]
  n=[sum(x%c==phases[c]%c for c in C) for x in range(315)]
  blocked=[{r['a']%11 for r in originals if x%(r['m']//11)==r['a']%(r['m']//11)} for x in range(315)]
  highs=[x for x in range(315) if n[x]>=9]
  dead=[x for x in range(315) if len(blocked[x]-{0})==10]
  if name=='one_dead_row':need(dead==[4] and n[4]==11,'actual11-coordinate dead-row upper is attained once')
  else:need(highs==[4,214] and n[4]==n[214]==9 and all(len(blocked[x])==9 for x in highs),
            'two nine-active rows are realized by one actual phase assignment')
  for head in heads:
   need(all(all(x%m!=a for m,a in head) for x in highs),
        'sharp rows are actual live cells in both declared heads')
  examples.append(dict(name=name,actual_q11_star_originals=originals,
    head_rows_n_ge_9=highs,head_rows_n_ge_10=[x for x in range(315) if n[x]>=10],
    head_rows_with_no_pure_live_q11_root=dead,maximum_active_labels=max(n)))
 out=dict(scope='First nonternary digits only, whole ternary height<=2. One global phase for each present c*q label, c a nonunit divisor315. Higher original heights are not included in these row-count claims.',
   head_cofactors=list(C),maximum_pair_common_cofactors=7,pair_extremal_differences=[105,210],
   compatible_triples_checked=105,triple_capacity=25,
   maximum_rows_n_ge_10=1,maximum_rows_n_ge_9=2,
   first_digit_unary_mass_after_discarding_bad_rows={'11':'1/5','13':'1/4','17':'1/2','19':'1/2'},
   four_axis_bad_row_union_at_most=6,weighted_head_bad_mass_upper='1/16',
   binomial_moment_coefficients=moments,sharp_actual_examples=examples)
 return out


def main():
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 result=json.loads(json.dumps(calculate()))
 rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
 if args.output is None:
  retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
  need(retained==result,'retained result agrees with exact reconstruction')
  print(rendered,end='')
 else:
  args.output.write_text(rendered)

if __name__=='__main__':main()
