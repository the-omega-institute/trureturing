"""Exact reciprocal tail and Taylor bounds for legal phase resampling.
Uses the report467 survivor lower bound, with fixed cutoff 10^9.
The arithmetic does not verify the resampling or minimax arguments.
"""
import argparse
from fractions import Fraction as F
from decimal import Decimal, localcontext
from math import prod
import json
from pathlib import Path
P=(3,5,7,11,13,17,19)
cutoff=10**9
labels=[1]
for p in P:
    extended=[]
    for d in labels:
        while d<=cutoff:
            extended.append(d)
            d*=p
    labels=extended
if len(labels)!=len(set(labels)):raise ValueError('duplicate smooth label')
labels.sort()
alpha=F(7235955529,6075000000000)
tail=prod(F(p,p-1) for p in P)-sum((F(1,d) for d in labels),F(0))
beta=alpha-tail
T=F(565,51)
a=T-F(69,20)
def exp_lower(x,n):
    term=total=F(1)
    for i in range(1,n+1):
        term*=x/i
        total+=term
    return total
checks={
 'nonunit_count_15524':len(labels)-1==15524,
 'positive_beta':beta>0,
 'exp_27over4_degree13_above840':exp_lower(F(27,4),13)>840,
 'log_cost_below_6737023over1million':beta*exp_lower(F(6737023,10**6),50)>1,
 'exponential_moment_above_384over5':beta*exp_lower(T,60)>F(384,5),
 'pair_bound_above_1over329':F(87,20)*(beta-1/exp_lower(a,50))>F(1,329),
 'uncut_pair_bound_above_1over327':F(87,20)*(alpha-1/exp_lower(a,50))>F(1,327),
}
if not all(checks.values()):raise ValueError(checks)
with localcontext() as ctx:
    ctx.prec=65
    dec=lambda x:Decimal(x.numerator)/Decimal(x.denominator)
    out={'cutoff':cutoff,'nonunit_label_count':len(labels)-1,
         'alpha':str(alpha),'tail':str(tail),'beta':str(beta),
         'tail_decimal':str(dec(tail)),'beta_decimal':str(dec(beta)),
         'negative_log_beta_decimal':str(-dec(beta).ln()),
         'remaining_threshold_decimal':str(dec(T)+dec(beta).ln()),
         'exponential_moment_decimal':str(dec(beta)*dec(T).exp()),
         'pair_lower_rational':str(F(87,20)*(beta-1/exp_lower(a,50))),
         'checks':checks}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
content=json.dumps(out,indent=2)+'\n'
if args.output is None:
    print(content,end='')
else:
    args.output.write_text(content,encoding='utf-8')
