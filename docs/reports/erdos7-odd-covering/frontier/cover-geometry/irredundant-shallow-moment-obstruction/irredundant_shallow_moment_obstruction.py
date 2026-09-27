#!/usr/bin/env python3
"""Fixed 35-label obstruction; no full-period or earlier-producer enumeration.
Checks actual numerical labels and private witnesses, then exact new bounds.
"""
from fractions import Fraction as F
from itertools import combinations
from math import prod,comb
from pathlib import Path
import json
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
P=(3,5,7,11,13,17,19);L=prod(P)
subsets=list(combinations(P,3));labels=[prod(S) for S in subsets]
def need(v,msg):
 if not v:raise ValueError(msg)
def crt(vals):return sum(a*(L//p)*pow(L//p,-1,p) for p,a in vals.items())%L
witnesses=[]
for S,d in zip(subsets,labels):
 x=crt({p:0 if p in S else 1 for p in P})
 hits=[e for e in labels if x%e==0]
 need(hits==[d],'private witness failed')
 witnesses.append({'modulus':d,'residue':0,'private_integer':x})
need(len(labels)==len(set(labels))==35 and max(labels)==4199 and all(d%2 and d>1 for d in labels),'label mismatch')
need(all(1%d!=0 and 2%d!=0 for d in labels),'explicit survivors fail')
S3=sum((F(1,d) for d in labels),F(0));D=prod(F(p,p-1) for p in P)
# Complete actual survivor has at most two zero-root coordinates.
U_count=sum(prod(p-1 for p in P if p not in Z) for k in range(3) for Z in combinations(P,k))
h=F(U_count,L)
need(1>=h>=1-S3>0,'survivor union lower inconsistent')
R_upper=(D-1)/h
need(R_upper<3,'good same full-survivor law bound failed')
alpha=F(7235955529,6075000000000);Lam=1/alpha
need(1/h<Lam and h*Lam>27,'density or entropy budget comparison failed')
# Exactly five roots are 1: the other two can have any non-1 values.
N5=sum((p-1)*(q-1) for p,q in combinations(P,2))
pair_lower=F(comb(comb(5,3),2)*N5,L)
moment_lower=F(2**35,L)
need(N5==1872 and pair_lower>F(1,329),'pair obstruction fails')
need(moment_lower>7000>F(384,5),'exponential moment obstruction fails')
out={'primes':list(P),'period':L,'original_count':35,'max_original_modulus':max(labels),'originals_with_private_witnesses':witnesses,
 'private_membership_checks':35*35,'full_period_enumerated':False,'survivor_root_rule':'number of coordinates equal to 0 is at most 2',
 'survivor_count':U_count,'survivor_Haar_mass':str(h),'reciprocal_original_sum':str(S3),'Euler_product':str(D),
 'uniform_complete_survivor_density':str(1/h),'uniform_complete_survivor_all_depth_R_upper':str(R_upper),
 'query_rule':'phase 1 at every one of the 35 original numerical labels',
 'query_load_rule':'binomial(number of coordinates equal to 1, 3)',
 'load_at_survivor_1':35,'load_at_survivor_2':0,
 'exponential_moment_strict_rational_lower':str(moment_lower),'five_one_root_count':N5,'pair_integral_lower':str(pair_lower),
 'entropy_bridge':'rho=uniform(U) has KL(rho||rho)=0, R_unused(rho)<=R_P(rho)<3<log(H(U)/alpha); last inequality uses H(U)/alpha>27>exp(3)',
 'thresholds_passed':{'moment_above_76_8':True,'pair_above_1over329':True,'all_depth_query_below3':True,'GD_unused_KL_budget':True}}
content=json.dumps(out,indent=2)+'\n'
if args.output is None:
 print(content,end='')
else:
 args.output.write_text(content,encoding='utf-8')
