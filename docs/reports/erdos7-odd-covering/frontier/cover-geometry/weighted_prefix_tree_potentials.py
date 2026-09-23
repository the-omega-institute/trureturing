#!/usr/bin/env python3
"""Exact finite controls for report 376's weighted prefix-tree lemma.

Prices include both prefix depths, with rational arithmetic throughout.
The binary branching parameter is a combinatorial control, not a witness
to a minimum odd cover. The unrestricted lemma is proved in the report.
"""
from itertools import combinations, product
from fractions import Fraction as F
import json

# p=3, b=2, H=2. Prefix vertices0..2 are at depth1;
# vertices3..11 are leaves, grouped by their first digit.
branch_pairs=list(combinations(range(3),2))
trees=[]
for roots in branch_pairs:
    for children in product(branch_pairs,repeat=2):
        trees.append(tuple(3*root+digit for root,chosen in zip(roots,children)
                           for digit in chosen))
if len(set(trees))!=27:raise ValueError('wrong complete binary tree enumeration')

def verify(prices):
    scores=[prices[x//3]+prices[3+x] for x in range(9)]
    costs=[max(scores[x] for x in tree) for tree in trees]
    threshold=min(costs)
    budget=sum(prices[:3],F(0))/2+sum(prices[3:],F(0))/4
    if threshold>budget:raise ValueError(('potential lemma fails',prices))
    chosen=trees[costs.index(threshold)]
    if any(scores[x]>budget for x in chosen):raise ValueError('chosen tree violates cap')
    return budget-threshold,chosen,budget,threshold

count=tight=0
for prices in product((0,1),repeat=12):
    gap,*_=verify(prices)
    count+=1;tight+=gap==0
# Deterministic rational prices, varying independently by level and position.
rational=[]
for k in range(1,28):
    prices=[F((i*i+(k+2)*i+3*k)%19,(i+k)%7+1) for i in range(12)]
    gap,tree,budget,threshold=verify(prices)
    rational.append(dict(k=k,prices=list(map(str,prices)),tree=tree,
                         budget=str(budget),minimum_tree_max=str(threshold),margin=str(gap)))
# An exact minimum four-leaf blocker: wrong p^-depth pricing would fail.
blocker=[0]*12
for leaf in [0,1,3,4]:blocker[3+leaf]=1
_,tree,budget,threshold=verify(blocker)
wrong_budget=F(sum(blocker[:3]),3)+F(sum(blocker[3:]),9)
if not (budget==threshold==1 and wrong_budget==F(4,9)<threshold):
    raise ValueError('mutation control failed')
print(json.dumps(dict(p=3,b=2,H=2,r=2,tree_count=len(trees),
                      all_binary_price_assignments=count,tight_assignments=tight,
                      rational_price_assignments=len(rational),rational_controls=rational,
                      negative_control=dict(prices=blocker,correct_budget=str(budget),
                                            wrong_p_inverse_depth_budget=str(wrong_budget),
                                            every_tree_max_at_least=str(threshold)),
                      scope='Finite potential-lemma controls only; b=2 is not an odd-cover transport'),indent=2))
