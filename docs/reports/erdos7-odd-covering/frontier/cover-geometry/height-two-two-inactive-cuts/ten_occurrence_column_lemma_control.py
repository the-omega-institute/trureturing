"""Exact seven-column necessary-count control; not an actual source search.
Predeclared expectation: whenever all six pairs of four total2 column
vectors become 3*indicator(T)+one excess after one nonnegative offset of
total6, they have one common branch triple and at least three equal vectors.
"""
from itertools import combinations_with_replacement,combinations
from collections import Counter
from pathlib import Path
from hashlib import sha256
import json
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, required=True, help="Result JSON path")
args=parser.parse_args()
n=7
vectors=[]
for i,j in combinations_with_replacement(range(n),2):
 v=[0]*n;v[i]+=1;v[j]+=1;vectors.append(tuple(v))
def pack(v):return sum(x<<(4*i)for i,x in enumerate(v))
patterns={}
for T in combinations(range(n),3):
 for j in range(n):
  v=[0]*n
  for i in T:v[i]=3
  v[j]+=1;patterns[pack(v)]=(tuple(v),T)
vc=[pack(v)for v in vectors];offset_cache={};passed=0;families=0;tested=0;bad=[]
for ids in combinations_with_replacement(range(len(vectors)),4):
 families+=1
 pairs=[vc[ids[i]]+vc[ids[j]]for i,j in combinations(range(4),2)]
 first=pairs[0]
 if first not in offset_cache:
  fv=tuple((first>>(4*i))&15 for i in range(n));choices=[]
  for target,(tv,T)in patterns.items():
   if all(tv[i]>=fv[i]for i in range(n)):choices.append(target-first)
  offset_cache[first]=choices
 for off in offset_cache[first]:
  tested+=1
  if not all(off+p in patterns for p in pairs):continue
  passed+=1
  branches={patterns[off+p][1]for p in pairs}
  if len(branches)!=1 or max(Counter(ids).values())<3:bad.append({'vectors':[vectors[i]for i in ids],'offset':[(off>>(4*i))&15 for i in range(n)],'branches':list(branches)})
if bad:raise ArithmeticError(json.dumps(bad[:5]))
result={'scope':'Necessary ten-occurrence count equations only, not actual fibres or universal source supplier','columns':n,'double_types':len(vectors),'four_double_multisets':families,'nonnegative_translations_tested':tested,'feasible_translations':passed,'branch_change_or_less_than_three_equal_counterexamples':len(bad),'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
