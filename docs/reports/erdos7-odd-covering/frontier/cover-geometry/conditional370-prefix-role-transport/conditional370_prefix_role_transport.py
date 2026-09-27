#!/usr/bin/env python3
"""Finite exhaustive role-alignment checks for Report635's prime transport.
Checks the source alphabets3,5, all partial distinguished-role embeddings and
one designated second digit. Ordinary proof supplies arbitrary target primes,
all finite heights, the same-family pullback and exact Haar averaging.
No survivor scan, numerical target-prime cutoff or new Lean claim.
"""
import argparse,json
from itertools import combinations,permutations,product
from pathlib import Path
from hashlib import sha256
checks={}
def ck(name,condition):
 if not condition:raise ArithmeticError(name)
 checks[name]=True

def assignments(p,n):
 for k in range(n+1):
  for roles in combinations(range(n),k):
   for vals in permutations(range(p),k):yield dict(zip(roles,vals))

def align(p,targets,parent,partial,child):
 full=dict(partial);used=set(full.values())
 for role in range(len(targets)):
  if role not in full:
   full[role]=min(set(range(p))-used);used.add(full[role])
 perm={full[role]:target for role,target in enumerate(targets)}
 for x,y in zip(sorted(set(range(p))-set(perm)),sorted(set(range(p))-set(perm.values()))):perm[x]=y
 u=0 if child is None else child
 second=list(range(p));second[u],second[0]=second[0],second[u]
 def tree(word):
  out=list(word);out[0]=perm[word[0]]
  if len(word)>1 and word[0]==full[parent]:out[1]=second[word[1]]
  return tuple(out)
 return full,perm,second,tree

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=ap.parse_args()
 specs=((3,(2,0),1),(5,(4,0,2),2));records=[];totals={}
 for p,targets,parent in specs:
  parts=list(assignments(p,len(targets)));ck(f'partial_first_count_{p}',len(parts)==(13 if p==3 else 136))
  n=0
  for idx,part in enumerate(parts):
   # A visible child requires its designated first role to be visible.
   children=[None]+list(range(p)) if parent in part else [None]
   for child in children:
    key=f'{p}_{idx}_{child}';full,perm,second,tree=align(p,targets,parent,part,child)
    ck(key+'_extends_visible_roles',all(full[k]==v for k,v in part.items()))
    ck(key+'_distinct_completion',len(set(full.values()))==len(targets))
    ck(key+'_root_permutation',set(perm)==set(perm.values())==set(range(p)))
    ck(key+'_child_permutation',set(second)==set(range(p)))
    ck(key+'_canonical_first_roles',all(perm[full[k]]==v for k,v in enumerate(targets)))
    if child is not None:ck(key+'_visible_child_role',tree((part[parent],child))==(targets[parent],0))
    for depth in (1,2,3):
     words=list(product(range(p),repeat=depth));images=[tree(w)for w in words]
     ck(key+f'_depth{depth}_bijection',len(set(images))==p**depth)
     ck(key+f'_depth{depth}_prefix_preservation',all(tree(w)[:j]==tree(w[:j])for w in words for j in range(1,depth+1)))
     ck(key+f'_depth{depth}_suffix_identity',all(tree(w)[2:]==w[2:]for w in words))
    # All first-role and designated-child cylinders are tested together on
    # the SAME tree permutation; there is no label-specific relabelling.
    words=list(product(range(p),repeat=2))
    ck(key+'_all_visible_first_cylinders',all((w[0]==value)==(tree(w)[0]==targets[role])for w in words for role,value in part.items()))
    if child is not None:
     ck(key+'_designated_leaf_cylinder',all((w==(part[parent],child))==(tree(w)==(targets[parent],0))for w in words))
    records.append({'prime':p,'visible_first_roles':{str(k):v for k,v in part.items()},'visible_child':child,'completed_first_roles':[full[k]for k in range(len(targets))],'first_permutation':[perm[k]for k in range(p)],'designated_child_permutation':second})
    n+=1
  totals[str(p)]={'partial_first_assignments':len(parts),'joint_first_child_cases':n,'designated_parent_role':parent,'canonical_first_roles':list(targets)}
 out={'schema':'conditional370-prefix-role-transport-v1','status':'PASS','scope':__doc__,'source_alphabets':totals,'alignments':records,'check_count':len(checks),'checks':checks,'new_lean_verification':False,'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
 args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'PASS','check_count':len(checks),'source_alphabets':totals},indent=2))
if __name__=='__main__':main()
