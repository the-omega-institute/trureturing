"""Generate the saved three-support phase colors with a bounded fixed-seed search."""

from pathlib import Path
from itertools import combinations,product
from collections import Counter
import random,json
P=(19,23,29,31,37,41,43,47,53,59,61,67,71,73,79)
triples=list(combinations(P,3))
A=(2,4,5,7,8)
U=tuple(range(30,113))
cells=[(c,z) for c in U for z in A]
assignment={S:cells[i%len(cells)] for i,S in enumerate(triples)}
allcolors=list(product(range(3),repeat=3))

def keys(S,col):
 z=assignment[S][1]
 phases=dict(zip(S,col))
 pairkeys=[(z,(p,r),(phases[p],phases[r])) for p,r in combinations(S,2)]
 querykeys=[]
 # P=S: exact vector and its six Hamming-distance-one neighbors.
 for w in allcolors:
  if sum(w[i]==col[i] for i in range(3))>=2:
   querykeys.append((z,S,w))
 # P meets S in precisely two elements.
 for pair in combinations(S,2):
  for p in P:
   if p not in S:
    T=tuple(sorted(pair+(p,)))
    for c in range(3):
     w=tuple(c if x==p else phases[x] for x in T)
     querykeys.append((z,T,w))
 return pairkeys,querykeys

out={}
for j,cap in [(0,4),(1,4)]:
 for seed in range(1):
  rng=random.Random(47101+seed+1000*j)
  pc=Counter(); qc=Counter(); chosen={}
  order=list(triples); rng.shuffle(order)
  for S in order:
   candidates=list(allcolors); rng.shuffle(candidates)
   for col in candidates:
    pkeys,qkeys=keys(S,col)
    if j:
     c,z=assignment[S]
     pkeys=pkeys+[("q",z,c,p,color) for p,color in zip(S,col)]
    if all(pc[k]<1 for k in pkeys) and all(qc[k]<cap for k in qkeys):
     chosen[S]=col; pc.update(pkeys); qc.update(qkeys); break
   else: break
  if len(chosen)==len(triples):
   out[j]={','.join(map(str,S)):col for S,col in chosen.items()}
   print('j',j,'seed',seed,'pair_max',max(pc.values()),'query_max',max(qc.values()),'owners',len(chosen),flush=True)
   break
 else: raise RuntimeError('no coloring')
Path(__file__).with_name('phase_colors.json').write_text(json.dumps(out,sort_keys=True)+'\n')
