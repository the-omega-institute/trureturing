"""Arithmetic model shared by the two Report862 controls."""

from pathlib import Path
from itertools import combinations
from math import prod
import json

P=(19,23,29,31,37,41,43,47,53,59,61,67,71,73,79)
q=113
G=10
A=(2,4,5,7,8)
U=tuple(range(30,113))
all_primes=tuple(p for p in range(5,q) if all(p%d for d in range(2,int(p**.5)+1)))
aux=tuple(p for p in all_primes if p not in P)
subsets=[S for k in range(1,4) for S in combinations(P,k)]
triples=[S for S in subsets if len(S)==3]
small=[S for S in subsets if len(S)<3]
cells=[(c,z) for c in U for z in A]
assignment={S:cells[i%len(cells)] for i,S in enumerate(triples)}
protected_cells=[(c,z) for c in range(3,30) for z in A]
assignment.update({S:protected_cells[i] for i,S in enumerate(small)})
assert len(assignment)==len(subsets)

def crt(data):
    n=prod(d for d,r in data)
    return sum(r*(n//d)*pow(n//d,-1,d) for d,r in data)%n if n>1 else 0

phase_colors=json.loads(Path(__file__).with_name('phase_colors.json').read_text())

def build_rows(cell_overrides=None):
    """Build numerical originals with optional support-to-cell replacements."""
    cells_by_support = dict(assignment)
    cells_by_support.update(cell_overrides or {})
    assert set(cells_by_support) == set(subsets)
    rows=[]
    for d,r,a in [(3,0,1),(9,1,2)]:
        rows.append(dict(d=d,r=r,S=(),a=a,j=0))
    for j in range(1,G+1):
        for a in range(3):
            c=3*(j-1)+a
            data=[(q**j,c)]+([(3**a,4%(3**a))] if a else [])
            rows.append(dict(d=3**a*q**j,r=crt(data),S=(),a=a,j=j,c=c,z=4))
    for S in subsets:
        c,z=cells_by_support[S]
        for a in range(3):
          for j in range(2):
            tag=1+a+3*j+6*(len(S)-1)
            if len(S)==3:
                colors=phase_colors[str(j)][','.join(map(str,S))]
                phase={p:13+3*j+(colors[i]+(0 if a==2 else a+1))%3 for i,p in enumerate(S)}
            else:
                phase={p:tag for p in S}
            data=list(phase.items())
            if a: data.append((3**a,z%(3**a)))
            if j: data.append((q,c))
            d=3**a*q**j*prod(S)
            rows.append(dict(d=d,r=crt(data),S=S,a=a,j=j,tag=tag,phase=phase,c=c,z=z))
    for p in aux:
        for a in range(3):
            data=[(p,a)]+([(3**a,4%(3**a))] if a else [])
            rows.append(dict(d=3**a*p,r=crt(data),S=(p,),a=a,j=0,aux=p,phase={p:a},z=4))
    return rows
