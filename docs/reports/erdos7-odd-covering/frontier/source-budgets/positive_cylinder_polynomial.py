"""A fixed actual cylinder cover counted as a positive multiaffine polynomial."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,prod
from pathlib import Path
import importlib.util
import sys
sys.dont_write_bytecode=True

_spec=importlib.util.spec_from_file_location('positive_cylinder_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require,load_module=_io.require,_io.load_module

CERTIFICATE='certificates/source_norms/source-budgets/positive_cylinder_polynomial.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/60-positive-cylinder-covers-across-head-profiles.md', 'problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'frontier/source-budgets/uniform_phase_capacity.py', 'certificates/source_norms/source-budgets/uniform_phase_capacity.json')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    INPUT='frontier/source-budgets/uniform_phase_capacity_input.json'
    require(sha256(ctx.raw(INPUT)).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','same complete seven-phase survivor geometry')
    expected=ctx.fresh('certificates/source_norms/source-budgets/uniform_phase_capacity.json','frontier/source-budgets/uniform_phase_capacity.py')
    D=ctx.read(INPUT);P=D['prime_order'];H=D['heights'];L=D['labels'];r=[F(row[-1]) for row in D['profiles']];sizes=[p**h for p,h in zip(P,H)];core=7
    last=[max(i for i,p in enumerate(P) if m%p==0) for m,a in L];complete=[sum(1<<j for j,e in enumerate(last) if e<i) for i in range(len(P)+1)];matches=[]
    for size in sizes:
     q=[gcd(m,size) for m,a in L]
     matches.append(tuple(sum(1<<j for j,((m,a),qj) in enumerate(zip(L,q)) if x%qj==a%qj) for x in range(size)))
    leaflabels=[tuple(j for j,(m,a) in enumerate(L) if m%P[i]==0) for i in range(core,len(P))]
    @lru_cache(None)
    def node(i,active):
     if not active:return F(1)
     if active&complete[i]:return F(0)
     if i==core:
      return prod(min(F(1),r[k]*(P[k]-len({L[j][1]%P[k] for j in ids if active>>j&1}))) for k,ids in enumerate(leaflabels,core))
     return min(F(1),r[i]*sum(mul*node(i+1,a) for a,mul in Counter(active&m for m in matches[i]).items()))
    @lru_cache(None)
    def poly(i,active):
     val=node(i,active)
     if val==0:return ()
     if val==1:return ((0,1),)
     if i==core:
      mask=0;coef=1
      for k,ids in enumerate(leaflabels,core):
       allowed=P[k]-len({L[j][1]%P[k] for j in ids if active>>j&1})
       if allowed*r[k]<1:mask|=1<<k;coef*=allowed
      return ((mask,coef),)
     ans=Counter()
     for a,mul in Counter(active&m for m in matches[i]).items():
      for mask,c in poly(i+1,a):ans[mask|(1<<i)]+=mul*c
     return tuple(sorted(ans.items()))
    active=(1<<len(L))-1;terms=poly(0,active);value=sum((c*prod(r[i] for i in range(len(P)) if mask>>i&1) for mask,c in terms),F(0))
    if value!=node(0,active) or value!=F(expected['partial_cylinder']['survival_upper']):raise ValueError('frozen polynomial evaluates to certified cover cost')
    require(len(terms)==38 and sum(c for mask,c in terms)==12533129880604949291,'complete frozen cover coefficient inventory')
    require(all(c>0 and 0<=mask<1<<20 for mask,c in terms),'positive integer coefficients on original20 coordinates')
    result={'schema':'fixed-survivor-positive-cylinder-polynomial-v1','scope':'The same actual seven-phase survivor cover on all20 named full-height coordinates. Its positive multiaffine polynomial bounds survivor mass at new deterministic full-history atom caps for any adaptive sampling order. It does not exclude every profile or reuse old continuation budgets at changed profiles.','terms':[{'coordinate_mask':mask,'primes':[p for i,p in enumerate(P) if mask>>i&1],'coefficient':str(c)} for mask,c in terms],'term_count':len(terms),'expanded_cylinders':str(sum(c for mask,c in terms)),'balanced_value':str(value)}
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
