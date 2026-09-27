"""Exact core-first terminal-phase elimination for two complete 154-label inputs."""
from fractions import Fraction as F
from functools import lru_cache
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

_spec = importlib.util.spec_from_file_location('terminal_phase_io', Path(__file__).with_name('adaptive_phase_io.py'))
_io = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require, load_module = _io.require, _io.load_module

CERTIFICATE='certificates/source_norms/source-budgets/terminal_phase_reduction.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md', 'problem-details/58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md', 'frontier/source-budgets/adaptive_phase_head_input.json', 'frontier/source-budgets/balanced_profile_head_input.json', 'frontier/source-budgets/capped_head_bellman.py', 'frontier/source-budgets/depth_cap_bellman.py')

def collapsed(s,problem,count_only):
 core=tuple(i for i,p in enumerate(problem.primes) if p<23)
 leaves=tuple(i for i,p in enumerate(problem.primes) if p>=23)
 require(core==tuple(range(7)) and len(leaves)==13,'exact intended partition')
 buckets={i:tuple(j for j,row in enumerate(problem.rows) if row[i][0]) for i in leaves}
 for j,row in enumerate(problem.rows):require(sum(bool(row[i][0]) for i in leaves)<=1,'no two-leaf original label')
 for i in leaves:
  require(problem.heights[i]==1 and all(problem.rows[j][i][0]==1 for j in buckets[i]),'leaf height1')
  require(len(buckets[i])<=problem.primes[i],'global injection feasible')
 @lru_cache(None)
 def value(axis,active):
  if not active:return F(0)
  if any(problem.last_axis[j]<axis for j in active):return F(1)
  if axis==len(core):
   survival=F(1)
   for i in leaves:
    incident=[j for j in active if problem.rows[j][i][0]]
    n=len(incident) if count_only else len({problem.rows[j][i][1] for j in incident})
    survival*=min(F(1),problem.profiles[i][1]*(problem.primes[i]-n))
   return 1-survival
  return s.compressed_row(problem.primes[axis],problem.heights[axis],problem.profiles[axis],problem.by_axis[axis],active,lambda hits:value(axis+1,hits))[0]
 return value(0,tuple(range(len(problem.labels)))),value.cache_info().currsize

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    weak=ctx.read('frontier/source-budgets/adaptive_phase_head_input.json')
    profile=ctx.read('frontier/source-budgets/balanced_profile_head_input.json')
    literal=load_module('terminal_phase_original_labels',Path(base)/'frontier/source-budgets/capped_head_bellman.py')
    original=dict(labels=[list(pair) for pair in literal.counterexample_154_labels()])
    require(weak['profiles']==profile['profiles'] and weak['prime_order']==profile['prime_order'] and weak['heights']==profile['heights'],'same complete balanced profile')
    require(len(original['labels'])==len(weak['labels'])==154,'two complete original inputs')
    require([(x,y) for x,y in zip(original['labels'],weak['labels']) if x!=y]==[([39,22],[39,14]),([45,43],[45,26]),([55,11],[55,28]),([63,7],[63,32])],'exact four globally fixed residue edits')
    s=load_module('terminal_phase_existing_solver',Path(base)/'frontier/source-budgets/depth_cap_bellman.py')
    records=[]
    for name,labels in [('original',original['labels']),('four-change',weak['labels'])]:
     p=s.HeadProblem(weak['prime_order'],weak['heights'],labels,weak['profiles'])
     literal=p.optimum();cl,cs=collapsed(s,p,False);require(literal==cl,'literal full20 equals collapsed core7')
     injected=[];buckets={q:[] for q in weak['prime_order'] if q>=23}
     for m,a in labels:
      qs=[q for q in buckets if m%q==0]
      require(len(qs)<=1,'one leaf per original modulus')
      if not qs:injected.append([m,a]);continue
      q=qs[0];target=len(buckets[q]);buckets[q].append(m);cofactor=m//q
      require(m% (q*q) !=0 and target<q,'valid distinct leaf phase')
      new=a%cofactor + cofactor*((target-a%cofactor)*pow(cofactor,-1,q)%q)
      require(0<=new<m and new%cofactor==a%cofactor and new%q==target,'faithful original CRT phase')
      injected.append([m,new])
     worst,ws=collapsed(s,p,True)
     q=s.HeadProblem(weak['prime_order'],weak['heights'],injected,weak['profiles']);full_worst=q.optimum()
     require(worst==full_worst and worst>=literal,'simultaneous global worst leaf phases')
     require([m for m,a in labels]==[m for m,a in injected],'original numerical label IDs')
     record={'input':name,'literal_full20':str(literal),'literal_collapsed7':str(cl),'worst_leaf_full20':str(full_worst),'worst_leaf_collapsed7':str(worst),'worst_leaf_decimal':float(worst),'gap':str(worst-literal),'literal_states':p.value.cache_info().currsize,'literal_collapsed_states':cs,'worst_collapsed_states':ws,'injected_labels':injected,'leaf_label_counts':{str(q):len(v) for q,v in buckets.items()}}
     records.append(record)
     p.value.cache_clear();q.value.cache_clear()
    result=dict(schema='globally-simultaneous-terminal-phase-reduction-v1',scope='Core-first fixed numerical core order; two input diagnostics only. The general terminal-phase reduction is proved separately in the chapter. No uniform arbitrary-core phase bound claimed.',prime_order=weak['prime_order'],heights=weak['heights'],profiles=weak['profiles'],original_labels=original['labels'],four_change_labels=weak['labels'],records=records)
    return ctx.finish(result)


if __name__ == "__main__":
    _io.run(CERTIFICATE,calculate,__file__)
