"""Exact finite audit for GoldenBase4ZeroTailForgetting.
Usage: python check_zero_tail_forgetting.py reference.lean new.lean companion.cs
All universal claims remain in the uncompiled Lean candidate. This checks its
finite table premises, separate exact arithmetic instances, and source handles.
"""
from pathlib import Path
from math import isqrt
from collections import deque
import re,ast,sys,json,hashlib


def require(p,msg):
 if not p:raise ValueError(msg)
def table(text,name):
 m=re.search(r'def '+re.escape(name)+r'\s*:[\s\S]*?:=\s*!\[([^]]*)\]',text)
 require(m is not None,'missing '+name)
 return ast.literal_eval('['+m.group(1)+']')
def check(ref,source,scribe):
 A,B,O=(table(ref,n) for n in ['zeroTarget','oneTarget','output'])
 require(len(A)==len(B)==len(O)==21,'table size')
 def run(w):
  q=0
  for a in w:
   require(a==0 or q<14,'invalid consecutive ones')
   q=(A if a==0 else B)[q]
  return q
 neg=lambda q:1<=q<=5;pos=lambda q:6<=q<=9
 require(all(pos(A[q]) and O[q]==3 for q in range(1,6)),'negative core')
 require(all(neg(A[q]) and O[q]==0 for q in range(6,10)),'positive core')
 require(all(neg(A[A[q]]) for q in range(14,21)),'two-zero entry')
 paths={0:[]};queue=deque([0])
 while queue:
  q=queue.popleft()
  for a in range(2 if q<14 else 1):
   t=(A if a==0 else B)[q]
   if t not in paths:paths[t]=paths[q]+[a];queue.append(t)
 require(len(paths)==21,'all access states')
 fl=lambda x:(x+isqrt(5*x*x))//2
 def value(w):
  q,v=0,0
  for a in w:q,v=v+a,q+v+2*a
  return q
 count=0
 for q in range(14,21):
  require(run(paths[q])==q,'access word')
  for l in range(2,102):
   w=paths[q]+[0]*l;x=value(w);digit=3 if l%2==0 else 0
   require(fl(4*x)-4*fl(x)==digit,'arithmetic parity law')
   require(O[run(w)]==digit,'table parity law')
   count+=1
 expected=['longTailDigit','zero_tail_output','zero_tail_arithmetic_digit','free_tail_completion_iff']
 for name in expected:
  require(re.search(r'^(?:def|theorem) '+name+r'\b',source,re.M) is not None,'source '+name)
  require('Prefix + "'+name+'"' in scribe,'Scribe '+name)
 # Exhaust all 2-state fixed short readouts. An independent long readout can
 # be chosen constant without changing either fixed short readout.
 cases=0
 from itertools import product
 for G in product(range(4),repeat=2):
  for E in product(range(4),repeat=2):
   R=lambda k,t: G[t] if k==0 else E[t] if k==1 else (3 if k%2==0 else 0)
   require(all(R(0,t)==G[t] and R(1,t)==E[t] for t in range(2)),'short readouts changed')
   require(all(R(k,t)==(3 if k%2==0 else 0) for k in range(2,15) for t in range(2)),'long completion')
   cases+=1
 return {'status':'PASS','negative_core_states':5,'positive_core_states':4,'transient_entries_checked':7,'exact_arithmetic_tail_cases':count,'independent_readout_pairs_checked':cases,'public_Scribe_handles':len(expected),'kernel_checked':False,'new_state_lower_bound':False}
if __name__=='__main__':
 require(len(sys.argv)==4,'usage: reference Lean Scribe')
 files=[Path(x) for x in sys.argv[1:]];ref,source,scribe=[p.read_text() for p in files]
 result=check(ref,source,scribe)
 rejected=[]
 for name,bad in [('wrong_zero',ref.replace('![0,9,8,7,7,6,','![0,9,8,7,7,5,',1)),('wrong_output',ref.replace('![0,3,3,3,3,3,','![0,2,3,3,3,3,',1))]:
  require(bad!=ref,'mutation did not apply')
  try:check(bad,source,scribe)
  except ValueError:rejected.append(name)
  else:raise ValueError('mutation accepted '+name)
 result['rejected_mutations']=rejected
 result['sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
 print(json.dumps(result,indent=2))
