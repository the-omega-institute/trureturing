"""Exact interval-source mutations and exhaustive finite recurrence regression.
Run: python check_interval_regression.py path/to/GoldenBase4IntervalMachine.lean
This program does not execute Lean or prove an infinite-domain statement.
"""
from pathlib import Path
import importlib.util
import itertools
import json
import sys
root=Path(__file__).parent
if len(sys.argv)!=2:
    raise SystemExit('usage: check_interval_regression.py Lean_table_file')
source_path=Path(sys.argv[1])
spec=importlib.util.spec_from_file_location('checker',root/'check_interval_source.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
report=mod.check(source_path)
from tempfile import TemporaryDirectory
source=(source_path).read_text()
mutations={'wrong_zero_target':source.replace('![0,9,8,7,7,6,','![0,9,8,7,7,0,',1),
'wrong_one_target':source.replace('![18,20,19,19,','![17,20,19,19,',1),
'wrong_output':source.replace('![0,3,3,3,3,3,','![0,2,3,3,3,3,',1),
'wrong_endpoint':source.replace('![(0,0),(12,-8),','![(0,0),(12,-7),',1)}
results=[]
with TemporaryDirectory() as tmp:
 for name,code in mutations.items():
  p=Path(tmp)/'bad.lean';p.write_text(code)
  try:mod.check(p)
  except (ValueError,AssertionError):results.append(name)
  else:raise RuntimeError('unrejected mutation '+name)
report['rejected_mutations']=results
fs=[0,1]
for _ in range(20):fs.append(sum(fs[-2:]))
def pair(w):return sum(a*fs[len(w)-i+1] for i,a in enumerate(w)),sum(a*fs[len(w)-i+2] for i,a in enumerate(w))
checks=0
for n in range(13):
 for w in itertools.product([0,1],repeat=n):
  q,v=pair(w)
  for a in [0,1]:
   assert pair(w+(a,))==(v+a,q+v+2*a);checks+=1
report['fib_append_regression_checks']=checks
print(json.dumps(report,indent=2))
