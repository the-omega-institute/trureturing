#!/usr/bin/env python3
'''Counted, controlled source searches; no orchestrator scripts are read.'''
import json
import shlex
import subprocess
import sys
from pathlib import Path

scope = sys.argv[1]
root = '.lake/packages/mathlib/Mathlib' if scope == 'mathlib' else 'D5'
queries = [
 ('characterisation', r'HasReverseMultipleProperty|reverseBase|reverseB\b|reverse.{0,50}(any|all).{0,30}multiple|multiple.{0,50}revers|\bAyad\b|\bBouchenna\b', 'ofDigits'),
 ('reversal', r'ofDigits_reverse_cons|ofDigits_reverse_zero_cons|digits_ofDigits|digits_append|eleven_dvd_iff', 'digits'),
 ('order', r'orderOf_pos|pow_orderOf_eq_one|orderOf_eq_one_iff|isUnit_iff_coprime|pow_totient', 'ZMod'),
]
if scope != 'mathlib':
 roots = ['D5', 'Problems', 'Library', 'Blueprint']
else:
 roots = [root]
records = []
for name, pattern, control in queries:
 def search(p):
  cmd = ['rg', '-n', '-i', '-g', '*.lean' if scope == 'mathlib' else '*', p, *roots]
  run = subprocess.run(cmd, text=True, capture_output=True)
  if run.returncode not in (0,1):
   raise RuntimeError(run.stderr)
  return dict(command=shlex.join(cmd), exit=run.returncode,
              count=len(run.stdout.splitlines()), hits=run.stdout.splitlines()[:200])
 result, positive = search(pattern), search(control)
 assert positive['count'] > 0
 positive['hits'] = positive['hits'][:3]
 records.append(dict(name=name, query=result, positive_control=positive))
 print(name, 'hits', result['count'], 'control', positive['count'])
 if name == 'characterisation':
  print('\n'.join(result['hits']))
Path('probe', 'search-'+scope+'.json').write_text(json.dumps(records, indent=2)+'\n')
with Path('probe/REPORT.md').open('a') as out:
 out.write('\n### Counted '+scope+' searches\n\n')
 for record in records:
  result, positive = record['query'], record['positive_control']
  out.write('- '+record['name']+': `'+result['command']+'`; '+str(result['count'])+' matching lines, exit '+str(result['exit'])+'. Positive control: `'+positive['command']+'`; '+str(positive['count'])+' matching lines, exit '+str(positive['exit'])+'.\n')
