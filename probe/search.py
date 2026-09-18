import subprocess, json
from pathlib import Path
searches = {
 'mathlib': [
  r"rg -n -i '\b(?:LinearRecurrence|companion|charpoly)\b' .lake/packages/mathlib/Mathlib/Algebra/LinearRecurrence.lean .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly",
  r"rg -n -i '\b(?:recurrence|companion|generating function)\b' .lake/packages/mathlib/Mathlib/RingTheory/PowerSeries",
  r"rg -n -i '\b(?:PowerSeries|generating|rational)\b' .lake/packages/mathlib/Mathlib/Algebra/LinearRecurrence.lean",
  r"rg -n -i '\b(?:generating function|rational generating|Perrier|Riordan|Jacobi.?Perron)\b' .lake/packages/mathlib/Mathlib -g '*.lean'",
 ],
 'repo': [
  r"git grep -n -i -P '\b(?:Perrier|Riordan|Jacobi.?Perron|multidimensional continued)\b' -- 'D5/**/*.lean' 'Blueprint/**' 'Problems/**' 'Library/**'",
  r"git grep -n -i -P '\b(?:LinearRecurrence|companion|generating_equation|generating_unique|rational_series)\b' -- 'D5/**/*.lean'",
 ],
 'positive_control': [r"git grep -n -P '\b(?:theorem|def)\b' -- 'D5/S3/Arith/RationalCompositionParityPeriodTen.lean'"]
}
result = {}
for category, commands in searches.items():
 result[category] = []
 for cmd in commands:
  p = subprocess.run(cmd, shell=True, text=True, capture_output=True)
  item = dict(cmd=cmd, hits=len(p.stdout.splitlines()), exit_code=p.returncode)
  result[category].append(item)
  print(json.dumps(item))
  with open('probe/search-matches.txt','a') as f:
   f.write(cmd+'\n'+p.stdout+p.stderr+'\n')
Path('probe/dedupe.json').write_text(json.dumps(result,indent=2)+'\n')
