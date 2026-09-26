#!/usr/bin/env python3
"""Exact q=7 counterexample to prefix contraction for merely capped rho."""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
import json
import argparse

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
args = parser.parse_args()

checks = 0

def check(condition):
    global checks
    checks += 1
    if not condition:
        raise ValueError('counterexample check failed')

q = 7
N = q**3
density = []
field = []
for n in range(N):
    root = n % q
    if root == 6:
        d = F(0)
    elif root:
        d = F(7,6)
    elif n == 0:
        d = F(7,5)
    elif n % 49 == 0:
        d = F(1,10)
    else:
        d = F(331,252)
    density.append(d)
    field.append(F(int(n % 49 == 0 and n != 0)))
    check(0 <= d <= F(7,5))
rho = [d/N for d in density]
check(sum(rho) == 1)
for r in range(7):
    check(sum(rho[n] for n in range(N) if n % q == r) == (F(0) if r==6 else F(1,6)))
prefix_mass = sum(rho[n] for n in range(N) if n % 49 == 0)
source_mass = sum(rho[n]*field[n] for n in range(N))
theta = source_mass/prefix_mass
check(prefix_mass == F(2,343))
check(source_mass == F(3,1715))
check(theta == F(3,10))
averaged = [theta if n % 49 == 0 else F(0) for n in range(N)]
for a in range(49):
    check(sum(rho[n]*field[n] for n in range(N) if n%49==a) == sum(rho[n]*averaged[n] for n in range(N) if n%49==a))
rows = []
max_original = F(0)
max_averaged = F(0)
for e in (1,2,3):
    modulus = q**e
    cap = F(1,6) if e==1 else F(7,5*modulus)
    for a in range(modulus):
        indices = [n for n in range(N) if n % modulus == a]
        mass = sum((rho[n] for n in indices),F(0))
        before = sum((rho[n]*field[n] for n in indices),F(0))/cap
        after = sum((rho[n]*averaged[n] for n in indices),F(0))/cap
        check(mass <= cap)
        max_original = max(max_original,before)
        max_averaged = max(max_averaged,after)
        rows.append({'height':e,'phase':a,'reference_mass':str(mass),'cap':str(cap),'original':str(before),'averaged':str(after)})
check(max_original == F(1,14))
check(max_averaged == F(3,10))
check(max_averaged > max_original)
# Below depth three the reference and both fields are Haar-constant on every
# depth-three atom. Both numerator and cap scale by7^{-(e-3)}, so the ratios
# equal the corresponding depth-three ratio exactly, at every greater height.
result = {'schema':'prefix-averaging-capped-reference-counterexample-v1','status':'PASS',
    'check_count':checks,'q':7,'reference':'root-balanced but nonuniform surviving-root Haar density',
    'source_mass':str(source_mass),'prefix_mass':str(prefix_mass),'average_on_prefix':str(theta),
    'all_height_original_supremum':str(max_original),'all_height_averaged_supremum':str(max_averaged),
    'deeper_height_justification':'Reference and both fields have constant Haar density on depth-three cylinders; numerator and cap scale identically below depth three.',
    'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'new_lean_verification':False,'queries':rows}
output = args.output
output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','check_count','all_height_original_supremum','all_height_averaged_supremum')}))
