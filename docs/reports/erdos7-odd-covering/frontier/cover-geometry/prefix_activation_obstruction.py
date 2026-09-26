#!/usr/bin/env python3
"""Exact actual-phase obstruction to first-root budgets, with a prefix repair.

Reads established fixtures/costs; imports no producer. No Lean verification.
"""
from pathlib import Path
from fractions import Fraction as F
from math import prod
from collections import Counter
import hashlib
import json
import argparse

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
basepath=args.source_dir/'central_cell_root_certificate.json'
gatepath=args.source_dir/'remaining33_global_root_exclusion_certificate.json'
base=json.loads(basepath.read_text())
parent=json.loads(gatepath.read_text())
rows=base['originals']
changes={35:15,175:50,245:50,147:51}
for row in rows:
    if row['modulus'] in changes:
        row['residue']=changes[row['modulus']]
        for comp in row['components']:
            comp['residue']=row['residue'] % comp['prime']**comp['exponent']
rows += [dict(kind='pure',modulus=9,residue=1,components=[dict(prime=3,exponent=2,residue=1)]),
         dict(kind='pure',modulus=25,residue=6,components=[dict(prime=5,exponent=2,residue=6)])]
by_modulus={r['modulus']:r for r in rows}
Q=(7,11,13,17,19)
checks=Counter()
def ck(name,value):
    if not value:raise ArithmeticError(name)
    checks[name]+=1
def central(l,m):return 3*(l%3)+l//3,5*(m%5)+m//5
def active(row,l,m):
    a,b=central(l,m)
    coords={3:a,5:b}
    return all(coords[c['prime']] % c['prime']**c['exponent']==c['residue']
               for c in row['components'] if c['prime'] in coords)
ck('108_unique_originals',len(rows)==len(by_modulus)==108)
ck('95_anchor_inventory',sum(r['kind'] in ('star','pair') for r in rows)==95)
for row in rows:
    ck('actual_global_CRT',0<=row['residue']<row['modulus'] and
       prod(c['prime']**c['exponent'] for c in row['components'])==row['modulus'] and all(
           row['residue']%c['prime']**c['exponent']==c['residue'] for c in row['components']))
ck('forced_originals',by_modulus[21]['residue']==15 and by_modulus[147]['residue']==51)
for l in range(3):
    ck('positive_actual_conflict_cell',l!=3 and 5!=6 and active(by_modulus[21],l,5) and active(by_modulus[147],l,5))
    for t in range(1,7):
        ck('one_root_cannot_absorb_at_each_firstroot_leaf',not(t==15%7 and t==51%7))
positive_masks=[]
for mask in range(64):
    a=sum(bool(mask>>l&1) for l in range(3))
    b=sum(bool(mask>>l&1) for l in range(3,6))
    positive=(a==0 or a==1 and b<=1 or a==2 and b==0)
    if positive:
        positive_masks.append(mask)
        ck('every643_positive_mask_misses_forced_leaf',any(not(mask>>l&1) for l in range(3)))
ck('all23_positive_masks_accounted',len(positive_masks)==23)
anchors=[r for r in rows if r['kind'] in ('star','pair')]
for l in range(6):
    for m in range(20):
        if l==3 or m==6 or l<3 and m<5:continue
        for row in anchors:
            if not active(row,l,m):continue
            covered=any(c['prime'] in Q and c['residue']%c['prime']==1 for c in row['components'])
            if row['modulus']==147:
                covered=(l<3 and row['residue']%49==2)
            ck('actual_firstroot_plus_prefix_source_absorbs_every_anchor',covered)
ck('square_prefix_strictly_cheaper_than_full_root',F(1,35)<F(1,6))
ck('repaired7_mass',F(5,6)-F(1,35)==F(169,210)>F(4,6))
g=F(parent['constants']['g']);alpha=F(parent['constants']['alpha'])
fees=list(map(F,parent['combined512_coefficients']))
uniform=[]
for budget in (1,2,3):
    Z=[F(q-2,q-1)-budget*F(1,q*(q-2)) for q in Q]
    h=[prod(Z[i] for i in range(5) if not(T>>i&1)) for T in range(32)]
    folded=[sum(fees[32*mode+T]*h[T] for T in range(32)) for mode in range(16)]
    gates=[g*h[0]*F(row['selectors'][0],675)-sum(folded[mode]*F(row['selectors'][mode],675)
             for mode in range(16)) for row in parent['anchor_release']['central_templates']]
    gamma=min(gates)
    tail=F(19740202146111572828188083,495176015714152109959649689600)
    network=alpha*(gamma-F(1411,100000)-F(1,65536)-tail)
    uniform.append(dict(prefix_budget=budget,gate=str(gamma),projected_full_network_bound=str(network)))
    ck('uniform_prefix_gate_positive',gamma>0)
    if budget==1:ck('one_prefix_repairs_full_network',network>F(1,3800))
    if budget==2:ck('two_prefix_full_network',network>F(1,163000))
    if budget==3:ck('three_prefix_does_not_pay_this_full_network_budget',network<0)
result=dict(status='PASS',checks=dict(checks),check_count=sum(checks.values()),
    scope='Actual108-original obstruction to641/643 positive root-table classes; prefix repair and uniform-prefix scalar reuse',
    base_fixture_sha256=hashlib.sha256(basepath.read_bytes()).hexdigest(),
    cost_source_sha256=hashlib.sha256(gatepath.read_bytes()).hexdigest(),
    replacements=changes,added_pure_originals=[{'modulus':9,'residue':1},{'modulus':25,'residue':6}],
    forced_ternary_leaves=[0,1,2],uniform_prefix_results=uniform,
    limitations="Reuses640's16 previously certified full16-mode maximum-response vectors for separable H_T=h_T M; does not rederive their11400-corner coverage or audit646's conditional-layout gate.",
    new_lean_verification=False)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
