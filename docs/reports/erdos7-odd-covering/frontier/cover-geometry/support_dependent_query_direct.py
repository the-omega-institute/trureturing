#!/usr/bin/env python3
"""Direct finite-cylinder integration of a fixed64-query counterexample.

Construct the192 original boxes and64 comparison boxes independently.
Partition each prime space by the finite list of cylinder endpoints;
integrate the actual first11 PA kernel, with no geometric-tail formulas.
"""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
import json
from pathlib import Path
import hashlib

table = {(0,0):(0,4),(0,1):(2,6),(0,2):(8,8),(0,3):(1,1),
         (0,4):(3,3),(0,5):(5,5),(0,6):(7,7),(0,7):(9,9),
         (1,0):(1,5),(1,1):(3,7),(1,2):(9,9),(2,0):(8,8),
         (2,1):(9,9),(3,0):(2,2),(4,0):(3,3),(5,0):(6,6),
         (6,0):(7,7),(7,0):(9,9)}

def cylinder(p,e,r): return (p**e,r%(p**e))
def old(p,slot,e):
    if e==0: return (1,0)
    root=4 if p==5 else 5
    return cylinder(p,e,root if slot==0 or e==1 else root+p)
def new(p,kind,e):
    if e==0: return (1,0)
    root=(4 if p==5 else 5) if kind=='T' else (3 if p==5 else 6)
    return cylinder(p,e,root if kind=='D' or e==1 else root+2*p)

oldboxes=[]
unit=(1,0)
for p in (5,7):
    for e,j in product(range(1,5),(1,2)):
        c=cylinder(p,e,j*p**(e-1))
        oldboxes.append((c,unit,unit) if p==5 else (unit,c,unit))
for a,b,j in product(range(1,5),range(1,5),(3,4)):
    oldboxes.append((cylinder(5,a,3*5**(a-1)),cylinder(7,b,j*7**(b-1)),unit))
row11=[]
for (a,b),cs in table.items():
    for e,slot in product(range(1,5),(0,1)):
        r=11**(e-1)-1+cs[slot]*11**(e-1)
        box=(old(5,slot,a),old(7,slot,b),cylinder(11,e,r))
        oldboxes.append(box);row11.append(box)
queries=[]
for a,b,c in product(range(4),repeat=3):
    k5='T' if b==0 else 'D'
    k7='D' if a==0 or c==0 else 'T'
    queries.append((new(5,k5,a),new(7,k7,b),cylinder(11,c,9)))

def leaves(p,conditions):
    refine=set()
    for modulus,residue in conditions:
        q=1
        while q<modulus:
            refine.add((q,residue%q));q*=p
    answer=[]
    def descend(q,r):
        if (q,r) not in refine:
            answer.append((r,F(1,q)));return
        for j in range(p):descend(q*p,r+j*q)
    descend(1,0)
    if sum(m for _,m in answer)!=1:raise ValueError('partition mass')
    return answer

parts={p:leaves(p,[box[i] for box in oldboxes+queries]) for i,p in enumerate((5,7,11))}
def hit(r,c):return r%c[0]==c[1]
base=oldboxes[:48]
out=F(0);mass=F(0);bins=defaultdict(F);fibres=0;countchecks=0
for (x,mx),(y,my) in product(parts[5],parts[7]):
    if any(hit(x,b[0]) and hit(y,b[1]) for b in base):continue
    active=[b[2] for b in row11 if hit(x,b[0]) and hit(y,b[1])]
    survivors=[(z,mz) for z,mz in parts[11] if not any(hit(z,c) for c in active)]
    g=sum(mz for _,mz in survivors)
    h=min(F(5,3),1/g) if g else F(0)
    candidates=[b[2] for b in queries if hit(x,b[0]) and hit(y,b[1])]
    integral=sum(mz*max(0,sum(hit(z,c) for c in candidates)-2) for z,mz in survivors)
    out+=mx*my*h*integral;mass+=mx*my*h*g
    bins[str(g)]+=mx*my*h*integral;fibres+=1;countchecks+=len(survivors)
expected=F(289905891459395808502,1661652350530156359375)
h548=F(13869387400909870454063,79759312825447505250000)
if len(oldboxes)!=192 or len(queries)!=64:raise ValueError('inventory')
if len({tuple(c[0] for c in b) for b in queries})!=64:raise ValueError('labels')
if out!=expected or out<=h548:raise ValueError('hinge comparison')
result={'original_count':len(oldboxes),'query_count':len(queries),
        'partition_sizes':{p:len(v) for p,v in parts.items()},
        'old_survivor_fibres':fibres,'joint_survivor_cells':countchecks,
        'actual_lambda11_mass':str(mass),'direct_hinge':str(out),
        'strict_gap':str(out-h548),'bins':dict(bins),
        'scope':'Fixed comparison queries under the actual192-original lambda11; not actual13 row loss.'}
dest=Path(__file__).with_suffix('.json')
dest.write_text(json.dumps(result,indent=2,default=str)+'\n',encoding='utf-8')
print(json.dumps({'direct_hinge':str(out),'strict_gap':str(out-h548),
                  'json_sha256':hashlib.sha256(dest.read_bytes()).hexdigest()},indent=2))
