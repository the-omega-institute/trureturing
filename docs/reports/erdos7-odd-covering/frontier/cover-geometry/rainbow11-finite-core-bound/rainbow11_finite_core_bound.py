#!/usr/bin/env python3
"""Exact seven-label certificate for a finite rectangular rainbow core.

Constructs the108 original boxes and integrates their actual first11
kernel. Enumerates all9625 joint shallow phases and253 individual phases.
The ordinary capped-kernel variation proof pays every arbitrary first11 original
outside the finite core using one convergent full-label tail. Standard library
only; no previous producer or retained result is imported.
"""
from fractions import Fraction as F
from itertools import product
import json
import hashlib
from pathlib import Path

table = {(0,0):(0,4),(0,1):(2,6),(0,2):(8,8),(0,3):(1,1),
         (0,4):(3,3),
         (1,0):(1,5),(1,1):(3,7),(1,2):(9,9),(2,0):(8,8),
         (2,1):(9,9),(3,0):(2,2),(4,0):(3,3),(5,0):(6,6)}

def cylinder(p,e,r): return (p**e,r%(p**e))
def old(p,slot,e):
    if e==0: return (1,0)
    root=4 if p==5 else 5
    return cylinder(p,e,root if slot==0 or e==1 else root+p)
oldboxes=[]
unit=(1,0)
for p in (5,7):
    for e,j in product(range(1,4),(1,2)):
        c=cylinder(p,e,j*p**(e-1))
        oldboxes.append((c,unit,unit) if p==5 else (unit,c,unit))
for a,b,j in product(range(1,4),range(1,4),(3,4)):
    oldboxes.append((cylinder(5,a,3*5**(a-1)),cylinder(7,b,j*7**(b-1)),unit))
row11=[]
for (a,b),cs in table.items():
    for e,slot in product(range(1,4),(0,1)):
        r=11**(e-1)-1+cs[slot]*11**(e-1)
        box=(old(5,slot,a),old(7,slot,b),cylinder(11,e,r))
        oldboxes.append(box);row11.append(box)
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


from math import prod
conds=[[box[i] for box in oldboxes] for i in range(3)]
for i,q in enumerate((25,7,121)):conds[i]+=[(q,r) for r in range(q)]
parts={p:leaves(p,conds[i]) for i,p in enumerate((5,7,11))}
def hit(r,c):return r%c[0]==c[1]
period={p:max(c[0] for c in conds[i]) for i,p in enumerate((5,7,11))}
ints={}
for p in period:
    ints[p]=[]
    for x,w in parts[p]:
        count=w*period[p]
        if count.denominator!=1:raise ValueError('prefix finer than original period')
        ints[p].append((x,count.numerator))
D=prod(period.values());base=oldboxes[:30]
fibres={};raw={};ks={}
for (x,mx),(y,my) in product(ints[5],ints[7]):
    if any(hit(x,b[0]) and hit(y,b[1]) for b in base):continue
    mask=0
    for (a,b),colors in table.items():
        for slot in (0,1):
            if hit(x,old(5,slot,a)) and hit(y,old(7,slot,b)):mask|=1<<colors[slot]
    if mask not in fibres:
        conditions=[cylinder(11,e,11**(e-1)-1+c*11**(e-1)) for c in range(10) if mask&(1<<c) for e in range(1,4)]
        counts=[0]*121
        for z,mz in ints[11]:
            if not any(hit(z,c) for c in conditions):counts[z%121]+=mz
        g=F(sum(counts),period[11]);h=min(F(5,3),1/g)
        if g!=1-F(133*mask.bit_count(),1331):raise ValueError('actual union')
        fibres[mask]=[(z,n) for z,n in enumerate(counts) if n]
        ks[mask.bit_count()]=h
    k=mask.bit_count()
    if k not in raw:raw[k]=[0]*(25*7*121)
    offset=((x%25)*7+y%7)*121;w=mx*my
    for z,n in fibres[mask]:raw[k][offset+z]+=w*n
coarse=[F(0)]*(25*7*11);m121=[F(0)]*121
for k,data in raw.items():
    factor=ks[k]/D
    for index,n in enumerate(data):
        if n:
            oldindex,z=divmod(index,121);v=n*factor
            coarse[oldindex*11+z%11]+=v;m121[z]+=v
mass=sum(coarse)
DB=[[F(0)]*7 for _ in range(25)];DC=[[F(0)]*11 for _ in range(25)]
ABC=[[[F(0)]*11 for _ in range(7)] for _ in range(5)]
for d,b,c in product(range(25),range(7),range(11)):
    v=coarse[(d*7+b)*11+c];DB[d][b]+=v;DC[d][c]+=v;ABC[d%5][b][c]+=v
AB=[[sum(ABC[a][b]) for b in range(7)] for a in range(5)]
AC=[[sum(ABC[a][b][c] for b in range(7)) for c in range(11)] for a in range(5)]
BC=[[sum(ABC[a][b][c] for a in range(5)) for c in range(11)] for b in range(7)]
mD=[sum(x) for x in DB]
w5=F(63,125);w7=F(229,343)
UPA=w5*w7-(w5-F(1,5))*(w7-F(1,7))*F(28,33)
P5=w7/5;P7=w5/7;P11=w5*w7*F(5,33);P25=w7/25
constant=P5+P7+P11+P25-UPA
rows=[];four_count=0
for c in range(11):
    best=None;arg=[]
    for a,b,d in product(range(5),range(7),range(25)):
        four_count+=1
        over=AB[a][b]+AC[a][c]+BC[b][c]-ABC[a][b][c]
        if d%5==a:over+=mD[d]
        else:over+=DB[d][b]+DC[d][c]-coarse[(d*7+b)*11+c]
        delta=constant-over
        if best is None or delta<best:best=delta;arg=[(a,b,d)]
        elif delta==best:arg.append((a,b,d))
    rows.append({'r11':c,'minimum':str(best),'phases':arg})
D0=min(F(x['minimum']) for x in rows)
max55=max(v for row in AC for v in row);max77=max(v for row in BC for v in row);max121=max(m121)
d55=w7*F(1,33)-max55;d77=w5*F(5,231)-max77;d121=w5*w7*F(5,363)-max121
D1=d55+d77+d121
F13=(w5+F(1,4))*(w7+F(1,6))*F(7,6)-w5*w7-UPA;gap=D0+D1;upper=F13-gap
checks={}
def check(name,value):
    if name in checks:raise ValueError('duplicate check '+name)
    checks[name]=bool(value)
    if not value:raise ValueError('failed '+name)
check('original_inventory',len(oldboxes)==108 and len(row11)==78 and len(table)==13)
check('all_four_phases',four_count==9625)
check('all_individual_phases',len(AC)*len(AC[0])+len(BC)*len(BC[0])+len(m121)==253)
check('actual_anchor_mass',mass==F(37407967,171199875))
check('D0',D0==F(526471991278,48559988544375))
check('D1',D1==F(3627674504,630649201875))
check('anchor_deficit',gap==F(805802928086,48559988544375))
check('maximum55',max55==F(267593,15073135))
check('maximum77',max77==F(25285599,2730083125))
check('maximum121',max121==F(13280282789,4414544413125))
check('all_three_caps',min(d55,d77,d121)>=0)
check('complete_cap_sum',F13==((w5+F(1,4))*(w7+F(1,6))*F(7,6)-w5*w7)-UPA)
# The seven-label nonnegative payoff is bounded by6. The ordinary
# variation lemma multiplies this by the actual density cap5/3.
Cref=F(5,363)*w5*w7+F(10,231)*w5+F(83,825)*w7+F(4,165)
Cmin=F(5,363)*F(1,2)*F(2,3)+F(10,231)*F(1,2)+F(83,825)*F(2,3)+F(4,165)
check('seven_label_constant',Cref==constant+w7/F(33)+w5*F(5,231)+w5*w7*F(5,363))
check('limiting_constant',Cmin==F(22402,190575))
Duniform=gap+Cmin-Cref
oldcap=(w5+F(1,4))*(w7+F(1,6))
high5=F(1,4*5**5);high7=F(1,6*7**4)
high_old=high5*(w7+F(1,6))+(w5+F(1,4))*high7-high5*high7
J=2*(oldcap/F(10*11**3)+high_old*(1-F(1,11**3))/10)
# Independent finite-box complement identity for the complete cap sum.
box5=w5+sum(F(1,5**a) for a in range(1,6))
box7=w7+sum(F(1,7**b) for b in range(1,5))
box11=sum(F(1,11**e) for e in range(1,4))
check('outside_box_cap_sum',J==2*(oldcap/F(10)-box5*box7*box11))
Dtail=Duniform-10*J
T=F(257,51);c0=F(6168733163201163811,542935350932041267200)
kappa=Dtail/4;mu=(T-2)*kappa-c0
check('pure_rectangle_deficit',Duniform==F(338800827094,20811423661875))
check('complete_old_cap',oldcap==F(647309,1029000))
check('all_outside_box_original_charge',J==F(4051379,34239975000))
check('tail_stable_deficit',Dtail==F(8796931120759,582719862532500))
check('positive_raw_margin',Dtail-4*c0/(T-2)==F(75634593128793577758661,529988671579135933644480000)>0)
check('positive_NC4_margin',mu==F(75634593128793577758661,697533477433185357828864000)>0)
# Exact finite stress cases for the variation inequality; these do not
# replace its general two-case proof in the report.
c=F(5,3);variation_cases=0
for ni,nx,ny in product(range(13),repeat=3):
    if ni+nx+ny>12:continue
    overlap,x,y=F(ni,12),F(nx,12),F(ny,12)
    a,b=overlap+x,overlap+y
    ha=min(c,1/a) if a else c;hb=min(c,1/b) if b else c
    pos=hb*y+max(F(0),hb-ha)*overlap
    if pos>c*max(x,y):raise ValueError('general variation')
    if y==0 and pos>c*x:raise ValueError('nested variation')
    variation_cases+=1
check('variation_stress_cases',variation_cases==455)
result={
 'scope':'The30 prescribed old originals at 0<=a,b<=3,a+b>0; first11 labels inside 0<=a<6,0<=b<5,1<=e<=3 exactly the78 prescribed originals with empty remaining cells; all labels outside these two finite windows and all13/17/19 labels arbitrary finite Q-smooth two-copy and globally fixed phases.',
 'anchor_original_count':len(oldboxes),'partition_sizes':{p:len(parts[p]) for p in parts},
 'color_masks':len(fibres),'actual_anchor_mass':str(mass),
 'four_phase_count':four_count,'individual_phase_count':253,'rows':rows,
 'max55':str(max55),'max77':str(max77),'max121':str(max121),
 'maximizing55_phases':[(a,c) for a,c in product(range(5),range(11)) if AC[a][c]==max55],
 'maximizing77_phases':[(b,c) for b,c in product(range(7),range(11)) if BC[b][c]==max77],
 'maximizing121_phases':[c for c in range(121) if m121[c]==max121],
 'D0':str(D0),'D1':str(D1),'anchor_deficit':str(gap),
 'anchor_hinge_upper':str(upper),'Cref':str(Cref),'Cmin':str(Cmin),
 'pure_rectangle_deficit':str(Duniform),'complete_old_cap_sum':str(oldcap),
 'arbitrary_outside_box_charge':str(J),'tail_stable_deficit':str(Dtail),
 'actual13_saving':str(kappa),'NC4_margin':str(mu),'final_query_upper':str(T-mu),
 'variation_stress_cases':variation_cases,'checks':checks,'passed_count':len(checks),'Lean':'not run'}
dest=Path(__file__).with_suffix('.json')
dest.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed_count':len(checks),'anchor_mass':str(mass),'D0':str(D0),'D1':str(D1),
 'tail_stable_deficit':str(Dtail),'NC4_margin':str(mu),'final_query_upper_decimal':float(T-mu),
 'json_sha256':hashlib.sha256(dest.read_bytes()).hexdigest()},indent=2))
