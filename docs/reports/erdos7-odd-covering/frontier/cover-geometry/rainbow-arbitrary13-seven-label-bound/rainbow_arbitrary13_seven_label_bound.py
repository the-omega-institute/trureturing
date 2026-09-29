#!/usr/bin/env python3
"""Seven-label certificate under the actual finite rainbow11 kernel.

Constructs the192 fixed original boxes and integrates their actual union.
Exhausts every phase at5,7,11,25 and every phase at55,77,121. Uses exact
integers/Fractions and finite prefix partitions, never a full CRT period.
No project producer or data is imported. Infinite query heights are handled
by the ordinary cap-sum and stability proof accompanying this experiment.
"""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
import json
import hashlib
from pathlib import Path

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
E={5:7,7:7,11:4};period={p:p**E[p] for p in E}
ints={}
for p in E:
    ints[p]=[]
    for x,w in parts[p]:
        count=w*period[p]
        if count.denominator!=1:raise ValueError('prefix finer than original period')
        ints[p].append((x,count.numerator))
D=prod(period.values());base=oldboxes[:48]
fibres={};raw={};ks={}
for (x,mx),(y,my) in product(ints[5],ints[7]):
    if any(hit(x,b[0]) and hit(y,b[1]) for b in base):continue
    mask=0
    for (a,b),colors in table.items():
        for slot in (0,1):
            if hit(x,old(5,slot,a)) and hit(y,old(7,slot,b)):mask|=1<<colors[slot]
    if mask not in fibres:
        conditions=[cylinder(11,e,11**(e-1)-1+c*11**(e-1)) for c in range(10) if mask&(1<<c) for e in range(1,5)]
        counts=[0]*121
        for z,mz in ints[11]:
            if not any(hit(z,c) for c in conditions):counts[z%121]+=mz
        g=F(sum(counts),period[11]);h=min(F(5,3),1/g)
        if g!=1-F(1464*mask.bit_count(),14641):raise ValueError('actual union')
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
w5=F(313,625);w7=F(1601,2401)
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
F13=F(93139019,475398000);gap=D0+D1;upper=F13-gap
checks={'original_inventory':len(oldboxes)==192,
        'all_9625_four_phase_tuples':four_count==9625 and len(rows)==11 and all(x['phases'] for x in rows),
        'cap55':max55<=w7*F(1,33),
        'cap77':max77<=w5*F(5,231),
        'cap121':max121<=w5*w7*F(5,363),
        'mass':mass==F(121611906311383,565194987328125),
        'D0':D0==F(73501141702295834,6782254491959821875),
        'D1':D1==F(6054681566538784,1056358773382171875),
        'upper':upper==F(14304757879004833932649,79759312825447505250000)}
capsum=(w5+F(1,4))*(w7+F(1,6))*F(7,6)-w5*w7
T=F(257,51);c0=F(6168733163201163811,542935350932041267200)
kappa=gap/4;mu=(T-2)*kappa-c0
checks.update({
 'complete_cap_sum':capsum==F(85599701,216090000),
 'comparison_union':UPA==F(9914617,49520625),
 'F13_identity':capsum-UPA==F13,
 'strict_13_only_margin':gap-4*c0/(T-2)==F(2253406402672999193988368222017,1395034104734293274541298008000000)>0,
 'absolute_13_saving':kappa==F(13765896910613993281,3323304701060312718750),
 'strict_NC4_margin':mu==F(2253406402672999193988368222017,1836044886230940825847901894400000)>0,
 'maximum55':max55==F(38566276513,2175193453125),
 'maximum77':max77==F(62201840963,6752727515625),
 'maximum121':max121==F(40822590747784381,13732664053968234375),
})
# Transfer the same seven-label certificate to every finite N,E>=4.
# The mathematical domination proof is in the accompanying report.
coeff=(F(5,33)+F(5,363)-1+F(28,33),
       F(1,7)+F(5,231)-F(28,231),
       F(1,5)+F(1,25)+F(1,33)-F(28,165),F(28,1155))
checks['positive_bilinear_coefficients']=coeff==(F(5,363),F(10,231),F(83,825),F(4,165)) and min(coeff)>0
def Csum(x,y):return coeff[0]*x*y+coeff[1]*x+coeff[2]*y+coeff[3]
C4=Csum(w5,w7);Cmin=Csum(F(1,2),F(2,3));epsilon=F(2,3*11**4)
checks['seven_label_constant']=C4==constant+w7*F(1,33)+w5*F(5,231)+w5*w7*F(5,363)==F(4270892,36315125)
checks['limiting_constant']=Cmin==F(22402,190575)
for k in range(11):
    g4=1-F(k,10)*(1-F(1,11**4));g0=1-F(k,10)
    h4=min(F(5,3),1/g4);h0=min(F(5,3),1/g0) if g0 else F(5,3)
    checks['kernel_ratio_K'+str(k)]=h0/h4<=1+epsilon
Duniform=Cmin-(1+epsilon)*(C4-gap)
kappa_uniform=Duniform/4;mu_uniform=(T-2)*kappa_uniform-c0
checks['uniform_deficit']=Duniform==F(9142782319955731204,553858897304769931875)
checks['uniform_saving']=kappa_uniform==F(2285695579988932801,553858897304769931875)
checks['uniform_NC4_margin']=mu_uniform==F(722502603087750387206885808749,611987095715588039413526047488000)>0
if not all(checks.values()):raise ValueError(checks)
result={'scope':'Actual192-original finite source, canonical548 colors; arbitrary phases on four plus three distinct shallow numerical labels.',
        'original_count':len(oldboxes),'partition_sizes':{p:len(parts[p]) for p in parts},
        'color_masks':len(fibres),'actual_lambda11_mass':str(mass),
        'four_phase_count':four_count,'rows':rows,
        'max55':str(max55),'max77':str(max77),'max121':str(max121),
        'd55':str(d55),'d77':str(d77),'d121':str(d121),
        'D0':str(D0),'D1':str(D1),'D13':str(gap),'Hstar':str(upper),
        'cap_sum':str(capsum),'comparison_union':str(UPA),
        'absolute13_saving':str(kappa),'NC4_margin':str(mu),'final_query_upper':str(T-mu),
        'maximizing55_phases':[(a,c) for a,c in product(range(5),range(11)) if AC[a][c]==max55],
        'maximizing77_phases':[(b,c) for b,c in product(range(7),range(11)) if BC[b][c]==max77],
        'maximizing121_phases':[c for c in range(121) if m121[c]==max121],
        'uniform_prefix_extension':{'N_min':4,'E_min':4,'kernel_ratio_excess':str(epsilon),
          'constant_coefficients':[str(x) for x in coeff],
          'C4':str(C4),'Cmin':str(Cmin),'D_uniform':str(Duniform),
          'actual13_saving':str(kappa_uniform),'NC4_margin':str(mu_uniform),
          'final_query_upper':str(T-mu_uniform)},
        'checks':checks,'passed_count':len(checks),'Lean':'not run'}
dest=Path(__file__).with_suffix('.json')
dest.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed_count':len(checks),'four_phase_count':result['four_phase_count'],
                  'D13':str(gap),'uniform_hinge_upper':str(upper),'NC4_margin':str(mu),
                  'uniform_prefix_NC4_margin':str(mu_uniform),
                  'json_sha256':hashlib.sha256(dest.read_bytes()).hexdigest()},indent=2))
