#!/usr/bin/env python3
"""Exact consumer for a same-Q-marginal lift with bounded residual overlap.

The all-family conclusion is the ordinary proof in Report572.
No Lean result or optimality claim is made.
"""
from fractions import Fraction as F
from math import gcd, lcm, prod
from pathlib import Path
import json

checks=[]
def need(name, value):
    if not value:
        raise ValueError(name)
    checks.append(name)

def encode(x):
    if isinstance(x,F): return {"exact":str(x),"decimal":float(x)}
    if isinstance(x,dict): return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [encode(v) for v in x]
    return x

B=F(432040125182653876501,86355045355449035400)
alpha=F(7575003978548161,73724315753088000)
c0=F(25,27)
T=F(566,49)
upper=B+(1+B)/c0
gate=566-49*upper
old=(1+2*B)/c0
haar9=gate*c0*alpha/F(11088)
need('h3 M2 minimum fibre mass', c0==1-F(2,3**3))
need('new exact query upper', upper==F(6199418183523781383463,539719033471556471250))
need('new upper passes pure23/29 gate', upper<T)
need('new exact gate slack', gate==F(1709481952235674937813,539719033471556471250))
need('old uniform mass-loss bound fails at same worst-case reserve', old>T)
need('new nine-head Haar bound', haar9==F(1709481952235674937813,62903178645754948300800000))
need('nine-head Haar lower exceeds one over 37000',haar9>F(1,37000))
new_delta=1-(1+B)/(T-B)
old_delta=1-(1+2*B)/T
need('strictly wider compatible-fibre reserve than old scalar criterion', old_delta<F(2,27)<new_delta)

no_pure_upper=1+2*B
no_pure_gate=566-49*no_pure_upper
need('no pure3 h1 M3 exact reserve',1-F(3,2*3)==F(1,2))
need('no pure3 exact common query bound',no_pure_upper==F(475217647860378394201,43177522677724517700))
need('no pure3 exact positive gate',no_pure_gate==F(1152813090433535702351,43177522677724517700)>0)

# One globally fixed actual family: complete source pure3, two exceptional
# cofactors5,7, and an essential Q-only triple385.
originals=[{'m':3,'a':2,'d':1,'e':1,'qphase':0,'tphase':2}]
for d in (5,7):
    for e,qphase in ((0,0),(1,1),(4,2),(5,3)):
        p3=3**e
        tphase=0
        a=qphase if e==0 else (qphase+d*((-qphase*pow(d,-1,p3))%p3))%(p3*d)
        originals.append({'m':p3*d,'a':a,'d':d,'e':e,'qphase':qphase,'tphase':tphase})
originals.append({'m':385,'a':2,'d':385,'e':0,'qphase':2,'tphase':0})
need('ten actual numerical labels distinct',len(originals)==len({r['m'] for r in originals})==10)
need('all originals are odd nonunits',all(r['m']>1 and r['m']%2 for r in originals))
need('one fixed CRT phase per original',all(r['a']%r['d']==r['qphase'] and r['a']%(3**r['e'])==r['tphase'] for r in originals))
period=lcm(*(r['m'] for r in originals))
private={}
for r in originals:
    private[str(r['m'])]=next((x for x in range(r['a'],period,r['m']) if all(x%s['m']!=s['a'] for s in originals if s is not r)),None)
need('all ten originals have an actual private witness',all(v is not None for v in private.values()))
need('essential Q-only triple excludes star and all-three-rooted support classes',private['385'] is not None and 385%3!=0)
selected={5:{0,1},7:{0,1},385:{2}}
need('selected phases cover every nonunit-cofactor original through e3',all(r['e']>3 or r['d']==1 or r['qphase'] in selected[r['d']] for r in originals))
need('through-five finite-window condition fails at cofactor5',len({r['qphase'] for r in originals if r['d']==5 and r['e']<=5})==4 and 5<=500000)
need('through-five finite-window condition fails at cofactor7',len({r['qphase'] for r in originals if r['d']==7 and r['e']<=5})==4 and 7<=500000)
V=[x for x in range(385) if all(x%d not in A for d,A in selected.items())]
tail=[r for r in originals if r['d']>1 and r['e']>3 and r['qphase'] not in selected[r['d']]]
active={x:{r['d'] for r in tail if x%r['d']==r['qphase']} for x in V}
need('residual activation uses at most two actual cofactors at each Q point',max(map(len,active.values()))==2)
# Exact SD1 PA source for this selected family: the initial allowed5/7
# pairs are uniform; at11 only pair(2,2) excludes root2; later rows are Haar.
nu={x:(F(1,150) if x%5==2 and x%7==2 else F(1,165)) for x in V}
need('one explicit selected Q source normalizes',sum(nu.values())==1)
need('selected Q source avoids all selected classes',all(all(x%d not in A for d,A in selected.items()) for x in nu))
T3=[t for t in range(243) if t%3!=2]
fibres={x:[t for t in T3 if all(not (t%(3**r['e'])==r['tphase'] and x%r['d']==r['qphase']) for r in originals if r['d']>1)] for x in V}
c={x:F(len(ts),len(T3)) for x,ts in fibres.items()}
need('all actual Q fibres meet the claimed reserve',min(c.values())>=c0)
need('explicit example exact minimum fibre survival',min(c.values())==F(53,54))
Z=sum(nu[x]/c[x] for x in V)
w={x:nu[x]/c[x]/Z for x in V}
need('inverse raw prior is one probability',sum(w.values())==1)
need('inverse raw prior has the intended normalized Q marginal',all(w[x]*c[x]*Z==nu[x] for x in V))
need('inverse product deletion has positive raw survival',sum(w[x]*c[x] for x in V)==1/Z and 1/Z>=c0)

# Exact all-height query formula on first4 primes3,5,7,11; independent
# Haar on13,17,19 completes the SAME law. Only finite cell masses are
# enumerated. The gamma factors sum every unresolved height geometrically.
def complete_norm(cells,denom,height_pairs):
    ans=F(0)
    divisors=[(1,F(1))]
    for p,H in height_pairs:
        divisors=[(d*p**e,g*(F(p,p-1) if e==H else 1)) for d,g in divisors for e in range(H+1)]
    for d,g in divisors:
        if d==1: continue
        masses=[0]*d
        for x,v in cells: masses[x%d]+=v
        ans+=g*F(max(masses),denom)
    return ans
qden=lcm(*(v.denominator for v in nu.values()))
qcells=[(x,int(v*qden)) for x,v in nu.items()]
qbase=complete_norm(qcells,qden,((5,1),(7,1),(11,1)))
haar_tail=prod(F(p,p-1) for p in (13,17,19))
RQ=(1+qbase)*haar_tail-1
need('explicit selected source obeys the SD1 complete-query bound',RQ<=B)
jointden=lcm(*((nu[x]/len(fibres[x])).denominator for x in V))
joint=[]
for x in V:
    mass=int(jointden*nu[x]/len(fibres[x]))
    for t in fibres[x]:
        residue=(x+385*((t-x)*pow(385,-1,243)%243))%period
        joint.append((residue,mass))
need('one joint law normalized on actual survivor',sum(v for _,v in joint)==jointden and all(all(x%r['m']!=r['a'] for r in originals) for x,_ in joint))
qbaseP=complete_norm(joint,jointden,((3,5),(5,1),(7,1),(11,1)))
RP=(1+qbaseP)*haar_tail-1
need('exact example full query norm passes gate and general bound',RP<T and RP<=upper)
need('exact example obeys its stronger actual-fibre bound',RP<=RQ+F(3,4)*(1+RQ)/min(c.values()))

result={
 'kind':'ordinary-proof-consumer-and-exact-arithmetic',
 'B':B,'c0':c0,'new_R_upper':upper,'gate_slack':gate,'old_uniform_bound':old,
 'new_compatible_loss_limit':new_delta,'old_scalar_loss_limit':old_delta,
 'nine_head_Haar_lower':haar9,
 'no_pure3_h1_M3':{'query_upper':no_pure_upper,'gate':no_pure_gate},
 'example':{'originals':originals,'period':period,'private_witnesses':private,'selected_Q_cells':len(V),'joint_positive_cells':len(joint),'minimum_fibre_survival':min(c.values()),'inverse_normalizer':Z,'raw_surviving_mass':1/Z,'RQ':RQ,'RP':RP},
 'checks':checks,'check_count':len(checks),
 'scope':{'all_finite_original_heights':True,'all_query_heights':True,'globally_fixed_phases':True,'same_Q_source_and_joint_law':True,'unrestricted_P_families':False,'exact_optimality':False,'new_Lean_verification':False}
}
p=Path(__file__).with_suffix('.json')
p.write_text(json.dumps(encode(result),indent=2)+'\n')
print(json.dumps({'checks':len(checks),'RP_upper':str(upper),'example_RP':str(RP),'example_RP_decimal':float(RP),'result':str(p)}))
