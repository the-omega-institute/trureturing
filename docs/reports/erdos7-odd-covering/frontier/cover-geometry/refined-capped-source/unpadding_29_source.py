"""Exact marked unpadding source, all-height moments, and restricted29 continuation.

The accompanying note proves the all-height and arbitrary-phase statements.
Finite controls are supplemental; inherited analytic tail premises are explicit.
Standard library only. No Lean claim and no program-byte identity gate.
"""
from fractions import Fraction as F
from math import comb, factorial, gcd, prod
from itertools import product
from pathlib import Path
import argparse
import json

P=(3,5,7,11,13,17,19,23)
LATE=P[3:]
MIXED=((15,2),(21,1),(35,1),(45,4),(63,29),(75,22),(105,29),(165,89))
SEPARATED=((15,2),(21,1),(35,16),(45,4),(63,38),(75,22),(105,74),(165,89))
CAPS={7:F(3,2),11:F(5,3),13:F(3,2),17:F(2),19:F(9,5),23:F(11,5)}
BOX=(8,9,5,3,3,3,3,3)


def need(ok,message):
    if not ok:
        raise ValueError(message)


def pure_phase(p,e):
    need(p in P and type(e)is int and e>=1,'Pure phase domain')
    return 0 if e==1 else (2 if p<=5 else 1)+p**(e-1)


def stirling(n,k):
    if n==0:return int(k==0)
    if k==0:return 0
    return k*stirling(n-1,k)+stirling(n-1,k-1)


def geom_moment(p,k):
    need(type(p)is int and p>1 and type(k)is int and 0<=k<=4,'Geometric moment domain')
    return sum((F(stirling(k,j)*factorial(j),(p-1)**j)for j in range(k+1)),F(0))


def shifted_moment(p,shift,k):
    need(type(shift)is int and shift>=0,'Nonnegative integer geometric shift')
    return sum((comb(k,j)*shift**(k-j)*geom_moment(p,j)for j in range(k+1)),F(0))


def A4(p):
    return shifted_moment(p,1,4)-1


def cap_moment(p,cap,k):
    need(0<=cap<=p,'Normalized run cap')
    return 1+cap*(shifted_moment(p,1,k)-1)


def prefix_sum(p,depth=None):
    need(p in P and (depth is None or type(depth)is int and depth>=0),'Complete prefix sum domain')
    if p in (3,5):
        fixed=1 if p==3 else 5
        if depth is not None and depth<=fixed:return F(depth+1)
        tail=F(0)if depth is None else F(1,p**(depth-fixed)*(p-1))
        return F(fixed+1)+F(1,p-1)-tail
    cap=F(7,5)if p==7 else F(p-1,p-2)
    return 1+cap/F(p-1)*(1-(F(0)if depth is None else F(1,p**depth)))


def tau(B,ell):
    need(type(B)is int and type(ell)is int and B>=286 and ell>=4 and 3**ell<=B and 4*ell>=25,
         'Analytic tail parameter domain')
    series=sum((F(factorial(25),factorial(25-j)*(3*ell)**j)for j in range(26)),F(0))
    return F(5625,6144)*F(2*ell*ell+1,2*ell*ell-1)**25*F(B,(B-1)**4)*series


def crt(pairs):
    modulus=prod(m for m,a in pairs)
    need(all(gcd(m,n)==1 for i,(m,a)in enumerate(pairs)for n,b in pairs[:i]),'Coprime CRT factors')
    residue=sum(a*(modulus//m)*pow(modulus//m,-1,m)for m,a in pairs)%modulus
    need(all(residue%m==a%m for m,a in pairs),'One fixed CRT phase')
    return modulus,residue


def finite_quartic_control(q,roots,cap):
    """Exhaust every complete3q phase layout on one nonuniform old source."""
    weights=(F(1,6),F(1,3),F(1,2));old_K=F(1)+15*max(weights)
    ds=(3,q,3*q);best=F(0);count=0
    mass=[weights[x%3]*cap/q if x%q in roots else F(0)for x in range(3*q)]
    for phases in product(*(range(d)for d in ds)):
        integral=sum((w*(1+sum(x%d==a for d,a in zip(ds,phases)))**4
                      for x,w in enumerate(mass)),F(0))
        best=max(best,integral);count+=1
    expected=old_K*(cap*F(len(roots),q)+cap*F(15,q))
    need(best==expected,'Every-phase finite quartic maximum equals root-product identity')
    return {'q':q,'live_roots':sorted(roots),'cap':cap,'complete_layouts':count,
            'maximum':best,'identity':expected}


def calculate():
    selected_pure=[(p**e,pure_phase(p,e))for p in P for e in range(1,4)]
    selected=dict(selected_pure+list(MIXED))
    need(len(selected)==32,'Distinct selected numerical labels')
    divisor_checks=0
    for dictionary in (MIXED,SEPARATED):
        phase=dict(selected_pure+list(dictionary))
        for m,a in dictionary:
            for d,b in phase.items():
                if d<m and m%d==0:
                    need(a%d!=b,'Selected proper-divisor disjointness');divisor_checks+=1
    pure_checks=0
    for p in P:
        for e in range(1,21):
            a=pure_phase(p,e)
            need(0<=a<p**e,'Normalized pure phase')
            for f in range(1,e):
                need(a%(p**f)!=pure_phase(p,f),'Finite pure-antichain control');pure_checks+=1
    mark_mod=3*5**5;u=F(1,mark_mod)
    for m,a in MIXED:
        if m%7==0:
            d=m//7;compatible=(a-1)%gcd(d,mark_mod)==0
            need(compatible==(m in (21,35)),'Exactly selected21 and35 are active on mark')
            if compatible:need(mark_mod%d==0 and a%7==1,'Active mark projection is complete and roots coincide')
        else:
            d=m//11 if m%11==0 else m
            need((a-1)%gcd(d,mark_mod)!=0,'Other selected classes miss the entire mark')
    need({a%7 for m,a in SEPARATED if m%7==0}=={1,2,3,4},'Collision-free control has no padded root')
    C=F(3,2);old_good=F(4,7);new_good=F(5,7);S=C*old_good;new_cap=1/new_good
    pure7=F(1,6);actual_bad=F(1,7)-F(1,42);artificial_bad=F(1,7)
    bad_density=(1-S)/(actual_bad+artificial_bad)
    need(S+bad_density*(actual_bad+artificial_bad)==1 and bad_density<=C,'Actual normalized padded kernel')
    need(bad_density==F(6,11)and bad_density*actual_bad==F(5,77)and bad_density*artificial_bad==F(6,77),
         'Actual and artificial old current losses')
    need(pure7+actual_bad+artificial_bad+old_good==1,'Actual all-height7 partition')
    need(new_cap==F(7,5)<C and new_cap*new_good==1,'New zero-loss cap-feasible physical kernel')
    for p in LATE:need(F(p-1,p-2)<=CAPS[p],'Later pure kernels obey existing caps')
    B4=u*shifted_moment(3,2,4)*shifted_moment(5,6,4)*prod(cap_moment(p,F(p-1,p-2),4)for p in LATE)
    old_mass=u*S;new_mass=u
    old_mean=F(5,2)*F(25,4)*cap_moment(7,C/S,1)*prod(F(p-1,p-2)for p in LATE)
    new_mean=F(5,2)*F(25,4)*cap_moment(7,new_cap,1)*prod(F(p-1,p-2)for p in LATE)
    old_K=B4*(S+C*A4(7));new_K=B4*(1+new_cap*A4(7))
    physical_old=B4*(1+C*A4(7));physical_new=new_K
    need(B4==F(2702942472674130023417,2332104825600000000),'Complete non7 fourth moment')
    need(old_mass==F(2,21875)and new_mass==F(1,9375),'Actual marked masses')
    need(old_mean==F(31000,1071)>28>new_mean==F(29600,1071),'Actual normalized full-query mean crosses28')
    need(old_K-new_K==B4*F(521,1890)>0 and physical_old-physical_new==B4*F(113,270)>0,
         'Both actual killed and physical raw fourth maxima decrease')
    need((C-new_cap)*F(15,7)-(1-S)==F(1,14)>0,'Strict unpadding improvement at every positive finite7 height')
    W=new_mass*new_mean;C29=F(7,4);mass29=(28*new_mass-W)/16
    need(C29*F(27,28)>=1 and C29<=29,'Actual29 capped-current kernel feasibility')
    K29=new_K*(1+C29*A4(29));bound29=F(16329)
    need(mass29==F(97,40162500)>0 and K29<bound29,'Arbitrary29 extension mass and complete fourth bound')
    growth=(F(1),F(25),F(250,3),F(100),F(40))
    need(all(growth[j]<=comb(25,j)for j in range(5)),'Coefficientwise complete quartic tail growth')
    allowance=tau(6561,8);tail_loss=bound29*allowance;tail_margin=mass29-tail_loss
    need(tail_margin>F(1,600000),'Full prime tail beyond6561 leaves positive actual distorted mass')
    fullsum=prod(prefix_sum(p)for p in P)
    boxsum=prod(prefix_sum(p,a)for p,a in zip(P,BOX))
    need(fullsum==new_mean,'All-divisor first moment equals exact product of prefix maxima')
    outside=new_mass*(fullsum-boxsum)
    need(0<outside<mass29/2,'All unused old labels outside the finite box cost less than half29 reserve')
    expanded_mass29=mass29-outside;expanded_tail=expanded_mass29-tail_loss
    need(mass29/2-tail_loss>F(1,2000000)and expanded_tail>F(1,2000000),
         'Extra outside-box old labels and unrestricted large tail have a certified common margin')
    hit_mod,hit_phase=crt([(3**10,1),(7,2),(11,2)])
    hit_mass=new_mass*F(1,3**9)*F(1,5)*F(10,99)
    need(hit_mod not in selected and hit_mod//(7*11)==3**10,'Extra original is outside the declared box')
    need(0<hit_mass<outside,'Specified actual extra class crosses mark with positive source mass')
    controls=[finite_quartic_control(5,{1,2},F(3,2)),finite_quartic_control(5,{1,2,3,4},F(5,4)),
              finite_quartic_control(7,{3,4,5,6},F(3,2)),finite_quartic_control(7,{2,3,4,5,6},F(7,5))]
    max_exponent_checks=0
    for q in (3,5,7,29):
        for h in range(1,7):
            direct=sum((F(1,q**max(es))for es in product(range(h+1),repeat=4)if max(es)>0),F(0))
            grouped=sum((F((j+1)**4-j**4,q**j)for j in range(1,h+1)),F(0))
            need(direct==grouped,'Complete exponent quadruple multiplicities');max_exponent_checks+=1
    invalid=0
    for operation in (lambda:pure_phase(7,0),lambda:cap_moment(7,F(8),4),lambda:prefix_sum(5,-1),
                      lambda:geom_moment(1,4),lambda:tau(6560,8),lambda:tau(6561,3)):
        try:operation()
        except ValueError:invalid+=1
        else:raise ValueError('Invalid domain control was accepted')
    return {'scope':'One fixed product mark with its specified pure completion and selected original dictionary; '
                    'arbitrary29-ending phases; optional distinct old labels outside the certified exponent box; '
                    'finite arbitrary prime tail above6561. Not arbitrary old8-prime families.',
            'selected_mixed_originals':MIXED,'collision_free_mixed_control':SEPARATED,
            'selected_pure_first_three':selected_pure,'pure_completion_formula':'a_p1=0; a_pe=b_p+p^(e-1), e>=2; b_3=b_5=2, b_p=1 otherwise',
            'mark':{'mod3':1,'mod3125':1,'haar_mass':u},'published_caps':CAPS,
            'old_live7_roots':(3,4,5,6),'new_live7_roots':(2,3,4,5,6),
            'old_physical7_cap':C,'old_normalized_killed7_cap':C/S,'new_physical7_cap':new_cap,
            'old_bad7_density':bad_density,'old_actual7_loss':bad_density*actual_bad,
            'old_artificial7_loss':bad_density*artificial_bad,
            'eta_complete_fourth':B4,'old_mass':old_mass,'new_mass':new_mass,'mass_gain':new_mass-old_mass,
            'old_normalized_mean':old_mean,'new_normalized_mean':new_mean,
            'old_raw_mean':old_mass*old_mean,'new_raw_mean':W,
            'old_raw_killed_fourth':old_K,'new_raw_killed_fourth':new_K,'raw_killed_fourth_gain':old_K-new_K,
            'old_raw_physical_fourth':physical_old,'new_raw_physical_fourth':physical_new,
            'raw_physical_fourth_gain':physical_old-physical_new,'finite_height_gap_factor_lower':F(1,14),
            'cap29':C29,'mass29_lower':mass29,'complete_fourth29_bound':K29,'fourth29_ceiling':bound29,
            'tail_cutoff':6561,'tail_ell':8,'tail_allowance':allowance,'tail_loss_upper':tail_loss,'tail_margin_lower':tail_margin,
            'extra_old_box':dict(zip(P,BOX)),'outside_box_query_upper':outside,'expanded_mass29_lower':expanded_mass29,
            'expanded_tail_margin_lower':expanded_tail,
            'actual_extra_crossing_original':{'modulus':hit_mod,'phase':hit_phase,'source_mass':hit_mass},
            'finite_controls':controls,'proper_divisor_checks':divisor_checks,'pure_pair_sample_checks':pure_checks,
            'exponent_quadruple_controls':max_exponent_checks,'invalid_domain_controls_rejected':invalid,
            'inherited_analytic_premise':'Report734 HM14--HM15 / Rosser--Schoenfeld Theorem8; not independently reproved here.',
            'lean_verification':False}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-result',type=Path);args=parser.parse_args()
    result=json.loads(json.dumps(calculate(),default=str))
    if args.write_result:args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:need(result==json.loads(Path(__file__).with_suffix('.json').read_text()),'Fresh data equals retained exact result')
    print(json.dumps({k:result[k]for k in ('old_mass','new_mass','old_normalized_mean','new_normalized_mean',
                     'mass29_lower','outside_box_query_upper','expanded_tail_margin_lower','lean_verification')},indent=2))


if __name__=='__main__':main()
