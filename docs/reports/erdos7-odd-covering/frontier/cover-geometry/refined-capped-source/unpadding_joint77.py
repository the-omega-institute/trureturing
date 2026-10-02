"""One actual7/11 interaction after unpadding, with complete query moments.

All-height claims are proved in the companion note. The finite controls
check real prefix marginals including the unresolved infinite pure tail.
"""
from fractions import Fraction as F
from math import comb,factorial,prod
from pathlib import Path
from collections import defaultdict
import argparse,json


def need(ok,why):
    if not ok:raise ValueError(why)


def geom(p,k):
    t=F(1,p-1)
    return (F(1),t,t+2*t*t,t+6*t*t+6*t**3,t+14*t*t+36*t**3+24*t**4)[k]


def shifted(p,a,k):
    return sum((comb(k,j)*a**(k-j)*geom(p,j)for j in range(k+1)),F(0))


def Ak(p,k):return shifted(p,1,k)-1


def pure11_good(depth,phase):
    need(type(depth)is int and depth>=0 and 0<=phase<11**depth,'Actual11 prefix domain')
    if depth==0:return F(9,10)
    if phase%11==0:return F(0)
    for e in range(2,depth+1):
        if phase%(11**e)==1+11**(e-1):return F(0)
    return F(1,11**depth)-(F(1,10*11**depth)if phase==1 else F(0))


def allowance(B=6561,ell=8,delta=F(2,5),growth=25):
    need(B>=286 and ell>=4 and 3**ell<=B and 4*ell>=growth and 0<delta<1,'Inherited analytic tail domain')
    coefficients=(F(1),F(15)/(1-delta),F(50)/(1-delta),F(60)/(1-delta),F(24)/(1-delta))
    need(all(coefficients[j]<=comb(growth,j)for j in range(5)),'Complete fourth-moment growth envelope')
    loss_constant=F(27,256)/(delta**3*(1-delta))
    return loss_constant/3*F(2*ell*ell+1,2*ell*ell-1)**growth*F(B,(B-1)**4)*sum(
        (F(factorial(growth),factorial(growth-j)*(3*ell)**j)for j in range(growth+1)),F(0))


def table_profile(h,forbidden,B,ell,delta,growth):
    need(type(h)is int and h>=1 and set(forbidden)==set(range(2,7)),'Actual marked table domain')
    good={};density={}
    for r,roots in forbidden.items():
        need(roots<=set(range(1,11)),'Forbidden11 roots lie outside the pure0 root')
        good[r]=F(9,10)-sum((pure11_good(1,z)for z in roots),F(0))
        need(good[r]>=F(3,5),'Every actual11 row permits zero loss below its published cap')
        density[r]=1/good[r]
    clean=set(range(2,11))-set().union(*forbidden.values())
    need(bool(clean),'One whole11 root must attain every marginal and joint cap')
    alpha=F(7,5);beta=sum(density.values())/5;kappa=alpha*max(density.values())
    m=F(1,3*5**h)
    values={k:shifted(3,2,k)*shifted(5,h+1,k)*(1+alpha*Ak(7,k)+beta*Ak(11,k)+kappa*Ak(7,k)*Ak(11,k))*
            prod(1+F(p-1,p-2)*Ak(p,k)for p in(13,17,19,23))for k in(1,4)}
    mean=values[1];mass29=m*(28-mean)/28;K29=m*values[4]*(1+Ak(29,4));tail=K29*allowance(B,ell,delta,growth)
    return {'height5':h,'forbidden_root_table':{r:sorted(roots)for r,roots in forbidden.items()},
            'actual11_good_masses':good,'actual11_densities':density,'common_clean11_root':min(clean),
            'alpha7':alpha,'beta11':beta,'kappa_joint':kappa,'mass8':m,'mean8':mean,
            'mass29_lower':mass29,'fourth29_bound':K29,'tail_cutoff':B,'tail_ell':ell,
            'tail_delta':delta,'tail_growth':growth,'tail_remaining_lower':mass29-tail}


def calculate():
    m=F(1,9375);C7=F(7,5);Dlo=F(10,9);Dhi=F(110,89);Dbar=(Dhi+4*Dlo)/5
    need(Dhi<=F(5,3)and Dhi*(F(9,10)-F(1,11))==1,'New actual11 kernel is normalized and cap-feasible')
    need(Dlo*F(9,10)==1,'Other actual11 kernels remain normalized')
    # Actual joint7^2 by11^2 marginal; pure11 tails above depth2
    # are retained analytically by pure11_good, not silently omitted.
    tables={(a,b):defaultdict(F)for a in range(3)for b in range(3)}
    point_count=0
    for z7 in range(49):
        if z7%7 not in (2,3,4,5,6):continue
        density=Dhi if z7%7==2 else Dlo
        for z11 in range(121):
            w=C7/F(49)*density*pure11_good(2,z11)
            if z7%7==2 and z11%11==2:w=F(0)
            for a,b in tables:tables[a,b][(z7%(7**a),z11%(11**b))]+=w
            point_count+=1
    need(tables[0,0][0,0]==1,'Actual joint source remains normalized')
    caps=[]
    for (a,b),table in tables.items():
        expected=F(1)if a==b==0 else C7/F(7**a)if b==0 else Dbar/F(11**b)if a==0 else C7*Dhi/F(7**a*11**b)
        need(max(table.values())==expected,'Actual prefix maximum equals the claimed joint cap')
        need(table[2%(7**a),3%(11**b)]==expected,'One nested centre attains all intersection caps')
        caps.append({'depth7':a,'depth11':b,'maximum':expected})
    need(tables[1,1][2,2]==0,'Actual2 mod77 is avoided')
    joint=tables[1,1][2,3];product_marginals=tables[1,0][2,0]*tables[0,1][0,3]
    need(joint==F(2,89)and product_marginals==F(182,8811)and joint-product_marginals==F(16,8811),
         'Updated marginal product misses an actual positive joint query mass')
    joint_moment={k:1+C7*Ak(7,k)+Dbar*Ak(11,k)+C7*Dhi*Ak(7,k)*Ak(11,k)for k in (1,4)}
    moment={k:shifted(3,2,k)*shifted(5,6,k)*joint_moment[k]*prod(
        1+F(p-1,p-2)*Ak(p,k)for p in (13,17,19,23))for k in (1,4)}
    mean=moment[1];K8=m*moment[4];mass29=m*(28-mean)/28;K29=K8*(1+Ak(29,4))
    need(mean==F(881600,31773)<28 and mass29==F(2011,2085103125)>0,'Actual correlated source passes full first-moment29 criterion')
    tail=K29*allowance();margin=mass29-tail
    need(margin>F(1,2500000),'Same-source arbitrary tail above6561 remains positive')
    simple_global_cap_mean=F(29600,1071)*Dhi/Dlo
    need(simple_global_cap_mean>28,'Replacing11 by one global maximum cap loses this mean certificate')
    before_joint_class_mass=m*F(1,5)*F(10,99)
    old_deletion_tail=F(97,40162500)-before_joint_class_mass-F(16329)*allowance()
    need(old_deletion_tail<0,'Deleting this low class and retaining785 bounds does not certify tail6561')
    # Independent complete finite-label enumeration on a finite two-axis
    # version of the same asymmetric conditional-root geometry.
    toy={}
    for u in (1,2):
        roots=(2,3,4)if u==1 else(1,2,3,4)
        for v in roots:toy[next(x for x in range(15)if x%3==u and x%5==v)]=F(1,2*len(roots))
    best=F(0);layouts=0
    for a in range(3):
        for b in range(5):
            for c in range(15):
                integral=sum((w*(1+(x%3==a)+(x%5==b)+(x%15==c))**4 for x,w in toy.items()),F(0))
                best=max(best,integral);layouts+=1
    toy_expected=1+15*F(1,2)+15*(F(1,6)+F(1,8))+225*F(1,6)
    need(best==toy_expected,'Arbitrary finite numerical phases attain the correlated joint tuple cap')
    table_rows=[]
    for hit_rows in range(1,6):
        forbidden={r:({2}if r<2+hit_rows else set())for r in range(2,7)}
        for h in range(1,6):
            row=table_profile(h,forbidden,729,6,F(1,4),20)if h==1 else table_profile(h,forbidden,6561,8,F(2,5),25)
            if h==1:need(row['tail_remaining_lower']>F(1,64),'Uniform shallow five-row table continuation')
            elif hit_rows<=3:need(row['tail_remaining_lower']>0,'Deep one-to-three-row table continuation')
            if h==5 and hit_rows>=4:need(row['tail_remaining_lower']<0,'Deep four/five-row boundary for this tail estimate')
            row['affected7_rows']=hit_rows;table_rows.append(row)
    triple=((77,2),(231,178),(385,46))
    for (d,a),root in zip(triple,(2,3,4)):
        need(a%7==root and a%11==2 and(a-1)%gcd_anchor(d)==0,'Literal independent labels realize three affected7 rows')
    need(table_rows[0]['mean8']==F(105792,10591)and table_rows[10]['mean8']==F(15168,1513),
         'Shallow single-row and three-row means')
    five_originals=triple+((539,68),(847,244))
    for r,(d,a)in zip(range(2,7),five_originals):
        need(d%77==0 and a%7==r and a%11==2 and 0<=a<d,'Literal five-row full numerical original phases')
    source_primes=(3,5,7,11,13,17,19,23);box=(4,3,2,2,2,2,2,2)
    def upper_prefix_sum(p,depth=None):
        if p in(3,5):return 2+F(1,p-1)*(1-(F(0)if depth is None else F(1,p**(depth-1))))
        cap=C7 if p==7 else Dhi if p==11 else F(p-1,p-2)
        return 1+cap/F(p-1)*(1-(F(0)if depth is None else F(1,p**depth)))
    epsilon=F(1,15)*(prod(upper_prefix_sum(p)for p in source_primes)-
                      prod(upper_prefix_sum(p,e)for p,e in zip(source_primes,box)))
    worst=table_rows[20]
    need(worst['mean8']==F(106560,10591),'Worst shallow full-table mean')
    need(epsilon==F(171200075537100824,14616199250706178125)<F(3,256),'Whole omitted old-label query allowance')
    strengthened_margin=worst['tail_remaining_lower']-epsilon
    need(strengthened_margin>F(1,256),'One source tolerates full table, arbitrary omitted old labels,29 and all prime tail')
    return {'scope':'785 fixed marked old source; old-head77-multiple classes covered by one forbidden11 clean root per live7 root; '
                    'arbitrary extra old labels outside box(4,3,2,2,2,2,2,2); arbitrary29-ending classes; '
                    'all remaining support primes exceed729. Other low old labels must miss the chosen source.',
            'extra_original':{'modulus':77,'phase':2},'mass8':m,'cap7':C7,
            'conditional11_cap_at7root2':Dhi,'conditional11_cap_other_live_roots':Dlo,'marginal11_cap':Dbar,
            'actual_prefix_points':point_count,'finite_joint_caps':caps,
            'query58mod77_mass_normalized':joint,'product_of_actual_marginals':product_marginals,
            'joint_minus_marginal_product':joint-product_marginals,
            'normalized_joint_moments':joint_moment,'normalized_complete_mean':mean,'raw_complete_fourth8':K8,
            'stage29_kernel':'Haar on29, followed by deletion of the full actual pure/mixed union',
            'mass29_lower':mass29,'raw_complete_fourth29_bound':K29,
            'tail_allowance6561':allowance(),'tail_loss_upper':tail,'tail_remaining_lower':margin,
            'single_global11_cap_mean':simple_global_cap_mean,
            'new_class_mass_under785_source':before_joint_class_mass,
            'old_delete_then785_tail_ledger':old_deletion_tail,
            'finite_correlated_layout_control':{'layouts':layouts,'maximum':best,'tuple_cap':toy_expected},
            'actual_three_row_originals':triple,'marked_table_endpoint_rows':table_rows,
            'actual_five_row_originals':five_originals,'shallow_worst_table':worst,
            'extra_old_box':dict(zip(source_primes,box)),'nonunit_box_labels':prod(e+1 for e in box)-1,
            'omitted_old_query_allowance':epsilon,'full_table_omitted_old_and_tail729_margin':strengthened_margin,
            'inherited_analytic_premise':'Report734 HM14--HM15 / Rosser--Schoenfeld Theorem8',
            'lean_verification':False}


def gcd_anchor(modulus):
    # Each listed extra label is77 times an actual whole-mark3/5 cofactor.
    need(modulus%77==0 and 15%(modulus//77)==0,'Literal shallow-mark label cofactor')
    return modulus//77


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-result',type=Path);args=parser.parse_args()
    result=json.loads(json.dumps(calculate(),default=str))
    if args.write_result:args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:need(result==json.loads(Path(__file__).with_suffix('.json').read_text()),'Fresh joint result equals retained exact data')
    print(json.dumps({k:result[k]for k in ('mass8','normalized_complete_mean','mass29_lower','tail_remaining_lower','lean_verification')},indent=2))


if __name__=='__main__':main()
