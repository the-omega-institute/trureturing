#!/usr/bin/env python3
"""Exact cofactor-Gram obstruction on Report450's actual 702-label family.

Reuses the proved original comb/CRT construction. Computes one fixed uniform
actual-fibre lift; neither original head/private verification nor Lean is claimed.
"""
from fractions import Fraction as F
from math import isqrt,prod
from pathlib import Path
import argparse,json


def require(ok,why):
    if not ok:raise ValueError(why)


def primes(a,b):
    return [n for n in range(a,b+1) if all(n%d for d in range(2,isqrt(n)+1))]


def interval(x,places=12):
    scale=10**places;n=(x*scale).numerator//(x*scale).denominator
    return {'lower':str(F(n,scale)),'upper':str(F(n+1,scale)),'decimal_lower':f'{n//scale}.{n%scale:0{places}d}','decimal_upper':f'{(n+1)//scale}.{(n+1)%scale:0{places}d}'}


def moment(T,probs):
    mean=sum(probs,F(0));variance=sum((t*(1-t) for t in probs),F(0))
    return T*T*((1+mean)**2+variance)


def compute():
    P=primes(11,821);H=4;T=F(3,2)*(1-F(1,3**H));a=T/3;terminal=F(1,3**H)
    require(len(P)==138 and P[-2:]==[811,821] and 8+H+(H+1)*len(P)==702,'same Report450 original inventory')
    u=[F(1,p) for p in P];t=[F(1,p-1) for p in P]
    S0=sum(u,F(0));S1=sum(t,F(0));V1=sum((z*(1-z) for z in t),F(0))
    require(T==F(40,27) and S1>F(41,40) and sum(t[:-1],F(0))<=F(41,40),'existing exact first-crossing boundary')
    Z=prod(1-z for z in u);J0=moment(T,u);JR=moment(T,t);survivor=Z*JR;deleted=J0-survivor
    expected=T*(1+S1);gap=survivor-9*Z
    require(expected>3 and JR>F(893,81)>9 and V1>F(369,400),'strict second moment obstruction from existing first-moment threshold')
    # Disjoint actual 3-free owner partition: first outside zero prime.
    earlier_nonzero=F(1);owner_deleted=F(0);owner_loewner=F(0);owner_variance=F(0);owner_mass=F(0);owner_rows=[]
    for i,p in enumerate(P):
        mass=earlier_nonzero/F(p)
        probabilities=t[:i]+u[i+1:]
        meanW=T*(1+sum(probabilities,F(0)))
        varianceW=T*T*sum((z*(1-z) for z in probabilities),F(0))
        square=meanW*meanW+varianceW
        owner_deleted+=mass*square;owner_loewner+=mass*meanW*meanW;owner_variance+=mass*varianceW;owner_mass+=mass
        owner_rows.append({'prime':p,'mass':str(mass),'conditional_mean_W3':str(meanW),'conditional_variance_W3':str(varianceW)})
        earlier_nonzero*=1-u[i]
    require(owner_mass==1-Z and owner_deleted==deleted and owner_deleted-owner_loewner==owner_variance,'exact same-owner deletion partition and its Loewner remainder')
    # Projected ACTUAL PRIVATE 3-free regions (not the full owner partition).
    # Exactly one outside zero is necessary; positive-3 union leaves vertical
    # fraction terminal+a*1[N_other_ones=0].
    private_mass=F(0);private_loewner=F(0);private_second=F(0);private_rows=[]
    none_one=prod(1-z for z in t)
    for i,p in enumerate(P):
        one_zero=Z/F(p-1)
        zero_other=none_one/(1-t[i])
        meanN=S1-t[i];varN=V1-t[i]*(1-t[i])
        q=one_zero*(terminal+a*zero_other)
        v=one_zero*T*(terminal*(1+meanN)+a*zero_other)
        second=one_zero*T*T*(terminal*((1+meanN)**2+varN)+a*zero_other)
        credit=v*v/q
        require(credit<=second,'private-owner Cauchy-Schwarz on actual vertical density')
        private_mass+=q;private_loewner+=credit;private_second+=second
        private_rows.append({'prime':p,'exactly_one_zero_mass':str(one_zero),'private_vertical_mass':str(q),'W3_private_first_moment':str(v),'private_Loewner_credit':str(credit)})
    require(private_loewner<=private_second<=deleted,'actual private Loewner credit is below exact deletion')
    require(J0-deleted-9*Z==gap>0 and J0-owner_loewner-9*Z>=gap and J0-private_loewner-9*Z>=gap,'exact and both owner certificates fail with one strict same-law margin')
    vals={'T_H':T,'pure_3_union_fraction':a,'terminal_3_fraction':terminal,'S_unconditioned':S0,'S_surviving':S1,
          'surviving_N_variance':V1,'Z':Z,'E_W3_on_R':expected,'E_W3_squared_before_deletion':J0,
          'E_W3_squared_on_R':JR,'survivor_W3_square_mass':survivor,'exact_deleted_W3_square_mass':deleted,
          'exact_certificate_positive_gap':gap,'owner_partition_Loewner_credit':owner_loewner,
          'owner_partition_variance_gap':owner_variance,'private_vertical_mass':private_mass,
          'private_Loewner_credit':private_loewner,'private_weighted_second_moment':private_second,
          'private_uncredited_deleted_mass':deleted-private_second,'private_within_owner_variance_gap':private_second-private_loewner,
          'owner_certificate_positive_gap':J0-owner_loewner-9*Z,'private_certificate_positive_gap':J0-private_loewner-9*Z}
    return {'scope':'One common law for every head probability supported on Report450 actual S: lambda x Haar outside, then condition outside coordinates nonzero. Original 702 odd/distinct/irredundant family is a NONCOVER. These exact moments show failure of this specified lift/certificate under those weaker premises, not a counterexample under whole coverage or to Erdős #7. Ordinary rational calculation, no Lean.',
            'source_report':'450-weighted-original-depths-and-the-uniform-lift-boundary.md','head_modulus':1225,'ternary_height':H,'outside_primes':P,'original_count':702,
            'exact':{k:str(v) for k,v in vals.items() if k not in {'private_Loewner_credit','private_within_owner_variance_gap','private_certificate_positive_gap'}},
            'exact_private_credit_form':'sum_p [Z/(p-1)] T_H^2 [3^-H(1+S_surviving-1/(p-1))+(T_H/3) product_(r!=p)(1-1/(r-1))]^2 / [3^-H+(T_H/3) product_(r!=p)(1-1/(r-1))]',
            'enclosures':{k:interval(v) for k,v in vals.items()},
            'exact_check_counts':{'full_owner_rows':len(owner_rows),'private_owner_rows':len(private_rows),'same_owner_deletion_identity':True,'both_Loewner_bounds':True,'all_three_certificate_gaps_strictly_positive':True}}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=parser.parse_args()
    out=compute();args.output.write_text(json.dumps(out,indent=2)+'\n')
    for k in ('Z','E_W3_on_R','E_W3_squared_before_deletion','E_W3_squared_on_R','exact_deleted_W3_square_mass','exact_certificate_positive_gap','owner_partition_Loewner_credit','private_Loewner_credit'):
        print(k,out['enclosures'][k]['decimal_lower'],out['enclosures'][k]['decimal_upper'])


if __name__=='__main__':main()
