#!/usr/bin/env python3
"""Exact consumer for the nine-prime height-one source's full-depth continuation.

Report707 supplies the uniform source mass premise. This program recomputes
its scalar hinge, the height-lift response and same-source continuation
constants. It does not repeat the source's 6561-vertex comparison or claim Lean.
"""
from fractions import Fraction as F
from math import comb, factorial, prod
import json
import argparse
from pathlib import Path


def need(condition, message):
    if not condition:
        raise ValueError(message)


def a4(p):
    t=F(1,p-1)
    return 15*t+50*t*t+60*t**3+24*t**4


def cutoff_tail(B,ell,delta=F(2,7),r=21):
    need(B>=286 and ell>=4 and 3**ell<=B and 4*ell>=r,"complete-tail analytic range")
    coefficients=(F(1),)+tuple(F(x)/(1-delta) for x in (15,50,60,24))
    need(all(x<=comb(r,j) for j,x in enumerate(coefficients)),
         "quartic growth coefficient domination")
    constant=F(27,256)/delta**3/(1-delta)/3
    need(constant==F(21609,10240),"delta-two-sevenths quartic tail coefficient")
    return constant*F(2*ell*ell+1,2*ell*ell-1)**r * F(B,(B-1)**4) * sum(
        F(factorial(r),factorial(r-j)*(3*ell)**j) for j in range(r+1))


def calculate():
    qs=(5,7,11,13,17,19,23,29)
    alpha=F(4945117,39037950) # imported source premise, Report707 SS4
    # Recover the exact truncated-ternary hinge by multiplicative convolution.
    atoms={1:F(1,2),2:F(1,2)}
    mean=F(3,2)
    for p in qs:
        C=F(p-1,p-2)
        next_atoms={}
        pure_atoms={1:1-C/p}
        pure_atoms.update((n,C*F(p-1,p**n)) for n in range(2,9))
        for x,wx in atoms.items():
            for y,wy in pure_atoms.items():
                if x*y<=8:
                    next_atoms[x*y]=next_atoms.get(x*y,F(0))+wx*wy
        atoms=next_atoms
        mean*=1+F(1,p-2)
    hinge=mean-8+sum((8-n)*w for n,w in atoms.items() if n<8)
    expected_hinge=F(
        36645196186562338862630609094665977037308771636736172158282771192951,
        91259075188331710704228574683636183224582522412602232580056664218750)
    need(hinge==expected_hinge,"current convolution matches inherited exact H0")
    truncated_B=8+hinge/alpha
    full_B=F(5,4)*truncated_B
    need(full_B==F(
        129126856543850023127314117640338874610874565841696281911913189017951,
        9248166035728768426468350854567289757356579420496010975363041782500),
        "full-height first query budget")
    need(full_B<14,"head full-depth query bound")
    outside=(31,37)
    b={p:F(1,p-2) for p in outside}
    inventory=prod(1+x for x in b.values())-1
    singleton=sum(b.values())
    need(inventory==F(13,203) and singleton==F(64,1015),"pure-conditioned exterior inventories")
    reserve=1+singleton-full_B*inventory
    need(reserve>F(1,6),"same-source retained mass before tail")
    fourth_head=(1+F(3,2)*a4(3))*prod(1+F(p-1,p-2)*a4(p) for p in qs)/alpha
    fourth=fourth_head*prod(1+F(p-1,p-2)*a4(p) for p in outside)
    need(fourth==F(112120806922512384639472776047817897341,
                     15922408493425335546839040000000),"raw retained eleven-prime fourth envelope")
    tail=cutoff_tail(1300,6)
    final=reserve-fourth*tail
    need(final>F(1,40),"eleven-prime local-height complete-tail margin")
    density_cap=F(3,2)*prod(F(p-1,p-2) for p in qs+outside)/alpha

    # If3 is absent, reuse the empty-core pure-product source on all eleven
    # small coordinates; it has no height restriction at any of them.
    no3=(5,7,11,13,17,19,23,29,31,37,41)
    no3_b=tuple(F(1,p-2) for p in no3)
    no3_mass=2+sum(no3_b)-prod(1+x for x in no3_b)
    need(no3_mass==F(29127751,66621555),"missing-three actual-source reserve")
    no3_fourth=prod(1+F(p-1,p-2)*a4(p) for p in no3)
    need(no3_fourth==F(557206396227505564754974463643573027501307,
                         19608473796830796549095424000000000000),"missing-three fourth envelope")
    no3_final=no3_mass-no3_fourth*tail
    need(no3_final>F(1,40),"missing-three uses same1300 tail, not20000 cutoff")

    # The factor5/4 is sharp for a root-concentrated source with Haar suffix.
    sharp_B0=F(1); sharp_B1=F(1)
    sharp_full=sharp_B0+F(3,2)*sharp_B1
    need(sharp_full/(sharp_B0+sharp_B1)==F(5,4),"sharp root-Haar lift constant")
    # A source uniform in1 mod9 is NOT Haar after its first ternary digit.
    nonhaar_full=1+1+F(3,2)
    nonhaar_truncated=F(2)
    need(nonhaar_full>F(5,4)*nonhaar_truncated,"omitting the Haar-suffix premise fails")
    # Proper numerical-label payment: missing the old unit in a two-outside
    # original removes a real b31*b37 cost. Keep this separate from the pure
    # singleton terms that were already excluded.
    need(inventory-singleton==b[31]*b[37]>0,"two-outside old unit retained")

    return {
      "status":"exact_rational_checks_passed_not_Lean",
      "source_premise":"Report707 SS4, same actual lambda restricted to all head originals",
      "source_mass_lower":alpha,"nonternary_head_primes":qs,
      "truncated_comparator_mean":mean,"small_atoms":atoms,"hinge8":hinge,
      "truncated_first_budget":truncated_B,"full_first_budget":full_B,
      "full_first_budget_decimal":float(full_B),"outside_primes":outside,
      "outside_complete_inventory":inventory,"outside_singleton_inventory":singleton,
      "post_outside_mass_lower":reserve,"post_outside_mass_decimal":float(reserve),
      "head_fourth_upper":fourth_head,"post_outside_fourth_upper":fourth,
      "post_outside_haar_cap":density_cap,
      "tail":{"cutoff":1300,"ell":6,"delta":F(2,7),"growth":21,"factor":tail},
      "final_mass_lower":final,"final_mass_decimal":float(final),
      "simple_final_lower":F(1,40),
      "missing_three":{"primes":no3,"mass_lower":no3_mass,"fourth_upper":no3_fourth,
                       "final_mass_lower":no3_final,"final_mass_decimal":float(no3_final)},
      "controls":{"sharp_lift_factor":F(5,4),"missing_Haar_suffix_counterexample":True,
                  "double_outside_unit_payment":b[31]*b[37]},
      "scope":"At most11 original support primes at most1300; if3 is present, only originals wholly on the smallest min(9,n) such primes must have v3<=1. Other originals have unrestricted finite heights/phases/support. All larger support primes exceed1300.",
      "analytic_input":"Report734 HM14 Rosser--Schoenfeld Theorem8 consequence; ordinary premise",
    }


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate(),default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:
        need(result==json.loads(Path(__file__).with_suffix('.json').read_text()),
             'Fresh local-height result equals retained exact data')
    print(json.dumps({k:result[k] for k in ('full_first_budget_decimal','post_outside_mass_decimal','final_mass_decimal','simple_final_lower')},indent=2))
