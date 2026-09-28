#!/usr/bin/env python3
"""Exact controls for absolute cubic continuation past 4000 and 9000.

The analytic Rosser--Schoenfeld prime-product premise is inherited from
Chapter33 SH11; this program verifies substitutions, not that theorem.
"""
from fractions import Fraction as F
from itertools import product
from math import prod,factorial,lcm,comb
from pathlib import Path
import json


def need(ok,message):
    if not ok:raise RuntimeError(message)


from hashlib import sha256
import runpy

DEPENDENCIES = {
    "fibre_credit_depth_two_four_fresh_heights.py": "f93c2c100dc8f4351a66be0ca18d5ce8992723500e6b393bf0a63b773931261c",
    "fibre_credit_depth_two_four_fresh_heights.json": "daedcfa370ad5979704109a926956d004343c33270a5e451d578d15071251041",
}

def calculate():
    directory = Path(__file__).resolve().parent
    for name, digest in DEPENDENCIES.items():
        need(sha256((directory / name).read_bytes()).hexdigest() == digest,
             'pinned four-direction source dependency: ' + name)
    source = runpy.run_path(str(directory / 'fibre_credit_depth_two_four_fresh_heights.py'))
    verified = json.loads(json.dumps(source['calculate']()))
    need(verified == json.loads((directory / 'fibre_credit_depth_two_four_fresh_heights.json').read_text()),
         'replayed complete four-direction source certificate')
    # All live clipped kernels on a complete height-two ternary coordinate.
    p,H=3,2
    row_checks=prefix_checks=0
    for mask in range(1<<(p**H)):
        bad=tuple(y for y in range(p**H) if (mask>>y)&1)
        beta=F(len(bad),p**H)
        for delta in (F(1,4),F(1,3),F(1,2)):
            denom=1-min(beta,delta)
            R=tuple(F(0) if y in bad else F(1,p**H)/denom for y in range(p**H))
            mass=sum(R,F(0))
            loss=max(beta-delta,F(0))/(1-delta)
            need(mass==1-loss and 0<=mass<=1,'exact live-kernel absolute row mass')
            need(loss<=F(4)*beta**3/(27*delta**2*(1-delta)),
                 'the actual deletion loss satisfies the cubic pointwise majorant')
            for e in range(H+1):
                for a in range(p**e):
                    actual=sum((R[y] for y in range(p**H) if y%(p**e)==a),F(0))
                    if e==0:need(actual<=1,'zero-depth row uses mass1, not the distorted cap')
                    else:need(actual<=F(1,p**e)/(1-delta),'every actual deep cylinder has the absolute cap')
                    prefix_checks+=1
            row_checks+=1

    # An actual finite original stage includes overlap, pure powers and mixed labels.
    OLD=5;CURRENT=9;PERIOD=45;delta=F(1,3)
    originals=((3,0),(9,3),(15,7),(45,14))
    old_mass=F(3,4)
    old_point_mass=old_mass/OLD
    Kold=old_mass*F(12,5)
    nu={};alpha={};beta={}
    for x in range(OLD):
        fibre=tuple(z for z in range(PERIOD) if z%OLD==x)
        bad=tuple(z for z in fibre if any(z%d==a for d,a in originals))
        beta[x]=F(len(bad),CURRENT)
        ub=F(0)
        for d,a in originals:
            oldcofactor=d
            currentfactor=1
            while oldcofactor%3==0:
                oldcofactor//=3;currentfactor*=3
            if x%oldcofactor==a%oldcofactor:ub+=F(1,currentfactor)
        alpha[x]=ub
        need(beta[x]<=alpha[x],'actual bad union is below the completed-load union bound')
        for z in fibre:
            nu[z]=F(0) if z in bad else old_point_mass/F(CURRENT)/(1-min(beta[x],delta))
    new_mass=sum(nu.values(),F(0))
    actual_loss=old_mass-new_mass
    alpha_cube=sum((old_point_mass*alpha[x]**3 for x in range(OLD)),F(0))
    theta=sum((F(1,3**e) for e in (1,2)),F(0))
    A3H=sum((F((e+1)**3-e**3,3**e) for e in (1,2)),F(0))
    Knew=Kold*(1+A3H/(1-delta))
    D=4*Kold*theta**3/(27*delta**2*(1-delta))
    need(alpha_cube<=Kold*theta**3 and actual_loss<=D,'actual absolute cubic loss chain')
    need(new_mass==F(13,20),'the stage is not normalized after survival')
    positive=tuple(z for z in range(PERIOD) if nu[z])
    common_den=lcm(*(v.denominator for v in nu.values()))
    weights=tuple(int(nu[z]*common_den) for z in positive)
    moduli=(1,3,5,9,15,45)
    columns=tuple(tuple(tuple(int(z%d==a) for z in positive) for a in range(d)) for d in moduli)
    max_numerator=-1
    query_count=0
    for chosen in product(*columns):
        value=sum(w*sum(bits)**3 for w,bits in zip(weights,zip(*chosen)))
        if value>max_numerator:max_numerator=value
        query_count+=1
    actual_query_cube=F(max_numerator,common_den)
    need(query_count==91125 and actual_query_cube<=Knew,'all complete actual45 query phases obey the propagated cube bound')

    # Three-exponent lcm counts are checked separately from the stage enumeration.
    triple_checks=0
    for q in (3,5,29,41):
        for height in range(1,5):
            raw=sum((F(1,q**max(exps)) for exps in product(range(height+1),repeat=3)),F(0))
            grouped=1+sum((F((e+1)**3-e**3,q**e) for e in range(1,height+1)),F(0))
            need(raw==grouped,'every exponent triple is counted once by its maximum')
            triple_checks+=1

    G3=F(verified["source_cubic_upper"])
    EW=F(verified["mean_W_lower"])
    rho4=EW/(28*30*36*40)
    def A3(q):return F(7*q*q-2*q+1,(q-1)**3)
    kappa4=G3*prod((1+A3(q) for q in (29,31,37,41)),start=F(1))
    need(rho4==F(21201970586591,5920223700787200),'one actual four-axis absolute reserve')
    need(kappa4==F(5006518103820493161366055877,391240726784822476800000),
         'unrestricted fresh-height cubic initialization on the same dominated source')

    B=4000;ell=7;growth=11
    need(B>=286 and ell>=6 and 3**ell<=B,'inherited prime-product and decreasing-integral range')
    c=F(2*ell**2+1,2*ell**2-1)
    poly=sum((F(factorial(growth),factorial(growth-j)*(2*ell)**j)
              for j in range(growth+1)),F(0))
    tau=c**growth*F(B,(B-1)**3)*poly
    tail=kappa4*tau
    reserve=rho4-tail
    need(c==F(99,97) and tail<rho4 and reserve>F(1,2100),'strict complete large-prime tail margin')
    # t=1/(p-1): A3=7t+12t^2+6t^3 and the entire growth polynomial
    # is coefficientwise bounded by (1+t)^11.
    growth_coefficients={0:F(1),1:F(21,2),2:F(18),3:F(9)}
    growth_slacks=tuple(F(comb(11,j))-growth_coefficients.get(j,F(0)) for j in range(12))
    need(all(v>=0 for v in growth_slacks) and growth_slacks[1:4]==(F(1,2),F(37),F(156)),
         'the degree11 factor bounds the exact cubic growth at every p>1')
    for q in (3,5,29,41):
        t=F(1,q-1)
        need(A3(q)==7*t+12*t*t+6*t**3,'exact cubic Haar factor in reciprocal-gap coordinates')

    # Explicit reset to full-head Haar restricted to the actual head survivors.
    # This permits arbitrary old-coordinate exponents on tail-touching originals.
    reset_rho=F(verified["Haar_lower"])
    reset_kappa=prod((1+A3(q) for q in (3,5,7,11,13,17,19,23,29,31,37,41)),start=F(1))
    reset_B=9000;reset_ell=8
    need(reset_B>=286 and reset_ell>=6 and 3**reset_ell<=reset_B,'reset analytic range')
    reset_c=F(2*reset_ell**2+1,2*reset_ell**2-1)
    reset_poly=sum((F(factorial(growth),factorial(growth-j)*(2*reset_ell)**j)
                    for j in range(growth+1)),F(0))
    reset_tau=reset_c**growth*F(reset_B,(reset_B-1)**3)*reset_poly
    reset_tail=reset_kappa*reset_tau
    reset_remaining=reset_rho-reset_tail
    need(reset_remaining>F(1,150000),'strict reset margin with arbitrary earlier exponents on tail originals')
    # Exact scalar factorization underlying the cubic loss majorant.
    for delta in (F(1,4),F(1,3),F(1,2)):
        for alpha_value in (delta,F(3,2)*delta,2*delta,3*delta):
            gap=4*alpha_value**3-27*delta**2*(alpha_value-delta)
            need(gap==(2*alpha_value-3*delta)**2*(alpha_value+3*delta),
                 'nonnegative factorization of the sharp cubic clipping inequality')

    out={'scope':'Ordinary absolute-submeasure cubic continuation; finite exact controls, not Lean. '
                 'The analytic prime-product theorem is inherited from Chapter33 SH11. '
                 'Final reserve is distorted mass, not a uniform final Haar density.',
         'kernel_rows_checked':row_checks,'kernel_prefix_caps_checked':prefix_checks,
         'actual_stage':{'old_period':OLD,'new_period':PERIOD,'originals':originals,
                         'old_mass':str(old_mass),'new_mass':str(new_mass),
                         'actual_loss':str(actual_loss),'union_load_cube':str(alpha_cube),
                         'loss_upper':str(D),'propagated_cube_upper':str(Knew),
                         'complete_queries_checked':query_count,'actual_maximum_cube':str(actual_query_cube)},
         'triple_exponent_count_checks':triple_checks,
         'four_axis_reserve':str(rho4),'four_axis_cubic_potential':str(kappa4),
         'cutoff_exclusive':B,'ell':ell,'prime_product_constant':str(c),
         'growth_exponent':growth,'integral_polynomial':str(poly),
         'tail_factor':str(tau),'tail_debit':str(tail),'tail_debit_decimal':float(tail),
         'remaining_absolute_mass_lower':str(reserve),'remaining_decimal':float(reserve),
         'remaining_greater_than':'1/2100',
         'growth_polynomial_coefficient_slacks':list(map(str,growth_slacks)),
         'haar_reset':{'head_Haar_reserve':str(reset_rho),'complete_all_height_cubic':str(reset_kappa),
                       'cutoff_exclusive':reset_B,'ell':reset_ell,'prime_product_constant':str(reset_c),
                       'integral_polynomial':str(reset_poly),'tail_factor':str(reset_tau),
                       'tail_debit':str(reset_tail),'tail_debit_decimal':float(reset_tail),
                       'remaining_absolute_mass_lower':str(reset_remaining),
                       'remaining_decimal':float(reset_remaining),'remaining_greater_than':'1/150000'},
         'exact_checks_passed':True}
    out["source_replayed"] = True
    out["dependency_hashes"] = DEPENDENCIES
    return out


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
             'retained result agrees with source replay and cubic tail arithmetic')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
