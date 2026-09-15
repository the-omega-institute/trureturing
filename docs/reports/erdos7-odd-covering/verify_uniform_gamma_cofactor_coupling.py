#!/usr/bin/env python3
"""Exact uniform Gamma35 bound from coupling the shared zero-exponent layout.

Python3.9+ standard library only. The accompanying proof gives the layout
inequality and the continuous linear-fractional vertex reduction. This checks
all72 rational branches and the absent-modulus-3 branch, with no solver.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


def require(condition,message):
    if not condition:
        raise ValueError(message)


def compute_certificate():
    y,a=F(1,4),F(7,8)
    cap=F(55,4)
    require(a-2*y==F(3,8)>0,'positive-positive lcm coefficient mismatch')
    require(a-y==F(5,8)>0,'combined lcm coefficient mismatch')
    records=[]
    denominators=[]
    for (w,v),(alpha,beta),z in product(
            ((F(1,2),F(1)),(F(1),F(1,2)),(F(1),F(1))),
            ((F(0),F(0)),(y,F(0)),(F(0),y)),(1-y,F(1))):
        x=(w+v)/3
        d,e=z-alpha,z-beta
        # Shift all deep mixed deletion to the unselected root, then
        # enlarge it to y/6. The proof shows both operations increase
        # the selected-root envelope while preserving positive denominators.
        n=w*d/3
        m=v*e/3-y/6
        require(n>=F(1,12)>0 and m>=F(1,24)>0,
                'relaxed root positivity failed')
        s=n+m
        denominators.append(s)
        for pure_branch,extra in (('selected',d),('other',F(2,3)*e)):
            for norm_branch,root_width in (('selected',w),('other',v)):
                # The actual full bound takes the maximum over these
                # four affine branches. Every branch is checked separately.
                numerator=3*n+extra+y*(x+w+1)+(a-y)*(x+root_width+1)
                value=1+numerator/s
                require(value<=cap,'a coupled uniform Gamma branch exceeds55/4')
                records.append({'w_v_alpha_beta_z':list(map(str,(w,v,alpha,beta,z))),
                                'pure_branch':pure_branch,'norm_branch':norm_branch,
                                'value':str(value)})
    require(len(denominators)==18 and len(records)==72,'vertex/branch count mismatch')
    maximum=max(F(row['value']) for row in records)
    require(maximum==cap,'exact coupled envelope maximum mismatch')
    x,z=F(5,6),1-y
    absent_denominator=x*z-y/2
    require(absent_denominator>0,'absent-modulus-3 denominator is not positive')
    absent=1+(2*z+a*x+2*a)/absent_denominator
    require(absent==F(215,24)<cap,'absent-modulus-3 branch failed')
    # The old57/4 budget vertex is realizable as an infinite-height limit.
    w,v,alpha,beta,z=F(1,2),F(1),F(0),y,1-y
    x=(w+v)/3
    n=w*(z-alpha)/3
    m=v*(z-beta)/3-y/6
    old=1+(3*n+(z-alpha)+a*x+2*a)/(n+m)
    new=1+(3*n+(z-alpha)+y*(x+w+1)+(a-y)*(x+v+1))/(n+m)
    require(old==F(57,4) and new==F(55,4),'shared-layout improvement at old extremum failed')
    return {'schema':'uniform-gamma-cofactor-coupling-v1','prime_support':[3,5],
            'Gamma_bound':str(cap),'same_law':'uniform complete survivor law',
            'positive_lcm_coefficient':str(a),'zero_to_positive_coefficient':str(y),
            'remaining_Gamma_coefficient':str(a-y),
            'parameter_vertex_count':18,'affine_branch_count':72,
            'minimum_vertex_survivor_density':str(min(denominators)),
            'maximizers':[row for row in records if F(row['value'])==maximum],
            'absent_modulus_3_bound':str(absent),
            'absent_modulus_3_denominator':str(absent_denominator),
            'old_budget_extremum':{'old_envelope':str(old),'coupled_envelope':str(new),
                                   'n':str(n),'m':str(m)}}


def main():
    data=json.loads(Path(__file__).with_name('uniform_gamma_cofactor_certificate.json').read_text())
    expected=compute_certificate()
    require(data==expected,'fixed certificate differs from exact recomputation')
    print('Verified all72 continuous-envelope branches: uniform Gamma35 <=55/4.')
    print('Positive denominators and absent-modulus-3 bound215/24 verified; '
          'the old57/4 extremal budget now has coupled bound55/4.')


if __name__=='__main__':
    main()
