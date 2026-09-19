#!/usr/bin/env python3
"""Exact universal weighted-root bounds; Python standard library only.

The accompanying mathematical proof supplies the weighted layout/cylinder
inequalities. This verifies all their parameter branches on the complete
continuous budget domain, including the nonvertex ternary-density edge.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import product
import json

def require(x,msg):
    if not x:raise ValueError(msg)

Y,A=F(1,4),F(7,8)
GCAP,RCAP=F(277,20),F(11,5)

def groups():
    return product(((F(0),F(0)),(Y,F(0)),(F(0),Y)),
                   (1-Y,F(1)),
                   ((F(0),F(0)),(Y/6,F(0)),(F(0),Y/6)))

def branch_margins(w,v,group):
    (alpha,beta),z,(t,u)=group
    d,e=z-alpha,z-beta
    n,m=w*d/3-t,v*e/3-u
    h,k=v+1,w+1
    normalizer=h*n+k*m
    x=(h*w+k*v)/3
    pure=(h*(3*n+d),3*h*n+F(2,3)*k*e,
          k*(3*m+e),3*k*m+F(2,3)*h*d)
    gamma=[(GCAP-1)*normalizer-p-A*(x+h*k) for p in pure]
    cylinder=[RCAP*normalizer-root-cap/6-Y*(x+mixed/3+maxh/6)
              for root,cap,mixed,maxh in product(
                  (h*n,k*m),(h*d,k*e),(h*w,k*v),(h,k))]
    return gamma+cylinder

def triangle_minimum(fn):
    # f(w,v)=a+b*w+c*v+d*w*v. There is no strict interior minimum
    # unless f is constant. The edges w=1 and v=1 are affine.
    a=fn(F(0),F(0));b=fn(F(1),F(0))-a
    c=fn(F(0),F(1))-a;d=fn(F(1),F(1))-a-b-c
    corners=((F(1,2),F(1)),(F(1),F(1,2)),(F(1),F(1)))
    tests=[(fn(w,v),(w,v)) for w,v in corners]
    # On v=3/2-w: f=A0+B0*w+C0*w^2, 1/2<=w<=1.
    B0=b-c+F(3,2)*d;C0=-d
    if C0>0:
        w=-B0/(2*C0)
        if F(1,2)<w<1:tests.append((fn(w,F(3,2)-w),(w,F(3,2)-w)))
    return min(tests),len(tests)



def uniform_margin(w,v,group,index):
    (alpha,beta),z,(t,u)=group
    d,e=z-alpha,z-beta
    n,m=w*d/3-t,v*e/3-u
    pure=(3*n+d,3*n+F(2,3)*e,3*m+e,3*m+F(2,3)*d)
    mixed=(w+1,v+1)
    return 13*(n+m)-pure[index//2]-A*((w+v)/3+mixed[index%2])


def balanced_R_margin(w,v,group,index):
    (alpha,beta),z,(t,u)=group
    n,m=w*(z-alpha)/3-t,v*(z-beta)/3-u
    normalizer=(v+1)*n+(w+1)*m
    return branch_margins(w,v,group)[4+index]+(F(15,7)-RCAP)*normalizer


# If a uniform Gamma branch exceeds 14, these fixed nonnegative
# multipliers certify every balanced R branch is <=15/7.
FALLBACK_MULTIPLIERS={
    1:tuple(map(F,('0','0','0','0','1/168','1/21','0','0',
                   '0','0','8/21','1/21','0','0','0','0'))),
    4:tuple(map(F,('0','0','0','0','1/21','8/21','0','0',
                   '0','0','1/21','1/168','0','0','0','0'))),
}


def compute_certificate():
    branch_count=point_count=0
    minimum=None
    def verify_everywhere(fn):
        nonlocal branch_count,point_count,minimum
        for group in groups():
            (margin,point),count=triangle_minimum(lambda w,v:fn(w,v,group))
            require(margin>=0,'negative continuous-domain branch margin')
            branch_count+=1;point_count+=count
            minimum=margin if minimum is None else min(minimum,margin)
    for index in range(20):
        verify_everywhere(lambda w,v,g:branch_margins(w,v,g)[index])
    balanced_count=branch_count
    require(balanced_count==360,'expected 360 balanced-law polynomial minima')
    for index in range(8):
        if index not in FALLBACK_MULTIPLIERS:
            verify_everywhere(lambda w,v,g:uniform_margin(w,v,g,index))
        else:
            for j,multiplier in enumerate(FALLBACK_MULTIPLIERS[index]):
                require(multiplier>=0,'negative fallback multiplier')
                verify_everywhere(lambda w,v,g:balanced_R_margin(w,v,g,j)+
                                   multiplier*uniform_margin(w,v,g,index))
    require(branch_count==1044,'expected 1044 continuous polynomial minima')

    root_lower=F(1,2)*(1-2*Y)/3-Y/6
    require(root_lower==F(1,24)>0,'root positivity failed')
    require(F(215,24)<=GCAP<14 and F(17,12)<=F(15,7)<RCAP,
            'absent-modulus-3 branch failed')
    propagated=[]
    for name,gamma,r in (('balanced',GCAP,RCAP),('hybrid',F(14),F(15,7))):
        removed_7=r/5
        require(0<=removed_7<1,'prime-7 deletion denominator failed')
        gamma_357=(gamma*F(5,3)-removed_7)/(1-removed_7)
        r_357=((r+1)*F(6,5)-1)/(1-removed_7)
        removed_11=r_357/9
        require(0<=removed_11<1,'prime-11 deletion denominator failed')
        gamma_35711=(gamma_357*F(61,45)-removed_11)/(1-removed_11)
        propagated.append({'law':name,'Gamma_35':str(gamma),'R_35':str(r),
                           'removed_mass_7_bound':str(removed_7),
                           'Gamma_357_bound':str(gamma_357),'R_357_bound':str(r_357),
                           'direct_Gamma_35711_bound':str(gamma_35711)})
    require(F(propagated[1]['Gamma_357_bound'])<F(653,16),
            'hybrid three-prime Gamma does not improve the earlier transport bound')
    require(F(propagated[1]['R_357_bound'])>F(1649,360),
            'the stated three-prime R tradeoff changed')
    require(F(propagated[1]['direct_Gamma_35711_bound'])>F(168332,1591),
            'the stated four-prime comparison changed')
    return {'schema':'erdos7-nonuniform-root-v1',
            'balanced_rule':'raw density h_A=v+1, h_B=w+1; normalize',
            'hybrid_rule':'uniform if refined uniform Gamma envelope <=14; otherwise balanced',
            'balanced_Gamma_bound':str(GCAP),'balanced_R_bound':str(RCAP),
            'hybrid_Gamma_bound':'14','hybrid_R_bound':'15/7',
            'root_density_lower_bound':str(root_lower),
            'absent_modulus_3_uniform_Gamma_bound':'215/24',
            'absent_modulus_3_uniform_R_bound':'17/12',
            'balanced_polynomial_minima':balanced_count,
            'fallback_polynomial_minima':branch_count-balanced_count,
            'total_polynomial_minima':branch_count,'point_evaluations':point_count,
            'global_minimum_margin':str(minimum),
            'fallback_multipliers':{str(k):list(map(str,v)) for k,v in FALLBACK_MULTIPLIERS.items()},
            'coherent_conditioned_propagation':propagated}


def main():
    from pathlib import Path
    actual=json.loads(read_artifact_text(Path(__file__).resolve().parent / 'certificates/nonuniform_root_certificate.json'))
    expected=compute_certificate()
    require(actual==expected,'fixed certificate differs from exact recomputation')
    print('Verified 1044 continuous polynomial minima: balanced (Gamma,R) <= (277/20,11/5); '
          'hybrid (Gamma,R) <= (14,15/7).')
    print('Hybrid conditioned three-prime law: Gamma <=481/12, R <=97/20. '
          'Direct four-prime bound350/3 does not improve the uniform lcm-block bound.')


if __name__=='__main__':main()
