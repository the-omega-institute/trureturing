#!/usr/bin/env python3
"""Complete original-low-test anchoring on the unchanged PG1 probability.

Recompute rational cylinder observations, the all-height coefficient formulas,
and the complete outside-box remainder.  The aligned2 consumer uses separately
verified, hash-bound source survival and 11/13 charge certificates.  This does
not evaluate the inside-box anchored layout maxima or a global low-test search.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import lcm
from pathlib import Path
import argparse
import json

HERE=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:raise ArithmeticError(message)

def prod(values):
    out=F(1)
    for value in values:out*=value
    return out

def valuation(d,p):
    out=0
    while d%p==0:out+=1;d//=p
    return out

def evaluate(data,source_directory):
    names=('mod3_conditioned_geometry_certificate.json',
           'original9_conditioned_geometry_certificate.json',
           'original9_convex_transfer_certificate.json',
           'pg1_joint_tail_certificate.json','pg1_signed_g2_certificate.json')
    raw={name:(source_directory/name).read_bytes() for name in names}
    hashes={name:sha256(value).hexdigest() for name,value in raw.items()}
    require(hashes==data['source_sha256'],'five unchanged canonical certificate inputs')
    source,m9,cx,joint,g2=(json.loads(raw[name]) for name in names)
    require(m9['source_sha256']==cx['mod3_source_sha256']==hashes[names[0]]
            and cx['original9_source_sha256']==hashes[names[1]]
            and joint['source_sha256']=={name:hashes[name] for name in names[:3]}
            and g2['source_joint_sha256']==hashes[names[3]],'source certificate dependency chain')
    case=next(c for c in source['cases'] if c['name']=='PG1')
    pts=case['points'];weights=case['weight_numerators'];den=case['weight_denominator']
    require(len(pts)==75 and len(weights)==75 and sum(weights)==den==1000000007
            and all(w>=0 for w in weights),'same 75-point PG1 law')
    require(pts==[x for x in range(315) if all(x%d!=a for d,a in case['family'])],
            'actual low carrier')
    ds=[d for d in range(1,316) if 315%d==0];primes=(3,5,7);heights=(2,1,1)
    sat={d:{p for p,h in zip(primes,heights) if valuation(d,p)==h} for d in ds}
    aa={d:prod(F(p,p-1) for p in sat[d]) for d in ds}
    gamma={d:aa[d]-1 for d in ds}
    bb={(d,e):prod(F(p*(p+1),(p-1)**2) if p in sat[d]&sat[e] else F(p,p-1)
                       for p in sat[d]|sat[e]) for d in ds for e in ds}
    kappa={(d,e):bb[d,e]-aa[d]-aa[e]+1 for d in ds for e in ds}
    require(gamma[1]==gamma[3]==0 and min(gamma.values())>=0 and min(kappa.values())>=0,
            'nonnegative full higher-label coefficients')
    def caps(values):
        require(len(values)==len(pts) and all(v>=0 for v in values),'nonnegative finite low measure')
        return {d:max(sum(v for x,v in zip(pts,values) if x%d==a)
                      for a in range(d)) for d in ds}
    plain_caps=caps(weights)
    high=sum((kappa[d,e]*F(plain_caps[lcm(d,e)],den) for d in ds for e in ds),F(0))
    q0=F(m9['result']['survival_lower']);G=F(m9['result']['Gamma_upper'])
    rho=F(cx['result']['fixed11_13_consumer']['retained_mass_lower'])
    require(q0>0 and rho>0 and q0==F(joint['result']['source_survival_lower']),
            'separately verified independent source and final survival')
    def anchored(family,reference):
        require(set(family)==set(ds) and all(type(a) is int and 0<=a<d for d,a in family.items()),
                'one genuine original class for each low divisor')
        load=[sum(int(x%d==family[d]) for d in ds) for x in pts]
        b_caps=caps([w*b for w,b in zip(weights,load)])
        floor_caps=caps([w*max(reference-b*b,0) for w,b in zip(weights,load)])
        square=F(sum(w*b*b for w,b in zip(weights,load)),den)
        cross=2*sum((gamma[d]*F(b_caps[d],den) for d in ds),F(0))
        U=square+cross+high
        deletion=sum((gamma[d]*F(floor_caps[d],den) for d in ds),F(0))
        excess=U+deletion-reference
        bound=reference+excess/(q0 if excess>=0 else 1)
        return {'original_low_residues':{str(d):a for d,a in family.items()},'reference':reference,
                'low_load':load,'weighted_load_caps':{str(d):v for d,v in b_caps.items()},
                'positive_deleted_floor_caps':{str(d):v for d,v in floor_caps.items()},
                'low_square':str(square),'anchored_cross':str(cross),'higher_higher':str(high),
                'unconditional_square_upper':str(U),'ordinary_deletion_upper':str(deletion),
                'signed_source_excess':str(excess),'head_square_upper':str(bound)}
    aligned=anchored({d:2%d for d in ds},29)
    require(max(aligned['low_load'])==12,'positive-part floor is necessary')
    independent_cross=2*sum((gamma[d]*F(plain_caps[lcm(d,e)],den)
                              for d in ds for e in ds),F(0))
    saving=independent_cross-F(aligned['anchored_cross'])
    require(saving>0,'strict saving over independent cross-term caps')
    # All omitted depths are accounted for.  Compare direct box summation
    # with a separately factored product of one-prime truncated moments.
    cut=(8,5,4);box=list(product(*(range(n+1) for n in cut)))
    probs={z:prod(F(p-1,p**(n+1)) for p,n in zip(primes,z)) for z in box}
    r={(d,z):prod(1+z[primes.index(p)] for p in sat[d])-1 for d in ds for z in box}
    moments={p:[sum((F(p-1,p**(z+1))*(1+z)**k for z in range(n+1)),F(0))
                for k in range(3)] for p,n in zip(primes,cut)}
    mass=prod(moments[p][0] for p in primes)
    require(mass==sum(probs.values()),'independent factored box probability')
    linear={d:prod(moments[p][int(p in sat[d])] for p in primes) for d in ds}
    first={d:gamma[d]-sum((probs[z]*r[d,z] for z in box),F(0)) for d in ds}
    second={(d,e):kappa[d,e]-sum((probs[z]*r[d,z]*r[e,z] for z in box),F(0))
            for d in ds for e in ds}
    for d in ds:
        require(first[d]==gamma[d]-linear[d]+mass,'factored first remainder')
        for e in ds:
            pair=prod(moments[p][int(p in sat[d])+int(p in sat[e])] for p in primes)
            require(second[d,e]==kappa[d,e]-pair+linear[d]+linear[e]-mass,
                    'factored second remainder')
    require(min(first.values())>=0 and min(second.values())>=0,'nonnegative complete remainders')
    outside=((1-mass)*F(aligned['low_square'])+
             2*sum((first[d]*F(aligned['weighted_load_caps'][str(d)],den) for d in ds),F(0))+
             sum((second[d,e]*F(plain_caps[lcm(d,e)],den) for d in ds for e in ds),F(0)))
    # The ordinary 11/13 comparison and the stronger current same-Q charge
    # comparison both concern the same fixed aligned2 zero-tail tuple.
    P=F(1403,630);M=F(4,3);GB=F(aligned['head_square_upper'])
    J=M*GB+(P-M)*G;simple=1+(J-1)/rho
    current=next(r for r in g2['result']['records']
                 if (r['final_root3'],r['final_root9'])==(2,2))
    source22=next(r for r in m9['result']['records'] if (r['root3'],r['root9'])==(2,2))
    source_excess=F(aligned['signed_source_excess']);old_excess=F(source22['criterion_excess'])
    A=F(current['inherited_criterion_constant'])+M*(29-33)
    B=F(current['inherited_criterion_inverse_Q'])+M*(source_excess-old_excess)
    require(B>0,'complete aligned2 common-Q criterion maximized at q0')
    excess=A+B/q0
    require(excess<0,'negative aligned2 criterion at final reference149')
    fine=149+excess
    require(fine<F(data['rounded_aligned2_Gamma13_upper']), 'strict aligned2 consumer bound')
    # This actual low layout is a boundary of the inexpensive *relaxation*.
    # Its computed upper bound is not a lower bound on its actual moment.
    fixture={int(d):a for d,a in data['boundary_fixture'].items()}
    boundary=anchored(fixture,33)
    require(F(boundary['head_square_upper'])>G,'ordinary anchored relaxation does not uniformly dominate source G')
    boundary['scope']='attained value of the explicit cheap upper-bound functional; not a lower bound on an actual moment'
    return {'scope':'general anchored all-height inequalities, with one fixed aligned2 PG1 test consumer; no global low-test improvement',
            'source_sha256':hashes,'point_count':len(pts),'weight_denominator':den,
            'plain_caps':{str(d):v for d,v in plain_caps.items()},
            'gamma':{str(d):str(v) for d,v in gamma.items()},
            'kappa':{str(d)+','+str(e):str(v) for (d,e),v in kappa.items()},
            'source_survival_lower':str(q0),'source_global_head_square_upper':str(G),
            'current_global_Gamma13_upper':g2['result']['Gamma13_upper'],
            'aligned2':aligned,'independent_cross_saving':str(saving),
            'outside_box':{'depth_box':list(cut),'probability':str(1-mass),
                           'first_coefficients':{str(d):str(v) for d,v in first.items()},
                           'second_coefficients':{str(d)+','+str(e):str(v) for (d,e),v in second.items()},
                           'aligned2_square_tail_upper':str(outside),
                           'scope':'outside contribution only; inside anchored layout maxima not evaluated'},
            'aligned2_simple_11_13':{'zero_tail_square_upper':str(J),'Gamma13_upper':str(simple)},
            'aligned2_current_charge':{'criterion_constant':str(A),'criterion_inverse_Q':str(B),
                                        'criterion_excess':str(excess),'Gamma13_upper':str(fine)},
            'cheap_relaxation_boundary':boundary}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',type=Path,default=HERE/'pg1_anchored_square_certificate.json')
    parser.add_argument('--source-directory',type=Path,default=HERE)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args();data=json.loads(args.certificate.read_text())
    require(data['schema']=='erdos7-pg1-anchored-square-v1','certificate schema')
    result=evaluate(data,args.source_directory)
    if args.write:
        data['result']=result;args.certificate.write_text(json.dumps(data,indent=2)+'\n')
    else:require(data['result']==result,'exact anchored observations, remainders and branch consumers')
    print(json.dumps({'aligned2_head_upper':result['aligned2']['head_square_upper'],
                      'aligned2_Gamma13_upper':result['aligned2_current_charge']['Gamma13_upper'],
                      'aligned2_Gamma13_decimal':float(F(result['aligned2_current_charge']['Gamma13_upper'])),
                      'unchanged_global_Gamma13_upper':result['current_global_Gamma13_upper'],
                      'cheap_boundary_head_upper':result['cheap_relaxation_boundary']['head_square_upper']}),flush=True)

if __name__=='__main__':main()
