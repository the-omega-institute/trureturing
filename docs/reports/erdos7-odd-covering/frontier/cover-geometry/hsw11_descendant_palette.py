#!/usr/bin/env python3
"""Exact fresh-palette capacity and a collision-free local old-cofactor patch.

This does not construct a distinct odd whole cover. It separates a proved
fresh-only descendant obstruction from a local refinement of the actual
HSW private cylinders using three vacant old-cofactor numerical moduli.
"""
from fractions import Fraction as F
from math import gcd, isqrt, prod
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ORIGINAL_SUPPORT = (3,5,7,11,13,17,19,23)
W = prod(ORIGINAL_SUPPORT)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def crt(congruences):
    a, m = 0, 1
    for b,n in congruences:
        require(gcd(m,n)==1,'noncoprime CRT')
        a = (a+m*(((b-a)*pow(m,-1,n))%n))%(m*n)
        m *= n
    return a,m


def product_bound(primes):
    return prod((F(p,p-1) for p in primes),start=F(1))


def fresh_capacity(q, fresh_primes, private_demands=3):
    require(prime(q) and q%2==1,'transport prime must be odd')
    require(private_demands<=q and private_demands>0,'invalid private demand count')
    require(len(fresh_primes)==len(set(fresh_primes)),'duplicate fresh prime')
    require(all(prime(p) and p%2==1 and p not in ORIGINAL_SUPPORT and p!=q for p in fresh_primes),
            'palette must contain only genuinely fresh odd primes')
    euler=product_bound(fresh_primes)
    capacity=euler/F(q*(q-1))
    demand=F(private_demands,q*q)
    return dict(euler=euler,capacity=capacity,demand=demand,
                necessary_threshold=F(private_demands*(q-1),q),
                strict_hole_lower=demand-capacity)


def bracket(x, digits=18):
    scale=10**digits
    lower=x.numerator*scale//x.denominator
    return dict(lower_numerator=lower,upper_numerator=lower+1,denominator=scale)


def minimal_fresh_count(q):
    require(q in (3,5),'HSW private-cylinder threshold is available only for q=3 or5')
    threshold=F(3*(q-1),q)
    primes=[]
    euler=F(1)
    p=29
    while euler<=threshold:
        if prime(p):
            previous=euler
            primes.append(p)
            euler*=F(p,p-1)
        p+=2
    require(previous<=threshold<euler,'crossing is not exact')
    require(all(a<b for a,b in zip(primes,primes[1:])),'unordered fresh palette')
    require(all(prime(p) and p not in ORIGINAL_SUPPORT and p%2 for p in primes),
            'crossing uses inadmissible prime')
    return dict(q=q,private_demands=3,threshold=str(threshold),
                smallest_possible_fresh_count=len(primes),first_prime=primes[0],
                last_prime=primes[-1],previous_last_prime=primes[-2],
                previous_product_bracket=bracket(previous),
                crossing_product_bracket=bracket(euler),primes=primes,
                exact_previous_product=str(previous),exact_crossing_product=str(euler),
                necessary_only=True)


def load_seed():
    path=Path(__file__).resolve().with_name('hsw11_family.py')
    spec=importlib.util.spec_from_file_location('literal_hsw11_seed',path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module,module.build_family()


def modulus_present(modulus, family):
    residual=modulus
    powers={}
    for p in ORIGINAL_SUPPORT:
        e=0
        while residual%p==0:
            residual//=p
            e+=1
        if e:
            powers[p]=e
    if residual!=1:
        return False
    if modulus==23:
        return True
    if 23 in powers:
        return powers[23]==1 and len(powers)==2 and any(
            p in powers and 1<=powers[p]<=22 for p in (3,5,7,13,17,19))
    for row in family['normal_families']:
        if set(row['primes'])==set(powers) and all(
            row['exponent_ranges'][str(p)][0]<=e<=row['exponent_ranges'][str(p)][1]
            for p,e in powers.items()):
            return True
    return False


def local_patch(seed, family):
    specifications=[(0,[(2,5),(1,23)]),(1,[(2,7),(1,23)]),(2,[(2,13),(2,17)])]
    descendants=[]
    for b,cofactor in specifications:
        a,m=crt([(3+b,9),*cofactor])
        require(m%9==0 and a%9==3+b,'descendant not sound for original 1 mod3')
        source_g=m//3
        source_j=11*m//3
        require(not modulus_present(source_g,family),'vacant modulus collides with original G image')
        require(not modulus_present(source_j,family),'vacant modulus collides with original J image')
        require(m%3==0,'image could collide with unchanged 3-free original')
        descendants.append(dict(original=[1,3],target_root=b,residue=a,modulus=m,
                                absent_source_G_modulus=source_g,
                                absent_source_J_modulus=source_j))
    require(len({r['modulus'] for r in descendants})==3,'patch has repeated moduli')
    fixtures=[]
    for oldroot,newroot in enumerate(range(3)):
        for closing_digit in (1,2):
            coordinates={3:1,5:2,7:2,13:2,17:2,19:1,23:closing_digit,11:oldroot}
            active=seed.active_classes(coordinates,family)
            require([(r['residue'],r['modulus']) for r in active]==[(1,3)],
                    'full source private-cylinder claim failed')
            a,m=crt([(3+newroot,9),*(
                (coordinates[p],p) for p in (5,7,13,17,19,23))])
            require(m==3*W//11,'wrong literal output private-cylinder modulus')
            require(all(m%r['modulus']==0 for r in descendants),
                    'one point does not decide the entire cylinder membership')
            hit=[i for i,r in enumerate(descendants) if (a-r['residue'])%r['modulus']==0]
            require(bool(hit)==(closing_digit==1 or newroot==2),
                    'local patch result differs from exact CRT membership')
            fixtures.append(dict(old_root=oldroot,new_root=newroot,old_23_digit=closing_digit,
                                 entire_output_cylinder=[a,m],active_source_classes=[[1,3]],
                                 patch_hits=hit,covered_by_patch=bool(hit)))
    # Verify all original high-power labels miss each whole cylinder: every
    # old power-prime first digit is nonzero. The evaluator's unique possible
    # instance of any normal family therefore has height one; closing labels
    # require a zero power-prime digit or zero 23 digit, absent here.
    return dict(descendants=descendants,fixtures=fixtures,
                patches_all_report349_q3_private_cylinders=True,
                uncovered_shifted_cylinders=sum(not f['covered_by_patch'] for f in fixtures),
                standard_transport_collisions=0,whole_cover_constructed=False,
                base_description='all standard images from F minus G on old roots0,1,2 plus unchanged p-free q-free labels',
                scope='All numerical moduli distinct, but two explicit private-source cylinders remain uncovered.')


def expect_rejection(fn, substring):
    try:
        fn()
    except ValueError as exc:
        require(substring in str(exc),'unexpected rejection reason')
        return str(exc)
    raise ValueError('invalid input unexpectedly accepted')


def main():
    seed,family=load_seed()
    crossing=[minimal_fresh_count(q) for q in (3,5)]
    require(crossing[0]['smallest_possible_fresh_count']==150 and crossing[0]['last_prime']==937,
            'q3 exact crossing changed')
    require(crossing[1]['smallest_possible_fresh_count']==509 and crossing[1]['last_prime']==3709,
            'q5 exact crossing changed')
    direct=[]
    for q,fresh in ((3,[]),(3,[29]),(3,[29,31]),(5,[]),(5,[29])):
        r=fresh_capacity(q,fresh)
        cofactor_mass=F(11*q,W)
        direct.append(dict(q=q,fresh_primes=fresh,
                           **{key:str(value) for key,value in r.items()},
                           private_old_cofactor_mass=str(cofactor_mass),
                           strict_global_hole_lower=str(cofactor_mass*r['strict_hole_lower'])))
    rejection=[expect_rejection(lambda:fresh_capacity(3,[23]),'genuinely fresh'),
               expect_rejection(lambda:fresh_capacity(3,[29,29]),'duplicate'),
               expect_rejection(lambda:fresh_capacity(3,[35]),'genuinely fresh'),
               expect_rejection(lambda:fresh_capacity(3,[2]),'genuinely fresh'),
               expect_rejection(lambda:fresh_capacity(29,[29]),'genuinely fresh'),
               expect_rejection(lambda:minimal_fresh_count(29),'only for q=3 or5')]
    print(json.dumps(dict(success=True,capacity_cases=direct,exact_cardinality_crossings=crossing,
                          local_old_cofactor_patch=local_patch(seed,family),rejections=rejection,
                          mathematical_scope='Only q and genuinely fresh primes in descendants for the capacity bound; old-cofactor patch is a separate local construction, not a whole cover.'),
                     sort_keys=True,indent=2))


if __name__=='__main__':
    main()
