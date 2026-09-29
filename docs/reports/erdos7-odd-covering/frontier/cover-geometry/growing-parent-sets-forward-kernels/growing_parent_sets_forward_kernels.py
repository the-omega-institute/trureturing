#!/usr/bin/env python3
"""Exact constants for growing parent-set sizes on one normalized forward law.

The accompanying proof supplies the all-dimension and all-prime inequalities.
No original labels, heights, phases or separate tuple optima are substituted.
"""
import argparse,json
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path

def encode(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [encode(v) for v in x]
    return x

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,default=Path(__file__).with_name('unrestricted_triple_parent_forward_kernels.json'))
    ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=ap.parse_args(); checks={}
    def require(name,truth):
        if not truth: raise ArithmeticError(name)
        checks[name]=True
    raw=args.source.read_bytes(); source=json.loads(raw)
    require('inherited_checks',bool(source['checks']) and all(v is True for v in source['checks'].values()))
    fingerprint=sha256(args.source.with_suffix('.py').read_bytes()).hexdigest()
    require('inherited_producer',source['producer_sha256']==fingerprint)
    require('inherited_no_Lean_claim',source['new_lean_verification'] is False)
    gate=F(source['constants']['head_gate']); alpha=F(source['constants']['alpha'])
    oldfee=F(source['consequence']['total_owner_fee']); ordinary=F(source['consequence']['ordinary_single_head_fee'])
    require('inherited_gate_precision',gate>F(147,5000))
    require('inherited_complete_three_parent_precision',oldfee<F(531,20000))
    require('inherited_head_and_ordinary',alpha==F(2673,138320) and ordinary==F(1,65536))
    require('inherited_conditional_interface',source['constants']['conditional_density_rule']=='v/4'
            and source['constants']['reference_parents']==[3,5,7])
    ps=(3,5,7,11); cs=(F(2),F(2),F(2),F(11,4)); n0=5
    ts=tuple(1+c*(F(3,p-1)+F(2,(p-1)**2)) for p,c in zip(ps,cs))
    require('four_parent_full_factors',ts==(F(5),F(11,4),F(19,9),F(47,25)))
    def cube_values(n):
        aa=tuple(c*F(p*(p+1),(p-1)**2*p**n) for p,c in zip(ps,cs))
        bb=tuple(c*F(p,(p-1)*p**n)*(n+1+F(2,p-1)) for p,c in zip(ps,cs))
        bound=sum((aa[i]*prod(ts[j] for j in range(4) if j!=i) for i in range(4)),F())
        bound+=2*sum((bb[i]*bb[j]*prod(ts[k] for k in range(4) if k not in (i,j)) for i in range(4) for j in range(i+1,4)),F())
        exact=prod(ts)-2*prod(t-b for t,b in zip(ts,bb))+prod(t-2*b+a for t,b,a in zip(ts,bb,aa))
        return bound,exact
    four_cross_checks=[]
    for n in (5,6,7):
        bound,exact=cube_values(n)
        require(f'four_cube_{n}',0<exact<=bound and bound*3**n<74)
        four_cross_checks.append(dict(n=n,exact_moment=exact,majorant=bound,scaled_majorant=bound*3**n))
    require('four_cube_start',four_cross_checks[0]['scaled_majorant']==F(2103072391361,28533312500))
    require('four_scaled_diagonal_ratios',all(F(3,p)<=1 for p in ps))
    require('four_scaled_cross_ratios',F(3,15)*F(7,6)**2==F(49,180)<1)
    require('four_threshold',2*n0**4+3==1253)
    oddcount=(n0+1)**4-n0**4
    require('four_odd_integer_count',oddcount==4*n0**3+6*n0**2+4*n0+1==671)
    fourfee=F(74*oddcount,n0**8)*F(1,2*3**(n0-1))
    require('four_entire_prime_tail',fourfee==F(24827,31640625)<F(1,1250))
    require('four_tail_rows_preserve_future_cap',F(2*(2*n0**4+2),n0**4+1)==4<F(1253,4))
    def C(r):return 3*r*(9*r+1)*5**(r-2)
    def t(r):return F(9*r*C(r),(3*r)**(r+1)*3**(3*r))
    require('generic_cross_start',3*(1+2)**2==27)
    require('generic_cross_term_decrease',F(1,5)*F(4,3)**2==F(16,45)<1)
    require('generic_arity_ratio_bound',F(5,81)*F(46,37)*F(1,5)==F(46,2997)<F(1,60))
    require('generic_dimension_four_start',C(4)==11100 and t(4)==F(925,306110016))
    require('generic_dimension_five_start',C(5)==86250 and t(5)==F(46,1937102445))
    highfee=F(60,59)*t(5)
    require('all_higher_arities',highfee==F(184,7619269617)<F(1,10**7))
    require('all_arity_four_alternative',F(60,59)*t(4)==F(4625,1505040912)<F(1,300000))
    thresholds=[dict(arity=r,minimum_cube_n=3*r,minimum_owner=2*(3*r)**r+3,
                     moment_constant=C(r),whole_prime_fee=t(r)) for r in range(5,9)]
    require('arity_five_threshold',thresholds[0]['minimum_owner']==1518753)
    raw_good=gate-oldfee-ordinary-fourfee-highfee
    simple_raw=F(147,5000)-F(531,20000)-F(1,65536)-F(1,1250)-F(1,10**7)
    simple=alpha*simple_raw
    require('one_common_positive_budget',raw_good>simple_raw==F(10417363,5120000000)>0)
    require('full_head_projection',simple==F(27845611299,708198400000000)>F(1,26000))
    result=dict(schema='growing-parent-sets-forward-kernels-v1',
      source=dict(name=args.source.name,sha256=sha256(raw).hexdigest(),producer_sha256=fingerprint),
      scope=dict(head='Fixed reference head and precise Report617 pure-source/relational-root phase hypotheses, inherited through619',
        small_arity='Union of at most three distinct smaller parent primes: every owner>=37 uses619 rows',
        four_parents='A fixed union of four distinct smaller parents: owner>=1253; cube threshold n>=5',
        higher_arity='Fixed union of r>=5 distinct smaller parents: owner>=2(3r)^r+3; cube n>=3r',
        tuples='Several syntactic tuples allowed only within the one declared parent union; actual numerical moduli deduplicated before one row is chosen',
        source_law='One full-head law followed by normalized owner rows in numerical order, including dead fibres; uniform conditional Haar cap v/4',
        heights='Arbitrary finite original heights and arbitrary globally fixed phases at distinct numerical moduli',
        ordinary='Inherited private domains, single-head Type I branches and separate components; no undeclared crossings',
        exclusions='Unrestricted head, parent sets violating the growth thresholds, changing union by branch, numerical-label duplication, non-increasing parents, undeclared ordinary interior crossings'),
      constants=dict(alpha=alpha,gate=gate,three_parent_fee=oldfee,ordinary=ordinary),
      four_parent=dict(primes=ps,caps=cs,all_factors=ts,minimum_cube_n=5,minimum_owner=1253,
        cross_checks=four_cross_checks,moment_upper='74*3^(-n)',odd_interval_count='4n^3+6n^2+4n+1',
        whole_prime_fee=fourfee,strict_fee=F(1,1250)),
      arbitrary_arity=dict(coordinate_cap='max(2,p_i/4)',moment_constant='3r(9r+1)5^(r-2)',
        whole_prime_fee='9r*C_r/(3r)^(r+1)*3^(-3r)',ratio_upper=F(46,2997),geometric_ratio=F(1,60),
        thresholds=thresholds,entire_arity_ge5_fee=highfee,strict_fee=F(1,10**7)),
      consequence=dict(raw_good_lower=raw_good,exact_head_lower=alpha*raw_good,simple_raw_lower=simple_raw,
        simple_head_lower=simple,strict_head=F(1,26000),full_density_lower='1/(26000 Q_off)'),
      checks=checks,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),new_lean_verification=False)
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks),four_tail=fourfee,all_arity_ge5_tail=highfee,
                                simple_raw=simple_raw,simple_head=simple,strict_head=F(1,26000)))))
if __name__=='__main__':main()
