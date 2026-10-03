"""Pinned ordinary eight-prime source + direct joint-query seed + tail1400.

Re-evaluates the existing32-vertex source and exact rational budgets. No new
geometry search, source reduction, analytic-theorem proof or Lean replay.
The direct joint-query bound and averaged transport are ordinary proof
obligations supplied by the companion text, not assertions proved by this code.
"""
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec,spec_from_file_location
import json
from math import comb,factorial,prod
from pathlib import Path
import sys

P=(3,5,7,13,17,19,23,29)
T=(2,4,4,8,8,12)
PINS={
'missing11-core-certificate/missing11_core_certificate.py':'42ea72e661e643f88df57d29c280f43f74b433282d9468b9604fb7ce4f2f1484',
'finite-prefix-sources/six_prime_prefix_certificate.py':'3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4',
'finite-prefix-sources/six_prime_prefix_geometry.json':'0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1'}

def need(ok,why):
    if not ok:raise ValueError(why)

def calculate(base):
    need(not sys.flags.optimize,'Inherited pinned helper requires assertions enabled')
    sys.dont_write_bytecode=True
    for name,pin in PINS.items():need(sha256((base/name).read_bytes()).hexdigest()==pin,'pinned existing input '+name)
    path=base/'missing11-core-certificate/missing11_core_certificate.py'
    spec=spec_from_file_location('e7_source68',path)
    source=module_from_spec(spec);spec.loader.exec_module(source)
    worst,mass=source.source_mass(P[2:],T)
    caps=tuple(F(p-1,p-1-t) for p,t in zip(P[2:],T))
    need(mass==F(10237584019,168750000000)>F(91,1500),'same-source32-vertex reserve')
    need(caps==(F(3,2),F(3,2),F(4,3),F(9,5),F(11,7),F(7,4)),'later full-coordinate kernel caps')
    density=prod(caps)
    need(density==F(297,20),'retained joint pointwise density cap')
    need(len(source.helper.BATCHES)==72 and source.helper.QUERIES==51840,'inherited query accounting')
    s=(F(1,2),F(3,4))
    a=tuple(F(3*p-1,(p-1)**2) for p in P)
    factors=tuple(x+y for x,y in zip(s,a[:2]))+tuple(1+c*v for c,v in zip(caps,a[2:]))
    G=prod(factors)
    need(factors[:2]==(F(5,2),F(13,8)),'pure-anchor zero-pair credits')
    need(G==F(26010182627,1040449536)<25,'one-source complete pair-query seed')
    B,ell,degree=1400,6,4
    delta=F(1,4);tail_cap=1/(1-delta);charge_factor=1/(4*delta*(1-delta))
    need(tail_cap==F(4,3)==charge_factor,'quarter-clipped kernel and homogeneous loss constants')
    need(B>=286 and ell>=4 and 3**ell<=B and ell>F(degree,2),'prime-product applicability and decreasing integrand')
    # a(q)=3x+2x^2 at x=1/(q-1), so 1+(4/3)a(q) <= (1+x)^4.
    # All nonconstant remainder coefficients are nonnegative.
    original_coefficients=(F(1),3*tail_cap,2*tail_cap,F(0),F(0))
    difference=tuple(F(comb(degree,j))-original_coefficients[j] for j in range(degree+1))
    need(all(v>=0 for v in difference),'fourth-power moment-product majorant')
    c=F(2*ell**2+1,2*ell**2-1)
    polynomial=sum(F(factorial(degree),factorial(degree-h)*ell**h) for h in range(degree+1))
    tau=c**degree/B*F(B,B-1)**2*polynomial
    need(polynomial==F(115,54) and tau==F(2286058400500,1342865721551787),'exact degree-four all-integer tail allowance')
    charge=charge_factor*G*tau
    need(charge==F(2123599874749732432625,37424571881219517431808),'paired exact tail charge')
    remaining=mass-charge
    need(remaining==F(7170057912347323462181930867,1827371673887671749600000000000)>F(1,256),'positive final distorted mass')
    return {'scope':'Finite pairwise-distinct odd numerical moduli>1; at most eight prime divisors <=1400; at least one of 3,5,7,11 absent from LCM. Arbitrary original finite heights, residues and supports; any finite number of prime divisors>1400. General head version uses padded eight ordered primes r_i>=P_i and all nonhead primes>1400.',
      'source_primes':P,'source_thresholds':T,'source_mass_lower':mass,'simple_source_mass_strict_lower':F(91,1500),'source_worst_vertex':worst,
      'source_conditional_caps':caps,'source_joint_density_cap':density,'pure_anchor_survivor_factors':s,
      'positive_pair_depth_sums':a,'pair_query_factors':factors,'joint_query_seed_upper':G,
      'tail_cutoff':B,'ell':ell,'tail_degree':degree,'tail_clipping_threshold':delta,'tail_kernel_cap':tail_cap,'tail_charge_factor':charge_factor,'prime_product_constant':c,'integral_polynomial':polynomial,'tau4':tau,
      'tail_loss_upper':charge,
      'distorted_survivor_mass_lower':remaining,'simple_distorted_survivor_strict_lower':F(1,256),
      'dependencies':PINS,'ordinary_source_archive_sha256':'9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c',
      'inherited_basic_vertices':32,'inherited_geometry_batches':72,'inherited_integer_queries':51840,
      'geometry_search_reexecuted':False,'ordinary_source_reduction_formalized_here':False,'analytic_prime_product_verified_here':False,'joint_query_transport_proved_by_code':False,'lean_verification':False,
      'final_Haar_density_claim':'The >1/256 bound is distorted mass, not a claimed uniform final Haar density.'}

if __name__ == '__main__':
    base=Path(__file__).resolve().parent.parent
    result=json.loads(json.dumps(calculate(base),default=str))
    expected=json.loads(Path(__file__).with_suffix('.json').read_text())
    need(result==expected,'retained result agrees with exact recomputation')
    print(json.dumps(result,indent=2))
