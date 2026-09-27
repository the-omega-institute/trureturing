#!/usr/bin/env python3
"""Exact same-source head release and fixed-row three-parent coefficients.

Pins the existing651 head interface and657 actual row certificate. The
mathematical source/phase, branch and infinite-tail bridges are stated in658.
No producer module is imported, no row is reoptimized, and no Lean result
is claimed. Only exact fractions and directed integer intervals certify bounds.
"""
from fractions import Fraction as F
from itertools import combinations
from math import comb, factorial, isqrt, prod
from pathlib import Path
import argparse
import hashlib
import json

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
checks = {}


def ck(name, condition):
    if not condition:
        raise ArithmeticError(name)
    checks[name] = checks.get(name, 0) + 1


def ceildiv(n, d):
    return -(-n // d)


def read_pin(name, expected):
    raw = (args.directory / name).read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    ck('source_hash_pin', digest == expected)
    data = json.loads(raw)
    ck('source_status', data['status'] == 'PASS')
    return data, digest


head, head_hash = read_pin(
    'unqueried_head_four_parent_certificate.json',
    '8bf5da7b70697b67e5f3df8b2787cbcac087841342423d028372ba4ebe903d2f')
policy, policy_hash = read_pin(
    'ordinary_domain_five_parent_certificate.json',
    'e46183469f280d262da37a9c33005e724690fc20b0106202c42c9913ed8d8ec0')
gamma = F(head['head_gate'])
alpha = F(head['projection_alpha'])
g = F(200163067, 201247200)
ck('head_gate', gamma == F(203129722400814193208791597,
                          20692505911553620784640000000))
ck('same_head_gate', F(policy['head_gate']) == gamma)
ck('same_projection', F(policy['projection_alpha']) == alpha == F(2673, 110656))
Q = (7, 11, 13, 17, 19)
r = {q: F(1, q-1) for q in Q}
a = {q: F(1, q*(q-2)) for q in Q}
D = {q: F(q-2, q-1) - (0 if q == 7 else 2*a[q]) for q in Q}
beta = {(q, s): a[q]*r[s]+r[q]*a[s] for q, s in combinations(Q, 2)}
ck('omitted_mass_source', all(F(head['unqueried_coordinate_mass_caps'][str(q)]) == D[q] for q in Q))


def induced(U, masses):
    return prod(masses[q] for q in U) - sum(
        beta[(q, s)] * prod(masses[p] for p in U if p not in (q, s))
        for q, s in combinations(U, 2))


minimum_masses = dict(D)
minimum_masses[7] = F(157, 210)
lambda_min = 1 - sum(beta[(q, s)]/(minimum_masses[q]*minimum_masses[s])
                     for q, s in combinations(Q, 2))
ck('uniform_induced_positivity', lambda_min == F(328686693796069, 337134711943765) > 0)
responses = {}
for mask in range(32):
    U = tuple(q for i, q in enumerate(Q) if not mask >> i & 1)
    low, up = induced(U, minimum_masses), induced(U, D)
    ck('induced_response_box', 0 < low <= up <= prod(D[q] for q in U))
    responses[mask] = up
charges = []
for i, q in enumerate(Q):
    bound = F(8, 675)*r[q]*responses[1 << i]
    charges.append(dict(modulus=225*q, owner=q, central_leaf_cap='8/675',
                        outside_root_cap=str(r[q]), induced_response=str(responses[1 << i]),
                        actual_event_mass_upper=str(bound), gate_debit_upper=str(g*bound)))
ck('released_numerical_inventory', [row['modulus'] for row in charges] == [1575, 2475, 2925, 3825, 4275])
debit = sum((F(row['gate_debit_upper']) for row in charges), F())
joint_gate = gamma-debit
ck('joint_gate', joint_gate == F(129051308183692805303085853,
                               20692505911553620784640000000) > 0)

# Keep the193 actual h values and global caps from657, without optimization.
inherited = policy['finite_rows']
primes = [p for p in range(37, 1253) if all(p % d for d in range(2, isqrt(p)+1))]
ck('complete_finite_owner_inventory', len(inherited) == 193 and [row['owner'] for row in inherited] == primes)
ck('finite_endpoint', policy['finite_endpoint'] == 1253)
ck('unchanged_tail_row', policy['tail_row_rule'] == 'unchanged655 relative half-threshold N=0')
S = 10**75
TMAX = max(ceildiv(F(row['t']).numerator, F(row['t']).denominator) for row in inherited)
K1 = {3: F(2, 3), 5: F(4, 15), 7: F(1, 6)}
DEEP = {3: F(2), 5: F(4, 3), 7: F(7, 5)}
atoms = {}
for p in K1:
    low, high = [0]*(TMAX+1), [0]*(TMAX+1)
    first = (1-K1[p], K1[p]-DEEP[p]/p**2)
    for j, probability in enumerate(first, 1):
        low[j] = probability.numerator*S//probability.denominator
        high[j] = ceildiv(probability.numerator*S, probability.denominator)
    ppow = p**3
    for j in range(3, TMAX+1):
        n, d = DEEP[p].numerator*(p-1), DEEP[p].denominator*ppow
        low[j], high[j] = n*S//d, ceildiv(n*S, d)
        ppow *= p
    atoms[p] = low, high
low, high = [0, S]+[0]*(TMAX-1), [0, S]+[0]*(TMAX-1)
for p in (3, 5, 7):
    alo, ahi = atoms[p]
    nlo, nhi = [0]*(TMAX+1), [0]*(TMAX+1)
    for i in range(1, TMAX+1):
        for j in range(1, TMAX//i+1):
            nlo[i*j] += low[i]*alo[j]
            nhi[i*j] += high[i]*ahi[j]
    for i in range(1, TMAX+1):
        nlo[i] //= S
        nhi[i] = ceildiv(nhi[i], S)
        ck('product_distribution_interval', 0 <= nlo[i] <= nhi[i])
    low, high = nlo, nhi
mean = prod(1+K1[p]+DEEP[p]/(p*(p-1)) for p in K1)-1
ck('complete_three_role_mean', mean == F(11, 5))
zeta = prod(D[q] for q in (11, 13, 17, 19))
hl, hu = [], []
pl = pu = ml = mu = 0
for t in range(TMAX+1):
    if t:
        pl += low[t]
        pu += high[t]
        ml += t*low[t]
        mu += t*high[t]
    lower = mean-t+F((t+1)*pl-ml, S)
    upper = mean-t+F((t+1)*pu-mu, S)
    ck('complete_integer_hinge_interval', 0 <= lower <= upper)
    hl.append(lower)
    hu.append(upper)
rows = []
for inherited_row in inherited:
    v, h = inherited_row['owner'], inherited_row['h']
    domain = F(v-2)-F(1, 65536)
    t, cap = domain-h, F(v-1, h)
    ck('unchanged_actual_row', inherited_row['N'] == 0 and F(inherited_row['D']) == domain
       and F(inherited_row['t']) == t and F(inherited_row['cap']) == cap)
    ck('actual_cap_capacity', 10 <= h < domain and cap < F(v, 10) and cap*domain/(v-1) > 1)
    n = t.numerator//t.denominator
    u = t-n
    ck('rational_interpolation_position', u == 1-F(1, 65536) and n+1 <= TMAX)
    feelo = zeta*((1-u)*hl[n]+u*hl[n+1])/h
    feehi = zeta*((1-u)*hu[n]+u*hu[n+1])/h
    ck('three_role_row_fee_interval', 0 <= feelo <= feehi and feehi-feelo < F(1, 10**60))
    rows.append(dict(owner=v, r=3, h=h, D=str(domain), t=str(t), N=0, cap=str(cap),
                     fee_lower=str(feelo), fee_upper=str(feehi)))
finite_low = sum((F(row['fee_lower']) for row in rows), F())
finite_up = sum((F(row['fee_upper']) for row in rows), F())

# Recompute the existing generic-five half-row tail; it also bounds three parents.
gp = (3, 5, 7, 11, 13)
gk = tuple(map(F, ('2/3', '4/15', '1/6', '1/10', '1/10')))
gd = tuple(map(F, ('2', '4/3', '7/5', '11/9', '13/10')))


def moments(p, k, d):
    q = F(1, p)
    geom = [1/(1-q)]
    for j in range(1, 8):
        geom.append(q/(1-q)*sum(comb(j, i)*geom[i] for i in range(j)))
    result = [F(1)]
    for j in range(1, 8):
        delta = 2**j-1
        result.append(1+k*delta+d*(sum(comb(j, i)*geom[i] for i in range(j))-1-q*delta))
    return result


XM = [moments(p, k, d) for p, k, d in zip(gp, gk, gd)]
M7 = sum((-1)**(7-j)*comb(7, j)*prod(m[j] for m in XM) for j in range(8))
A7 = F(2**7*6**6, 7**7)
five_tail = A7*M7/(6*1249**6)
ck('same_complete_tail_moment', M7 == F(policy['complete_fifth_role_count_moment7']))
ck('same_complete_halfrow_tail', five_tail == F(policy['complete_five_parent_tail']))

# The cap table is identical, hence reconstruct the same directed Euler bound.
headcaps = dict(zip((3, 5, 7, 11, 13, 17, 19, 23, 29, 31),
                   map(F, ('2', '4/3', '7/5', '11/9', '13/11', '17/15', '19/17', '5/3', '20/11', '2'))))
finitecaps = {row['owner']: F(row['cap']) for row in rows}
B0, scale = 2187, 2**160
mlo = mhi = plo = phi = scale
counts = dict(head=0, finite=0, half=0)
for p in range(3, B0+1, 2):
    if not all(p % d for d in range(2, isqrt(p)+1)):
        continue
    if p in headcaps:
        cap = headcaps[p]
        counts['head'] += 1
    elif p in finitecaps:
        cap = finitecaps[p]
        counts['finite'] += 1
    else:
        cap = F(2*(p-1), p-3)
        counts['half'] += 1
        ck('actual_tail_cap', cap < F(p, 10))
    term = 1+cap*(F(3, p-1)+F(2, (p-1)**2))
    mlo = mlo*term.numerator//term.denominator
    mhi = ceildiv(mhi*term.numerator, term.denominator)
    plo = plo*p//(p-1)
    phi = ceildiv(phi*p, p-1)
ck('same_Euler_counts', counts == policy['Euler_counts'] == dict(head=10, finite=193, half=123))
Mlo, Mhi, Plo, Phi = (F(x, scale) for x in (mlo, mhi, plo, phi))
for name, value in (('M0_lower', Mlo), ('M0_upper', Mhi), ('Podd_lower', Plo), ('Podd_upper', Phi)):
    ck('same_Euler_interval', value == F(policy[name]))
Ctail = F(B0, B0-1)
typeI = F(1, 65536)
base = finite_up+five_tail+typeI
policies = []
for kind, K in (('RS', 46), ('elementary', 68)):
    V = 2**K
    if kind == 'RS':
        polynomial = sum(F(factorial(6), factorial(6-j))*F(7*K, 10)**(6-j) for j in range(7))
        fee = Mhi*Ctail*F(99, 97)**6*F(V, V-3)**2*polynomial/(2*(V-1)*F(1841, 240)**6)
    else:
        ratio = F(1, 2)*F(K+3, K+2)**6
        ck('elementary_geometric_ratio', ratio < 1)
        fee = 2*(Mhi*Ctail/Plo**6)*(4*(K+2))**6/F(2**K)/(1-ratio)
    ck('same_complete_arbitrary_tail', fee == F(policy[kind+'_policy']['fee']))
    raw = joint_gate-base-fee
    projected = alpha*raw
    ck('complete_joint_release_budget', projected > F(1, 10000))
    policies.append(dict(kind=kind, K=K, arbitrary_threshold=V, max_parents_below_switch=3,
                         fee=str(fee), raw_margin=str(raw), projected_margin=str(projected),
                         density_denominator=10000))
out = dict(schema='joint-square-pair-225-star-v1', status='PASS', new_lean_verification=False,
           scope='One head with55 incidences; all15 square stars, all20 square pairs and all5 deep225 stars free; three-parent rows below fixed RS46/elementary68 switch; arbitrary finite parents thereafter',
           producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           source651_sha256=head_hash, source657_sha256=policy_hash,
           head_gate_before_release=str(gamma), g=str(g), projection_alpha=str(alpha),
           head_root_incidence_counts=dict(linear_stars=35, pairs=20),
           coordinate_mass_upper={str(q): str(D[q]) for q in Q},
           uniform_induced_retention_lower=str(lambda_min),
           induced_response_upper={str(mask): str(value) for mask, value in responses.items()},
           released225_originals=charges, complete_release_gate_debit=str(debit),
           head_gate=str(joint_gate), finite_row_parameters_reoptimized=False,
           finite_endpoint=1253, finite_row_rule='inherited657 actual-domain full-Haar cap calibration',
           tail_row_rule='unchanged655 relative half-threshold N=0',
           scale=str(S), threshold_max=TMAX,
           branch_parameters=dict(parents=[3, 5, 7], factor=str(zeta), exact_EC=str(mean)),
           finite_rows=rows, finite_fee_lower=str(finite_low), finite_fee_upper=str(finite_up),
           coordinate_moments=[list(map(str, m)) for m in XM],
           complete_generic_five_role_moment7=str(M7), sharp_halfrow_constant7=str(A7),
           complete_five_parent_tail=str(five_tail), ordinary_typeI_fee=str(typeI),
           Euler_endpoint=B0, Euler_scale=str(scale), Euler_counts=counts,
           M0_lower=str(Mlo), M0_upper=str(Mhi), Podd_lower=str(Plo), Podd_upper=str(Phi),
           Ctail=str(Ctail), fee_before_arbitrary=str(base), policies=policies,
           checks=checks, check_count=sum(checks.values()))
args.output.write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(dict(status=out['status'], check_count=out['check_count'],
                     head_gate=float(joint_gate), finite_fee=float(finite_up),
                     same657_caps=True, policies=[dict(kind=p['kind'], raw=float(F(p['raw_margin'])),
                                                       projected=float(F(p['projected_margin'])),
                                                       density_denominator=p['density_denominator']) for p in policies]), indent=2))
