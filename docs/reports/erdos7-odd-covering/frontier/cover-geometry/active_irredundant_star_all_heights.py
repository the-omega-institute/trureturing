"""Arbitrary finite new-prime heights in the actual irredundant star extension.

No source bank replay, optimizer, residue-period scan, or invented coupling.
Literal CRT private points check every original class. Conditional kernels
use their exact disjoint three-piece partition and clean prefix witnesses.
"""
from fractions import Fraction as F
import argparse
from hashlib import sha256
from math import prod, isqrt, lcm
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/cover-geometry/active_irredundant_star_all_heights.json'
SOURCE = 'certificates/source_norms/cover-geometry/scalar19_capacity_star_obstruction.json'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
parser.add_argument('--output', type=Path, help='Override output certificate path, for isolated staging.')
parser.add_argument('--later-height', type=int, default=8, help='Common positive finite height for new primes; default8.')
mode = parser.add_mutually_exclusive_group()
mode.add_argument('--write', action='store_true')
mode.add_argument('--check', action='store_true')
args = parser.parse_args()
if args.later_height < 1:
    parser.error('--later-height must be positive')
BASE = args.base.resolve()
OUTPUT = args.output if args.output is not None else BASE/CERTIFICATE

def require(ok, message):
    if not ok:
        raise ValueError(message)

spec = importlib.util.spec_from_file_location('active_star_io', BASE/'certificate_io.py')
require(spec is not None and spec.loader is not None, 'canonical IO')
io = importlib.util.module_from_spec(spec)
spec.loader.exec_module(io)
path = BASE/SOURCE
raw = io.read_artifact_bytes(path)
source = json.loads(raw)
source_hash = sha256(raw).hexdigest()
old_primes = (3, 5, 7, 11, 13, 17, 19)
new_primes = tuple(p for p in range(23, 102) if all(p % d for d in range(2, isqrt(p)+1)))
require(len(new_primes) == 18 and new_primes[-1] == 101, 'full 23 to 101 horizon')
heights = {p: (31 if p == 3 else 8) for p in old_primes}
heights.update({p: args.later_height for p in new_primes})
prime_powers = {p: p**h for p, h in heights.items()}
Q = prod(prime_powers.values())
crt_idempotents = {p: (Q//m)*pow(Q//m, -1, m) for p, m in prime_powers.items()}

def crt_point(coordinates):
    x = sum(coordinates[p]*crt_idempotents[p] for p in heights) % Q
    require(all(x % m == coordinates[p] % m for p, m in prime_powers.items()), 'literal CRT point')
    return x

def pair_residue(m, a, n, b):
    return (a + m*((b-a)*pow(m, -1, n) % n)) % (m*n)

classes = []
def add(kind, modulus, residue, changed):
    coords = {p: 2 for p in heights}
    coords[3] = prime_powers[3]-1
    coords.update(changed)
    witness = crt_point(coords)
    classes.append({'kind': kind, 'modulus': modulus, 'residue': residue,
                    'private_point': witness})

for p in old_primes:
    for e in range(1, heights[p]+1):
        m = p**e
        r = p**(e-1)-1
        add('old-pure', m, r, {p: r})
for p in old_primes[1:]:
    for i in range(1, 32):
        for j in range(1, 9):
            m, n = 3**i, p**j
            a, b = 2*3**(i-1)-1, 2*p**(j-1)-1
            add('old-star-mixed', m*n, pair_residue(m, a, n, b), {3: a, p: b})
for q in new_primes:
    for e in range(1, heights[q]+1):
        m = q**e
        f, c = q**(e-1)-1, 2*q**(e-1)-1
        add('new-pure', m, f, {q: f})
        add('new-active-mixed', 3*m, pair_residue(3, 1, m, c), {3: 1, q: c})
require(len(classes) == 1567+36*args.later_height, 'all old essential and both new classes at every depth')
require(len({r['modulus'] for r in classes}) == len(classes), 'all moduli distinct')
require(all(r['modulus'] > 1 and r['modulus'] % 2 for r in classes), 'all moduli odd and nontrivial')
require(lcm(*(r['modulus'] for r in classes)) == Q, 'actual full period retained')
private_checks = 0
for i, row in enumerate(classes):
    matches = []
    for j, other in enumerate(classes):
        private_checks += 1
        if row['private_point'] % other['modulus'] == other['residue']:
            matches.append(j)
    require(matches == [i], 'original class has a literal private integer')
coords = {p: 2 for p in heights}
coords[3] = 1
survivor = crt_point(coords)
require(all(survivor % r['modulus'] != r['residue'] for r in classes), 'explicit complete survivor')

# Exact Haar densities of the old star, active root band, and final family.
side = {p: sum((F(1, p**e) for e in range(1, heights[p]+1)), F(0)) for p in old_primes}
surv = {p: 1-side[p] for p in old_primes}
resid = {p: 1-2*side[p] for p in old_primes}
ra = F(1, 3**31)*prod(surv[p] for p in old_primes[1:])
rb = side[3]*prod(resid[p] for p in old_primes[1:])
old_density = ra+rb
active_density = F(1, 3)*prod(resid[p] for p in old_primes[1:])
require(0 < active_density < old_density, 'both actual old bands have positive Haar mass')
active_probability = active_density/old_density
new_side = {q: sum((F(1,q**e) for e in range(1,heights[q]+1)),F(0)) for q in new_primes}
final_density = (old_density-active_density)*prod(1-new_side[q] for q in new_primes)+active_density*prod(1-2*new_side[q] for q in new_primes)
require(0 < final_density < old_density, 'actual nonzero final survivors and genuine added deletion')

kernels = []
M = F(1)
M1 = F(1)
Minfinity = F(1)
for q in new_primes:
    h = heights[q]
    delta = F(1, q-2)
    c = new_side[q]
    Aq = sum((F(2*e+1,q**e) for e in range(1,h+1)),F(0))
    K = sum(q**(h-e) for e in range(1,h+1))
    require(c == F(K,q**h), 'exact disjoint side-cylinder count')
    require(0 < c < F(1,q-1) < F(1,2), 'complete geometric tail and positive actual survivor densities')
    forbidden = [(q**e, q**(e-1)-1, 'F') for e in range(1,h+1)]
    forbidden += [(q**e, 2*q**(e-1)-1, 'C') for e in range(1,h+1)]
    for i,(m,r,kind) in enumerate(forbidden):
        for n,s,other_kind in forbidden[i+1:]:
            require((r-s) % min(m,n) != 0, 'every actual F/C cylinder pair is disjoint')
    for t in range(1,h+1):
        require(all((2-r) % min(q**t,m) != 0 for m,r,kind in forbidden),
                'a literal clean prefix attains the cap at every current depth')
    rows=[]
    for a in (0,1):
        alpha = F(a)*c/(1-c)
        require(alpha <= delta, 'actual pure-base forbidden fraction at most chosen fixed threshold')
        theta = min(alpha,delta)
        beta = max(alpha-delta,0)/(1-delta)
        require(beta == 0, 'all actual killed charges vanish')
        # Exact compressed partition: F union, C union, and their complement.
        base_masses = (F(0), c/(1-c), (1-2*c)/(1-c))
        actual_kernel_masses = (F(0), F(0) if a else base_masses[1]/(1-theta), base_masses[2]/(1-theta))
        require(sum(base_masses) == sum(actual_kernel_masses) == 1, 'actual pure and clipped row probabilities')
        density = 1/((1-c)*(1-theta))
        require(density == 1/(1-c-a*c), 'exact good-row density against full Haar')
        caps=[]
        for t in range(1,h+1):
            cap = F(1,q**t)*density
            require(cap == F(1,q**t)*(1/(1-c)+F(a)*c/((1-c)*(1-2*c))), 'bandwise exact cap decomposition')
            caps.append(str(cap))
        rows.append({'active_band':a,'actual_mixed_fraction':str(alpha),'delta':str(delta),'beta':str(beta),
                     'actual_kernel_masses_F_C_rest':list(map(str,actual_kernel_masses)),
                     'good_Haar_density':str(density),'depth_prefix_maxima':caps})
    finite_factor = 1+Aq/(1-2*c)
    full_factor = 1+F(3*q-1,(q-1)*(q-3))
    require(1+F(3,q-2) <= finite_factor < full_factor, 'H1 through finite H through full-height moment factors')
    # Exact H=1 reduction of both band coefficients and resulting physical kernel.
    c1=F(1,q); A1=F(3,q)
    require(A1/(1-c1) == F(3,q-1), 'old H1 unweighted coefficient')
    require(A1*c1/((1-c1)*(1-2*c1)) == F(3,(q-1)*(q-2)), 'old H1 active-band coefficient')
    for a in (0,1):
        alpha1=F(a,q-1)
        require(min(alpha1,F(1,q-1)) == min(alpha1,delta), 'old and new H1 thresholds give exactly the same kernel')
    M *= finite_factor
    M1 *= 1+F(3,q-2)
    Minfinity *= full_factor
    kernels.append({'prime':q,'height':h,'side_Haar_mass':str(c),'square_transfer_A':str(Aq),
                    'rows':rows,'unweighted_growth_coefficient':str(Aq/(1-c)),
                    'active_band_growth_coefficient':str(Aq*c/((1-c)*(1-2*c))),
                    'moment_multiplier_upper':str(finite_factor),'all_height_multiplier_upper':str(full_factor),
                    'positive_original_mixed_union_probability':str(active_probability*c/(1-c))})
require(M1 <= M < Minfinity, 'whole-horizon factors compare in the correct direction')

# Reuse304 inverse-capacity algebra on NEW finite-height coefficients only.
# No old full-height capacities or old potential rows are recomputed.
GRID=10**45

def radical_interval(x):
    n=isqrt(x.numerator*GRID*GRID//x.denominator)
    lo,hi=F(n,GRID),F(n+1,GRID)
    require(lo*lo<=x<hi*hi,'direct positive integer-square radical enclosure')
    return lo,hi

def finite_capacity(q,H,required):
    a=sum((F(2*e+1,q**e) for e in range(1,H+1)),F(0))
    s=sum((F(1,q**e) for e in range(1,H+1)),F(0))
    b=s*s/4
    lo,hi=radical_interval(required*b*(a+required*b))
    return required/(1+a+2*required*b+2*hi),required/(1+a+2*required*b+2*lo)

def rounded(lo,hi):
    return F(lo.numerator*GRID//lo.denominator,GRID), F(-((-hi.numerator*GRID)//hi.denominator),GRID)

def finite_horizon_capacity(H):
    q=new_primes[-1]
    s=sum((F(1,q**e) for e in range(1,H+1)),F(0))
    lo=hi=1/(s*s)
    rows=[]
    for q in reversed(new_primes[:-1]):
        lo2=finite_capacity(q,H,lo)[0]
        hi2=finite_capacity(q,H,hi)[1]
        lo,hi=rounded(lo2,hi2)
        rows.append({'prime':q,'input_capacity_lower':str(lo),'input_capacity_upper':str(hi)})
    require(0<lo<hi and hi-lo<F(1,10**35),'strict finite-height capacity enclosure')
    return {'common_height':H,'capacity_lower':str(lo),'capacity_upper':str(hi),'backward_rows':rows}
finite_capacity_data=finite_horizon_capacity(args.later_height)
height1_capacity_data=finite_horizon_capacity(1)

star = source['actual_star']
require(tuple(star['head_primes']) == old_primes and star['height3'] == 31 and star['other_heights'] == 8, 'same old actual star')
L = F(star['uniform_gamma_lower'])
cap_row = next(r for r in source['rows'] if r['through_prime'] == 101)
capacity_upper = F(cap_row['seed_capacity_upper'])
require(L > capacity_upper, 'same T6 obstruction survives all irredundancy and activity requirements')
require(capacity_upper < F(53112508688515, 10**12), 'displayed strict capacity upper')
finite_capacity_upper=F(finite_capacity_data['capacity_upper'])
require(Minfinity < F(3097096558845,10**12), 'displayed complete-height multiplier upper')
if args.later_height == 8:
    require(finite_capacity_upper < F(53112508689463,10**12), 'displayed height8 finite-capacity upper')
require(F(height1_capacity_data['capacity_lower']) > L, 'height1 finite-capacity lower exceeds the retained star lower')
if args.later_height >= 8:
    require(finite_capacity_upper < L, 'even actual finite-height T6 coefficients remain obstructed at height8 and above')

out = {'schema': 'active-irredundant-star-all-heights-v1',
       'source_sha256': {SOURCE: source_hash},
       'old_primes': list(old_primes), 'new_primes': list(new_primes),
       'height_by_prime': {str(p): h for p,h in heights.items()},
       'literal_period': Q, 'original_class_count': len(classes),
       'private_membership_checks': private_checks, 'original_classes': classes,
       'explicit_survivor': survivor,
       'old_haar_survivor_density': str(old_density), 'old_active_band_haar_density': str(active_density),
       'uniform_old_active_band_probability': str(active_probability),
       'final_haar_survivor_density': str(final_density),
       'actual_kernels': kernels, 'whole_horizon_gamma_multiplier_upper': str(M),
       'height1_whole_horizon_gamma_multiplier':str(M1),
       'all_height_whole_horizon_gamma_multiplier_upper':str(Minfinity),
       'actual_finite_height_T6_capacity':finite_capacity_data,
       'height1_T6_capacity':height1_capacity_data,
       'retained_gamma19_lower': str(L), 'T6_through101_capacity_upper': str(capacity_upper),
       'strict_obstruction_gap': str(L-capacity_upper),
       'actual_finite_height_T6_obstruction_gap':str(L-finite_capacity_upper),
       'scope': 'All original forbidden classes have private integers; every new mixed block is genuinely effective on the actual old survivor set. The old seven-prime lower exceeds the T6 capacity for every supported old marginal, but actual family-aware kernels give zero killed charges through101 at arbitrary finite new-prime heights. At height8 even the finite-height T6 coefficients are obstructed. No uniform arbitrary-family improvement, no covering counterexample, no Lean claim.'}
if args.write:
    io.write_certificate_text(OUTPUT, json.dumps(out, indent=2)+'\n')
require(json.loads(io.read_artifact_bytes(OUTPUT)) == out, 'exact canonical output certificate')
print('PASS: actual classes', len(classes), 'literal private-membership checks', private_checks)
print('Old Gamma lower', float(L), 'T6 through101 capacity upper', float(capacity_upper))
print('Old active band probability', float(active_probability), 'finite horizon Gamma multiplier upper', float(M))
print('Full-height horizon multiplier upper',float(Minfinity), 'height1 multiplier',float(M1))
print('New finite-height T6 capacity upper',float(finite_capacity_upper), 'height1 capacity upper',float(F(height1_capacity_data['capacity_upper'])))
print('Final Haar survivor density', float(final_density), 'all18 physical and killed kernels normalized with zero charge')
