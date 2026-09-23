"""Exact genuine three-point selector obstruction beyond all pair exclusions.
Report494: all-subset inventories and a positive fibre-sum bound.

Standard library only.  It constructs the literal original-cofactor boxes,
all subset capacities, the two complete rational vertex sets, feasible zero
witnesses for each pair, and positive auxiliary chart weights.  No search
history, pair-graph input, source independence, or actual-cover claim.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
from math import prod

PROFILES = ((2,2,-2,2,1,2,1), (2,2,-2,1,2,2,1), (2,-2,0,2,2,2,1))
INDICES = (108,98,931)
EXPECTED = (20,20,40,24,40,40,58)
ANCHORS = ((3,0),(5,0),(9,1),(15,2),(25,1),(27,4))
CAPS = ((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))

def need(test, message):
    if not test:
        raise ValueError(message)

ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir',type=Path,default=ROOT)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
source_inputs={
 'mixed_split_pair_support_certificate.json':'21835ce8429c77ff3a0debe4e3cfd9d85e807f78abf2dce54ecf9892e65cc449',
 'common_law_mass_tail.json':'3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4'}
source_data={}
for name,digest in source_inputs.items():
    raw=(args.input_dir/name).read_bytes()
    need(hashlib.sha256(raw).hexdigest()==digest,'source identity '+name)
    source_data[name]=json.loads(raw)
source=source_data['common_law_mass_tail.json']['common_seven_core_law']
need(tuple(map(F,source['conditional_caps']))==tuple(c for p,c in CAPS),'same comparison caps')
cert=source_data['mixed_split_pair_support_certificate.json']
need(cert['reference']==[2,7,3,4] and cert['split_later_primes']==[7],'fixed comparison scope')
# Reconstruct the certificate index order, instead of trusting its labels.
def profile_load(s):
    return (prod(max(1,v) for v in s[:3])+prod(max(1,-v) for v in s[:3])-1)*prod(s[3:])
all_profiles=[]
def complete_profile(s):
    if len(s)==7:
        all_profiles.append(s);return
    for f in range(1,39):
        child=s+(f,)
        if profile_load(child)>38:break
        complete_profile(child)
signed_factors=list(range(2,39))+list(range(-2,-39,-1))
for a,b,c in product(signed_factors,signed_factors+[0],[0]+signed_factors):
    if profile_load((a,b,c))<=38:complete_profile((a,b,c))
profile_rows=[s for s in all_profiles if profile_load(s)>=20]
need(len(profile_rows)==20076,'full middle profile order')
need(all(profile_rows[i]==s and i in cert['indices'] for i,s in zip(INDICES,PROFILES)),
     'all three profiles belong to the prior pair-admissible support')

def boxes(s):
    a = tuple(max(1,v) for v in s[:3]) + s[3:]
    b = tuple(max(1,-v) for v in s[:3]) + s[3:]
    return set(product(*(range(v) for v in a))), set(product(*(range(v) for v in b)))

inventory = [boxes(s) for s in PROFILES]
labels = set().union(*(a|b for a,b in inventory))
patterns = Counter((sum((d in a)<<i for i,(a,b) in enumerate(inventory)),
                    sum((d in b)<<i for i,(a,b) in enumerate(inventory))) for d in labels)
capacity = tuple(sum(n*max((a&m).bit_count(),(b&m).bit_count())
                     for (a,b),n in patterns.items()) for m in range(1,8))
need(capacity == EXPECTED, 'literal seven subset inventories')

A = [tuple((m>>i)&1 for i in range(3)) for m in range(1,8)]
A += [tuple(-int(i==j) for i in range(3)) for j in range(3)]

def solve(rows, rhs):
    """Rational Gauss-Jordan elimination, returning None for singular bases."""
    a = [[F(v) for v in row]+[F(r)] for row,r in zip(rows,rhs)]
    for col in range(3):
        pivot = next((j for j in range(col,3) if a[j][col]),None)
        if pivot is None:
            return None
        a[col],a[pivot] = a[pivot],a[col]
        c = a[col][col]
        a[col] = [v/c for v in a[col]]
        for j in range(3):
            if j != col:
                c = a[j][col]
                a[j] = [v-c*w for v,w in zip(a[j],a[col])]
    return tuple(a[i][-1] for i in range(3))

def vertices(axis):
    rhs = list(capacity)+[0,0,0]
    for mask in (1,2,4):
        rhs[mask-1] = min(rhs[mask-1],axis)
    found = set()
    nonsingular = 0
    for basis in combinations(range(10),3):
        v = solve([A[i] for i in basis],[rhs[i] for i in basis])
        if v is None:
            continue
        nonsingular += 1
        if all(sum(c*x for c,x in zip(row,v)) <= b for row,b in zip(A,rhs)):
            found.add(v)
    need(nonsingular == 78,'all nonsingular bases')
    return sorted(found)

V,W = vertices(22),vertices(28)
need(V and W,'nonempty complete vertex sets')
table = [[sum((22-t)*(28-u) for t,u in zip(v,w))-capacity[-1] for w in W] for v in V]
minimum = min(map(min,table))
need(minimum == 6,'exact positive three-point numerator')
arg = next((i,j) for i,row in enumerate(table) for j,value in enumerate(row) if value==minimum)

# Each two-point restriction has a valid zero-survivor relaxed budget.
# These witnesses need not and, by the three-point result, cannot glue.
pair_witnesses = []
for pair,t,u in (((0,1),(20,20),(20,20)),
                 ((0,2),(20,20),(18,22)),
                 ((1,2),(20,20),(18,22))):
    qs = [capacity[(1<<i)-1] for i in pair]
    n = capacity[sum(1<<i for i in pair)-1]
    c = [(22-x)*(28-y) for x,y in zip(t,u)]
    need(all(0<=x<=min(22,q) for x,q in zip(t,qs)) and sum(t)<=n,'pair axis23')
    need(all(0<=x<=min(28,q) for x,q in zip(u,qs)) and sum(u)<=n,'pair axis29')
    need(all(0<=x<=q for x,q in zip(c,qs)) and sum(c)<=n,'pair mixed zero witness')
    pair_witnesses.append({'points':list(pair),'Q':qs,'N':n,'axis23':list(t),
                           'axis29':list(u),'mixed_deletion':c})

def shell_conditional(p,E,residue,reference,f):
    if residue == reference:
        return F((p-1)*p**E,p**f) if f>E else F()
    d,v = residue-reference,0
    while d%p==0:
        d//=p
        v+=1
    return F(v+1==f)

def initial_cell(n,s):
    x,y = n%27,n%25
    if (x%3==2) != (s[0]>0):
        return F()
    w = shell_conditional(3,3,x,2 if s[0]>0 else 7,abs(s[0]))
    if s[1]==0:
        return w if y%5 not in (3,4) else F()
    if y%5 != (3 if s[1]>0 else 4):
        return F()
    return w*shell_conditional(5,2,y,3 if s[1]>0 else 4,abs(s[1]))

cells = [n for n in range(675) if all(n%m!=a for m,a in ANCHORS)]
need(len(cells)==221,'six-anchor joint chart')
weights = []
for s in PROFILES:
    later = F(1)
    for j,((p,C),f) in enumerate(zip(CAPS,s[2:])):
        baseline = f==(0 if j==0 else 1)
        later *= 1-(2 if j==0 else 1)*C/p if baseline else C*F(p-1,p**abs(f))
    contributions = [(n,initial_cell(n,s)/675) for n in cells if initial_cell(n,s)]
    six = sum((w for n,w in contributions),F())
    eight = sum((w for n,w in contributions if n%45!=31 and n%75!=16),F())
    need(six>0 and eight>0 and later>0,'strict positive auxiliary profile masses')
    weights.append({'profile':list(s),'six_anchor_initial_mass':str(six),
                    'eight_anchor_initial_mass':str(eight),'later_comparison_mass':str(later),
                    'six_anchor_profile_mass':str(six*later),'eight_anchor_profile_mass':str(eight*later),
                    'positive_six_anchor_cells':len(contributions),
                    'positive_eight_anchor_cells':sum(n%45!=31 and n%75!=16 for n,w in contributions),
                    'sample_cell':next(n for n,w in contributions if n%45!=31 and n%75!=16)})

out = {
    'verified':True,
    'source_inputs':source_inputs,
    'support_pair_audit_rerun':False,
    'Lean_rerun':False,
    'scope':'Fixed two global centres, first-root split at3,5,7 and common at11,13,17,19; one selector per original full numerical label.',
    'profile_schema':['signed3','signed5','signed7','common11','common13','common17','common19'],
    'profiles':[list(s) for s in PROFILES],
    'indices_in_fixed_20076_profile_order':list(INDICES),
    'capacities_by_nonempty_bitmask':list(capacity),
    'literal_label_count':len(labels),
    'membership_pattern_histogram':[[a,b,n] for (a,b),n in sorted(patterns.items())],
    'axis23_vertices':[[str(v) for v in row] for row in V],
    'axis29_vertices':[[str(v) for v in row] for row in W],
    'axis23_vertex_row_minima':[str(min(row)) for row in table],
    'nonsingular_bases_per_polytope':78,
    'vertex_pairs_checked':len(V)*len(W),
    'minimum_numerator':str(minimum),
    'minimizing_axis23':[str(v) for v in V[arg[0]]],
    'minimizing_axis29':[str(v) for v in W[arg[1]]],
    'survivor_sum_lower_bound':str(minimum/616),
    'all_three_strictly_below_threshold_impossible_for':'0 < theta <= 1/308',
    'old_pair_threshold':'1/3696',
    'pair_zero_witnesses':pair_witnesses,
    'auxiliary_chart_reference':[2,7,3,4],
    'eight_anchor_extra_phases':{'45':31,'75':16},
    'positive_auxiliary_profile_masses':weights,
    'evidence_boundary':'Exact standard-library arithmetic and ordinary proof, not Lean. Positive auxiliary chart weights do not assert positive mass in the completed actual source or simultaneous realizability as its low-survivor set. No source replacement and no new centre choices per point.'
}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({'minimum_numerator':str(minimum),'survivor_sum_lower_bound':str(minimum/616),
                  'vertices':[len(V),len(W)],'positive_auxiliary_profile_masses':weights},indent=2))
