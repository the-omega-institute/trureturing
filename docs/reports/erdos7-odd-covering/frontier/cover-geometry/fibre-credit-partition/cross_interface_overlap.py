"""Exact cross-interface condition and same-source phase separation.

Uses existing endpoint enclosures without rerunning their old checker.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',required=True)
ap.add_argument('--endpoint',required=True)
ap.add_argument('--output',required=True)
args=ap.parse_args()
raw=Path(args.input).read_bytes()
data=json.loads(raw)
endpoint_raw=Path(args.endpoint).read_bytes()
ep=json.loads(endpoint_raw)
Q=data['primes']
h=dict(zip(Q,data['heights']))
assignment=dict(data['selected_witness'])
for d in ep['flipped_cofactors']:
    assignment[d]=1
c={q:F((q-1)*q**h[q],(q-2)*q**h[q]+1) for q in Q}
b={q:c[q]-1 for q in Q}
checks=0
def need(ok,message):
    global checks
    checks+=1
    if not ok:
        raise ValueError(message)
need(ep['input_sha256']==sha256(raw).hexdigest(),'Bind inherited endpoint to this exact inventory input')
need(set(ep['flipped_cofactors'])=={77,91,119,133},'Existing four-flip input')
need(35 in assignment and 77 in assignment and assignment[77]==1,'Required numerical labels present')
need(all(t==(1 if q==5 else 2) for q,e,t in data['star_roots']),'Same active stars on root1')
Elo=F(ep['both_group_root1_lower'])
Ehi=F(ep['both_group_root1_upper'])
eps_uniform=F(1,385)
gain=Elo+eps_uniform
need(gain>F(1,750),'Clean compatible cylinders cross the existing negative gap')
need(1-c[5]/5>=b[5],'One can enlarge5 blockers outside the clean5 cylinder')
C=F(3)
for q in Q:
    C*=c[q]
need(C<8 and gain/C>F(1,6000),'Same-source mass converts to positive actual density')

def cylinder_overlap(q,e,a,f,z):
    return F(1,q**max(e,f)) if (a-z)%q**min(e,f)==0 else F(0)
def pure(q):
    return [(e,0 if e==1 else 1+q**(e-1)) for e in range(1,h[q]+1)]
def holes(q):
    return pure(q)+([(e,2 if e==1 else 3+q**(e-1)) for e in range(1,h[q]+1)] if q==5 else [])
def mass(q,e,a):
    return c[q]*(F(1,q**e)-sum((cylinder_overlap(q,e,a,f,z) for f,z in holes(q)),F(0)))
for q in Q:
    all_source_holes=pure(q)+[(e,2 if e==1 else 3+q**(e-1)) for e in range(1,h[q]+1)]
    for (e,a),(f,z) in combinations(all_source_holes,2):
        need(cylinder_overlap(q,e,a,f,z)==0,'Actual source holes are disjoint')
    need(c[q]*(1-sum((F(1,q**e) for e in range(1,h[q]+1)),F(0)))==1,
         'Actual disjoint pure union gives exactly the declared normalizer')
for q in (5,7,11):
    need(mass(q,1,4)==c[q]/q,'Literal4 row is full in the same source')
need(mass(7,1,5)==mass(7,1,4),'Move between equal-mass7 rows')
carrier=1-b[5]
m35=mass(5,1,4)*mass(7,1,4)
m77=carrier*mass(7,1,4)*mass(11,1,4)
eps_actual=mass(5,1,4)*mass(7,1,4)*mass(11,1,4)
need(eps_actual==F(1997331875,432601753328),'Exact common-source overlap')
need(4%7!=26%7 and 4%11==26%11,'4 mod77 and26 mod77 differ only at7')
need(26%7==5 and 4%35==4,'Literal CRT phase pair')
need((4-26)%7!=0,'Incompatible common7 coordinate gives zero overlap')

# Every other free/selected mixed original can be put inside a pure
# first-coordinate hole. This keeps the complete numerical roster,
# selected roots and all source metadata identical in the two models.
roster=[]
for d,t in sorted(assignment.items()):
    need(d>1,'Positive mixed label')
    p=next(q for q in Q if d%q==0)
    free_same=4 if d in (35,77) else 0
    free_separate=26 if d==77 else free_same
    # Residue0 mod d makes every supported coordinate zero and hence
    # lies inside a pure first-prime hole. Lift0 mod d to ternary root t.
    selected=d*((t*pow(d,-1,3))%3)
    need(selected%d==0 and selected%3==t,'Complete selected phases keep their assigned ternary root')
    if d not in (35,77):
        need(free_same%p==0,'Inactive free mixed original lies in a pure hole')
    need(selected%p==0,'Inactive selected mixed original lies in a pure hole')
    roster.append((d,free_same,free_separate,3*d,selected,t))
need(len({m for d,a,z,m,r,t in roster})==2138,'All original selected moduli retained')
need(len({d for d,a,z,m,r,t in roster})==2138,'All matching free numerical moduli retained')
source_moduli=[3]+[n for q in Q for e in range(1,h[q]+1) for n in (q**e,3*q**e)]
all_moduli=source_moduli+[n for d,a,z,m,r,t in roster for n in (d,m)]
need(len(source_moduli)==85 and len(all_moduli)==4361,'Full original source and mixed roster count')
need(len(set(all_moduli))==len(all_moduli) and all(n>1 and n%2==1 for n in all_moduli),
     'Full actual phase families have distinct odd nonunit moduli')
result={
 'contract':'Conditional theorem for the same four-flip finite profile; all actual phases arbitrary except the stated clean compatible35/77 relation. Phase countermodels retain the complete2138 mixed selected and2138 free numerical roster plus85 pure/star originals. They are not covers or irredundant families.',
 'input_sha256':sha256(raw).hexdigest(),'endpoint_sha256':sha256(endpoint_raw).hexdigest(),
 'checks':checks,'old_root1_lower':str(Elo),'old_root1_upper':str(Ehi),
 'uniform_overlap_lower':str(eps_uniform),'conditional_survivor_lower':str(gain),
 'conditional_survivor_lower_decimal':float(gain),'conditional_survivor_threshold':'1/750',
 'density_cap':str(C),'conditional_density_lower':str(gain/C),'conditional_density_threshold':'1/6000',
 'actual_pair':{'first':{'modulus':35,'residue':4},'second_compatible':{'modulus':77,'residue':4},
                'second_incompatible':{'modulus':77,'residue':26},
                'first_mass':str(m35),'second_mass':str(m77),
                'compatible_overlap':str(eps_actual),'incompatible_overlap':'0',
                'compatible_group_union':str(m35+m77-eps_actual),'incompatible_group_union':str(m35+m77)},
 'complete_roster_count':2*len(assignment)+85,
 'complete_phase_rule':'Keep original85 pure/star source. For every mixed cofactor d retain free d and selected3d; free35 and77 have the displayed phases. Every other free d has residue0 mod d. Each selected3d has residue d*((t*inverse(d mod3)) mod3), including four flipped roots. Thus all other mixed originals lie in an actual pure first-prime hole.',
 'limits':['The alignment/cleanliness premise is additional actual phase information.',
           'Equal group masses/caps do not determine cross-group intersection.',
           'Zero overlap in the second model does not rule out a uniform overlap-or-slack theorem.',
           'No Lean verification or unrestricted Erdos7 resolution.']}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:result[k] for k in ('checks','uniform_overlap_lower','conditional_survivor_lower_decimal','complete_roster_count')},sort_keys=True))
