#!/usr/bin/env python3
"""Actual finite AP family refuting the unrestricted report564 profile threshold.
No CRT-period scan. Does not bound actual survivor mass above or settle noncoverage.
"""
from fractions import Fraction as F
from collections import Counter,defaultdict
from functools import lru_cache
from itertools import combinations,product
from math import prod
from pathlib import Path
import hashlib,json,argparse
P=(3,5,7,11,13,17,19);Q=P[1:];L=P[3:]
H=8;K=4;A=7
S0=F(65869,378675)
B5=F(19132074022251234990036997833948759259,18473247078046657922374787501704265625)
TARGET=51*B5/310
CHECKS={}
def check(name,value):
    if name in CHECKS or not value:raise RuntimeError(name)
    CHECKS[name]=True

def comb(p,d,e):return d*p**(e-1)+(p**(e-1)-1)//(p-1)
def neutral(p,h):return (p**h-1)//(p-1)
def mask_of(S):return sum(1<<Q.index(q) for q in S)
def crt(rows):
    n=prod(m for m,r in rows)
    return n,sum(r*(n//m)*pow(n//m,-1,m) for m,r in rows)%n

def root_phase(a,S):
    if S==(5,) and a==2:return 2
    if S==(7,) and a>=3:return 7+9*comb(3,2,a-2)
    return comb(3,2,a)

def channels(S,a=None):
    if a is None:return tuple(len(S)+6 for q in S)
    if (S==(5,) and a==2) or (S==(7,) and a>=3):return (3,)
    return tuple(min(len(S)+1,q-1) for q in S)

supports=[s for size in range(1,7) for s in combinations(Q,size)]
groups=[]
for a in range(1,A+1):
    for S in supports:
        groups.append({'kind':'rooted','support':S,'root_depth':a,'root_residue':root_phase(a,S),'channels':channels(S,a)})
for size in (2,3,4):
    for S in combinations(L,size):
        groups.append({'kind':'old','support':S,'root_depth':0,'root_residue':0,'channels':channels(S)})
check('group_count',len(groups)==452)
check('valid_channels',all(all(0<=d<q and d not in (0,1) for q,d in zip(g['support'],g['channels'])) for g in groups))

# Full original labels are explicitly generated and hashed, never projected/merged.
seen=set();digest=hashlib.sha256()
def add(row):
    n,r=row
    if n in seen or n<=1 or n%2==0 or not 0<=r<n:raise RuntimeError('original_label')
    seen.add(n);digest.update((str(n)+','+str(r)+'\n').encode())
for p in P:
    for e in range(1,H+1):add((p**e,comb(p,0,e)))
for g in groups:
    for exps in product(range(1,K+1),repeat=len(g['support'])):
        rows=[(q**e,comb(q,d,e)) for q,d,e in zip(g['support'],g['channels'],exps)]
        if g['root_depth']:rows.append((3**g['root_depth'],g['root_residue']))
        add(crt(rows))
check('all_original_labels_distinct',len(seen)==110032)

# Each channel is a disjoint union of depth-e cylinders, disjoint from the pure comb.
# Two different channels are disjoint because the first non-1 digit is different.
w={p:1-sum((F(1,p**e) for e in range(1,H+1)),F()) for p in P}
c={q:sum((F(1,q**e) for e in range(1,K+1)),F())/w[q] for q in Q}
check('actual_root_source_mass',w[3]==F(3281,6561))
for p in P:
    check('finite_pure_mass_'+str(p),w[p]==F(p-2,p-1)+F(1,(p-1)*p**H))
    # Direct finite word comparisons check all distinct channel/depth combinations used.
    used={d for g in groups for q,d in zip(g['support'],g['channels']) if q==p}|{0}
    cells=[(e,d,comb(p,d,e)) for d in used for e in range(1,H+1 if d==0 else K+1)]
    for i,(e,d,r) in enumerate(cells):
        check('comb_pair_'+str(p)+'_'+str(i),all(r%(p**min(e,f))!=s%(p**min(e,f)) for f,j,s in cells[:i]))

# A group-private witness proves private witnesses for all its original exponent tuples.
# Specified Q coordinates have exactly one non-1 digit, at their target exponent;
# unspecified Q coordinates are neutral. Group membership then means channel equality.
def witness_root(g):
    a=g['root_depth'];S=g['support']
    if not a:return neutral(3,H)
    if S==(5,) and a==2:return 2
    if S==(7,) and a>=3:return root_phase(a,S)
    if a==1:return 5
    if a==2:return 7
    return root_phase(a,S)
def group_matches(g,root,code):
    if g['root_depth'] and root%(3**g['root_depth'])!=g['root_residue']:return False
    return all(code.get(q)==d for q,d in zip(g['support'],g['channels']))
for i,g in enumerate(groups):
    root=witness_root(g)
    code=dict(zip(g['support'],g['channels']))
    check('group_private_'+str(i),[j for j,f in enumerate(groups) if group_matches(f,root,code)]==[i])
    check('group_private_avoids_pure3_'+str(i),all(root%(3**e)!=comb(3,0,e) for e in range(1,H+1)))

cap={mask_of(S):prod((c[q] for q in S),start=F(1)) for S in supports}
rooted=[g for g in groups if g['kind']=='rooted'];old=[g for g in groups if g['kind']=='old']
by_phase=defaultdict(list)
for g in rooted:by_phase[(3**g['root_depth'],g['root_residue'])].append(g)
source=[r for r in range(3**H) if all(r%(3**e)!=comb(3,0,e) for e in range(1,H+1))]
check('actual_root_enumeration',len(source)==3281)
profile_counts=Counter();profile_reps={}
for r in source:
    active=old+sum((gs for (mod,res),gs in by_phase.items() if r%mod==res),[])
    union_channels=defaultdict(set);root_counts=Counter()
    for g in active:
        mask=mask_of(g['support'])
        union_channels[mask].add(g['channels'])
        if g['kind']=='rooted':root_counts[mask]+=1
    # Distinct vectors correspond to disjoint Q-channel rectangles, so these are exact unions.
    signature=tuple(len(union_channels[m]) for m in range(1,64))+tuple(root_counts[m] for m in range(1,64))
    profile_counts[signature]+=1;profile_reps.setdefault(signature,r)
check('six_actual_root_profiles',len(profile_counts)==6)

def polynomials(weights):
    @lru_cache(None)
    def phi(mask):
        if not mask:return F(1)
        bit=mask&-mask;val=phi(mask^bit);s=mask
        while s:
            if s&bit:val-=weights.get(s,F())*phi(mask^s)
            s=(s-1)&mask
        return val
    return {m:phi(m) for m in range(64)}

profiles=[];G=F();G0=F();Omega=F()
for i,(sig,n) in enumerate(sorted(profile_counts.items())):
    weights={m:sig[m-1]*cap[m] for m in range(1,64)}
    pp=polynomials(weights)
    for m,v in pp.items():check('actual_profile_'+str(i)+'_subset_'+str(m),v>0)
    h=pp[63]
    collision=sum((max(sig[63+m-1]-1,0)*cap[m] for m in range(1,64)),F())
    g=max(h,S0-collision,F())
    check('actual_profile_'+str(i)+'_g_equals_h',g==h)
    mass=F(n,len(source));G+=mass*g;G0+=mass*h;Omega+=mass*collision
    profiles.append({'representative_root_mod6561':profile_reps[sig],'count':n,'mass':mass,
                     'union_multiplicities':sig[:63],'active_rooted_group_counts':sig[63:],
                     'scope_union_probabilities':weights,'all64_polynomials':pp,'h':h,'collision':collision,'g':g})
check('root_profile_partition',sum((p['mass'] for p in profiles),F())==1)
check('profile_certificate_strict_failure',G==G0<TARGET)

# Independent integrated identity from two balanced phase moves.
base={m:cap[m]*(2 if m&3==0 and m.bit_count()>=2 else 1) for m in range(1,64)}
pb=polynomials(base)
old_weights={m:cap[m] for m in range(1,64) if m&3==0 and m.bit_count()>=2}
cold=polynomials(old_weights)[63]
zero=1-sum((F(1,3**a) for a in range(1,A+1)),F())/w[3]
moved=sum((F(1,3**a) for a in range(3,A+1)),F())/w[3]
identity=(1-zero)*pb[63]+zero*cold-moved*c[5]*c[7]*pb[60]
check('independent_negative_cross_term_identity',identity==G)
# Direct root-region cardinalities: zero, B, A1\B, movedD, A2\D, oldA>=3.
mB=F(1,9)/w[3];mA1=F(1,3)/w[3];mA2=F(1,9)/w[3]
check('six_root_region_masses',sorted(p['mass'] for p in profiles)==sorted([zero,mB,mA1-mB,moved,mA2-moved,moved]))
check('collision_identity',Omega==mB*c[5]+moved*c[7])
# Endpoint boxes also certify the same finite construction at H=A=K=n>=3.
limit_c={q:F(1,q-2) for q in Q}
limit_base={m:prod((limit_c[q] for i,q in enumerate(Q) if m>>i&1),start=F(1))
            *(2 if m&3==0 and m.bit_count()>=2 else 1) for m in range(1,64)}
limit_profiles={}
for name,dx,dy,mass,omega in [('zero',0,0,F(),F()),('base',0,0,F(4,9),F()),
    ('extra5',1,0,F(2,9),limit_c[5]),('missing5',-1,0,F(1,9),F()),
    ('missing5_extra7',-1,1,F(1,9),limit_c[7]),('missing7',0,-1,F(1,9),F())]:
    weights=dict(limit_base)
    if name=='zero':weights={m:v/2 for m,v in limit_base.items() if m&3==0 and m.bit_count()>=2}
    else:weights[1]+=dx*limit_c[5];weights[2]+=dy*limit_c[7]
    pp=polynomials(weights)
    for mask,value in pp.items():check('limit_'+name+'_positive_'+str(mask),value>0)
    check('limit_'+name+'_g_equals_h',max(pp[63],S0-omega,F())==pp[63])
    limit_profiles[name]={'mass':mass,'all64_polynomials':pp,'h':pp[63],'omega':omega}
limit_G=sum((r['mass']*r['h'] for r in limit_profiles.values()),F())
limit_poly=polynomials(limit_base)
check('limit_baseline',limit_poly[63]==S0)
check('limit_L_complement',limit_poly[60]==F(598,935))
check('limit_cross_term',limit_G==S0-limit_poly[60]/135)
check('limit_fraction',limit_G==F(233,1377))
check('limit_strict_failure',limit_G<TARGET)
check('limit_mass_partition',sum((r['mass'] for r in limit_profiles.values()),F())==1)
check('finite_n3_collision5',F(5**3-1,3*5**3+1)>S0)
check('finite_n3_collision7',F(7**3-1,5*7**3+1)>S0)
result={'scope':__doc__,'parameters':{'P':P,'Q':Q,'L':L,'pure_height_H':H,'Q_mixed_height_K':K,'root_mixed_height_A':A},
        'original_count':len(seen),'originals_modulus_residue_stream_sha256':digest.hexdigest(),
        'mixed_groups':groups,'actual_pure_masses':w,'actual_Q_channel_masses':c,
        'root_profiles':profiles,'baseline_profile':pb[63],'old_only_profile':cold,'zero_root_mass':zero,'moved_root_mass':moved,
        'negative_cross_correction':moved*c[5]*c[7]*pb[60],'G0':G0,'G':G,'target':TARGET,'strict_target_gap':TARGET-G,
        'G_decimal':float(G),'target_decimal':float(TARGET),'gap_decimal':float(TARGET-G),'Omega':Omega,
        'saturation_limit':{'profiles':limit_profiles,'G':limit_G,'target_gap':TARGET-limit_G},
        'checks':CHECKS,'passed_checks':len(CHECKS),
        'limits':'Refutes only the universal report564 G threshold. No upper bound on actual nu0(U), no all-law impossibility, no Lean verification.'}

def encode(v):
    if isinstance(v,F):return str(v)
    raise TypeError(type(v).__name__)
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=parser.parse_args()
args.output.write_text(json.dumps(result,default=encode,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('original_count','passed_checks','G_decimal','target_decimal','gap_decimal','originals_modulus_residue_stream_sha256')},indent=2))
print('G='+str(G));print('gap='+str(TARGET-G));print('json_sha256='+hashlib.sha256(args.output.read_bytes()).hexdigest())
