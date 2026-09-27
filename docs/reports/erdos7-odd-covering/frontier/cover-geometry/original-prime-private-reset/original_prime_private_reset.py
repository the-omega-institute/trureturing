#!/usr/bin/env python3
"""Exact original-AP controls for private-to-hole pure-prime reset bridge."""
from fractions import Fraction as F
from math import lcm,prod
from pathlib import Path
import argparse,hashlib,json

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,default=Path(__file__).with_name('original_completion_uniform_lift.controls.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()

def need(b,s):
    if not b:raise ValueError(s)
def factor(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=out.get(n,0)+1
    return out

def reset(x,q,y,L):
    step=L//q
    return (x+(y-x)%q*step*pow(step,-1,q))%L

def small(labels,p,a):
    L=lcm(*(m for m,r in labels));facts=factor(L);q=p**facts[p]
    target=p**a;ar=dict(labels)[target]
    need(len(set(m for m,r in labels))==len(labels),'numerical moduli distinct')
    need(all(m>1 and m%2 for m,r in labels),'odd nonunit original moduli')
    need(all(m%p or m%target==0 for m,r in labels),'pure minimum p-height hypothesis')
    hits={x:[m for m,r in labels if x%m==r] for x in range(L)}
    need(all(any(js==[m] for js in hits.values()) for m,r in labels),'every original has private point')
    holes=[x for x,js in hits.items() if not js];private=[x for x,js in hits.items() if js==[target]]
    need(bool(holes),'actual noncover')
    cof=L//q;R=[z for z in range(cof) if all(z%m!=r for m,r in labels if m%p)]
    expected={x for x in range(L) if x%target==ar and x%cof in R}
    need(set(private)==expected,'exact private = pure prefix times p-free survivor')
    edges=0
    for h in holes:
        for y in range(ar,q,target):
            x=reset(h,q,y,L)
            need(x%cof==h%cof and x%q==y,'one full p-coordinate change')
            need(hits[x]==[target],'reset target genuinely private')
            edges+=1
    need(edges==len(holes)*(q//target),'exact private/hole edge count')
    u=F(len(private),L);h=F(len(holes),L)
    need(u==F(len(R),target*cof) and h<=(target-1)*u,'same Haar private identity and hole bound')
    return dict(labels=[dict(modulus=m,residue=r) for m,r in labels],period=L,p=p,pure_exponent=a,private_points=len(private),holes=len(holes),reset_edges=edges,private_mass=str(u),hole_mass=str(h),edge_count_formula='|H|*p^(H_p-a)',membership_checks=L*len(labels))

controls=[small([(3,0),(5,1),(15,4)],3,1),small([(3,0),(5,1),(15,4)],5,1),small([(9,0),(45,1),(175,2)],3,2)]
# The minimum positive p-height hypothesis is material for a higher pure power.
negative=[(9,0),(15,6)];L=45;h=1;x=reset(h,9,0,L)
need(not any(h%m==r for m,r in negative),'higher-pure boundary hole')
need(x==36 and [m for m,r in negative if x%m==r]==[9,15],'higher pure reset can land in overlap')

# PR1 is sufficient, not necessary: the same moduli can have disjoint roots.
positive=[(9,0),(15,1)]
positive_holes=[t for t in range(45) if all(t%m!=r for m,r in positive)]
for t in positive_holes:
    y=reset(t,9,0,45)
    need([m for m,r in positive if y%m==r]==[9],'disjoint lower-height class preserves designated privacy')

path=args.source
d=json.loads(path.read_text());labels=[(r['modulus'],r['residue']) for r in d['originals']]
need(len(labels)==len(set(m for m,r in labels))==702,'same702 original numeric labels')
P=d['outside_primes'];H=d['H'];blocks=[3**H,25,49,*P];L=prod(blocks)
need(L==lcm(*(m for m,r in labels)),'full original period')
values=[3**H-1,1,1,*([2]*len(P))]
h=sum(v*(L//q)*pow(L//q,-1,q) for v,q in zip(values,blocks))%L
need(not any(h%m==r for m,r in labels),'actual numeric702-family hole')
checks=len(labels);counts={};prime3_reset=None
for p,q in [(3,3**H),(5,25),(7,49)]+[(p,p) for p in P]:
    need((p,0) in labels,'retained original prime class')
    for y in range(0,q,p):
        x=reset(h,q,y,L)
        owners=[m for m,r in labels if x%m==r];checks+=len(labels)
        need(owners==[p],'every original prime-root reset is truly private')
        if p==3 and y==0:prime3_reset=x
    counts[str(p)]=q//p
need(sum(counts.values())==177,'177 actual private neighbors in141 directions')
# Pointwise in every original cofactor b in R3, independently of its law.
for t in range(3**H):
    if t%3==0:
        need(t%3==0 and all(t%(3**e)!=3**(e-1)-1 for e in range(2,H+1)),'pure3 root is disjoint from deeper pure comb')
        need(all(t%(3**e)!=2*3**(e-1)-1 for e in range(1,H+1)),'pure3 root is disjoint from mixed comb')
need(all((3**H-1)%(3**e)!=r for e in range(1,H+1) for r in (3**(e-1)-1,2*3**(e-1)-1)),'terminal point misses every3-bearing original')
result=dict(scope='Ordinary exact original-AP controls; not Lean or an odd-distinct PS1 counterexample. The prime-reset criterion assumes a pure original at the minimum positive p-height, irredundancy/comparable disjointness, and retains all original numerical moduli. No whole-cover assumption is used.',small_controls=controls,higher_pure_missing_hypothesis=dict(labels=negative,period=45,hole=1,reset=36,reset_owners=[9,15]),higher_pure_disjoint_lower_height=dict(labels=positive,period=45,holes=len(positive_holes),every_reset_private_to=9),report450=dict(source_json=path.name,source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),original_classes=702,period=str(L),actual_hole=str(h),private3_neighbor=str(prime3_reset),prime_directions=len(counts),actual_private_neighbors=sum(counts.values()),membership_checks=checks,private_neighbors_per_prime=counts,common_law='Uniform(Z/81) times ANY probability nu supported on the actual R3. For every cofactor in R3 all first3-digit0 points are private to original0 mod3, and terminal3-value80 is a hole.',bad_prime3_private_mass='1/3',terminal_hole_mass='1/81',independent_prime3_resampling_private_to_terminal_probability='1/243'))
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(small_controls=controls,report450_checks=checks,prime_directions=len(counts),actual_private_neighbors=sum(counts.values()),bad_prime3_private_mass='1/3',terminal_hole_mass='1/81'),indent=2))
