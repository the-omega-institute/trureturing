#!/usr/bin/env python3
"""Exact necessary cut profiles and the forced nineteen-point law for Report449.

Standard library only. The companion ordinary proof forces the private points
from actual literal trees; this program does not treat relaxed profiles as
realized sources or certify unrestricted odd noncoverage.
"""

from fractions import Fraction as F
from itertools import product, combinations, combinations_with_replacement
import argparse
import json
from math import lcm
from pathlib import Path

N=(4,5,5,5)
Q=(2,3,3,3)

def ceild(x,d): return (x+d-1)//d

def ff(a,q,p): return p+(a-q)*ceild(p,q)

def integer_private_min(active,eligible,u):
    if u<=0: return 0, []
    candidates=[]
    for r in eligible:
        for p in range(ceild(u,2)+1):
            z=max(p,u-p)
            cost=sum(ff(active[j],Q[j],p if j==r else z) for j in eligible)
            candidates.append((cost,r,p))
    v=min(x[0] for x in candidates)
    return v,[x[1:] for x in candidates if x[0]==v]

def literal_source_control():
    """One actual 118-point blocker with a matching integral flow and cut.

    It witnesses nonemptiness of the cut66 source class, not realization
    by an original odd whole-cover residual.
    """
    common = {7*h for h in range(5)}
    private = {(r,c,r+7*c) for r,n in enumerate(N,start=1) for c in range(n)}
    source = set(private)
    for r,n in enumerate(N,start=1):
        for c in range(n):
            source.update((r,c,y) for y in common)
            if r == 1:
                source.add((r,c,29))
    if len(source) != 118:
        raise RuntimeError('literal source size')
    choices = list(combinations(range(5),3))
    tree_checks = 0
    fibres = {(r,c):{y for rr,cc,y in source if (rr,cc)==(r,c)}
              for r in range(5) for c in range(5)}
    for roots in choices:
        for childsets in product(choices,repeat=3):
            leaves = set().union(*(fibres[r,c] for r,cs in zip(roots,childsets) for c in cs))
            counts = [sum(y%7==g for y in leaves) for g in range(7)]
            if sum(v>=3 for v in counts)<3:
                raise RuntimeError(('literal product blocking',roots,childsets))
            tree_checks += 1
    projection = {y for r,c,y in source}
    counts = [sum(y%7==g for y in projection) for g in range(7)]
    if tree_checks!=10000 or sum(v>=5 for v in counts)<5:
        raise RuntimeError('standalone tree')

    # Units1/63: every private point gets2. Public column0 gets21,
    # and the public leaf29 gets7. Each point follows its actual bridge.
    flow = {point:2 for point in private}
    for r in (2,3,4):
        for c,v in enumerate((2,2,1,1,1)):
            flow[r,c,7*c] = v
    for c,v in enumerate((2,2,2,1)):
        flow[1,c,29] = v
    if sum(flow.values())!=66 or not set(flow)<=source:
        raise RuntimeError('actual matching flow')
    for r,n in enumerate(N,start=1):
        if sum(v for (rr,c,y),v in flow.items() if rr==r)>21:
            raise RuntimeError('source/root capacity')
        for c in range(n):
            if sum(v for (rr,cc,y),v in flow.items() if (rr,cc)==(r,c))>7:
                raise RuntimeError('root/child capacity')
            for g in range(7):
                if sum(v for (rr,cc,y),v in flow.items() if (rr,cc,y%7)==(r,c,g))>6:
                    raise RuntimeError('private column capacity')
    if any(v>2 or v<=0 for v in flow.values()):
        raise RuntimeError('private leaf capacity')
    if any(sum(v for (r,c,y),v in flow.items() if y%7==g)>21 for g in range(7)):
        raise RuntimeError('public column capacity')
    if any(sum(v for (r,c,y),v in flow.items() if y==h)>7 for h in range(49)):
        raise RuntimeError('public leaf capacity')
    # Cut all19 private leaf edges, public column0 and public leaf29.
    if any(point not in private and point[2]%7!=0 and point[2]!=29 for point in source):
        raise RuntimeError('cut misses an actual path')
    cut_units = 21+7+2*len(private)
    if cut_units!=sum(flow.values()):
        raise RuntimeError('flow/cut mismatch')
    return {'actual_points':len(source),'five_tree_tests_via_ternary_seven_duality':tree_checks,
            'standalone_leaf_counts':counts,'matching_flow_and_cut':str(F(cut_units,63)),
            'source':sorted(source),'flow_units_over63':[[*p,v] for p,v in sorted(flow.items())],
            'scope':'One actual finite source and an explicit matching flow/cut; no original covering-family realization.'}


def verify():
    small=[]
    compatible67=[]
    min_by_eligible={}
    partial_four_min=None
    profiles=0
    for active in product(*(range(n+1) for n in N)):
        top=sum(min(3,n-a) for n,a in zip(N,active))
        eligible=[r for r in range(4) if active[r]>=Q[r]]
        j=len(eligible)
        for k in range(10):
            profiles+=1
            if j==0:
                lower=7*(top+k)
            elif j==1:
                # Each active nonempty child needs a private cut if R=0.
                lower=7*(top+k)+(2*sum(active) if k==0 else 0)
            else:
                z,_=integer_private_min(active,eligible,max(0,9-k))
                # A full-active standalone tree also forces R + sum L >=5/3.
                if active==N: z=max(z,15-k)
                if k==0: z=max(z,sum(active))
                lower=7*(top+k)+2*z
            min_by_eligible[j]=min(lower,min_by_eligible.get(j,lower))
            if j==4 and active!=N:
                partial_four_min=lower if partial_four_min is None else min(partial_four_min,lower)
            if lower<=67 and (67-7*(top+k))%2==0:
                compatible67.append({'active':active,'top_units':top,'public_units':k,
                                     'private_units':(67-7*(top+k))//2})
            if lower<=66:
                small.append({'active':active,'top_units':top,'public_units':k,
                              'private_min_units':(lower-7*(top+k))//2 if j else None,
                              'lower_numerator':lower})
    # A cut with R>1 costs >=70/63 if not fully active, or >=80/63 if fully active.
    if small != [{'active':N,'top_units':0,'public_units':3,'private_min_units':22,'lower_numerator':65},
                 {'active':N,'top_units':0,'public_units':4,'private_min_units':19,'lower_numerator':66}]:
        raise RuntimeError(('unexpected small profiles',small))

    # A cost66 cut cannot have public k3: it would require odd private numerator45.
    cut66=[p for p in small if (66-7*(p['top_units']+p['public_units']))%2==0]
    if len(cut66)!=1 or cut66[0]['public_units']!=4: raise RuntimeError(cut66)

    # Exhaust every p-vector for the surviving all-active k4 (u5) case.
    attainers=[]
    for p in product(range(6),repeat=4):
        if any(p[i]+p[j]<5 for i,j in combinations(range(4),2)): continue
        cost=sum(ff(N[r],Q[r],p[r]) for r in range(4))
        if cost==19: attainers.append(p)
    if attainers != [(2,3,3,3)]: raise RuntimeError(('p-shape',attainers))

    # Sorted child integer costs attaining each required pair sum and total.
    shapes={}
    for n,q,p,total in [(4,2,2,4),(5,3,3,5)]:
        arr=[z for z in combinations_with_replacement(range(total+1),n)
             if sum(z)==total and sum(z[:q])==p]
        if arr != [(1,)*n]: raise RuntimeError(('child-shape',arr))
        shapes[str(n)]=arr

    # At67 the only candidates are fully active, (k,Z)=(3,23) or(5,16).
    expected67=[{'active':N,'top_units':0,'public_units':3,'private_units':23},
                {'active':N,'top_units':0,'public_units':5,'private_units':16}]
    if compatible67!=expected67: raise RuntimeError(('cut67 profiles',compatible67))
    p67=[]
    for p in product(range(5),repeat=4):
        if any(p[i]+p[j]<4 for i,j in combinations(range(4),2)): continue
        if sum(ff(N[r],Q[r],p[r]) for r in range(4))==16: p67.append(p)
    if p67!=[(2,2,2,2)]: raise RuntimeError(('k5 private p',p67))
    full67=[z for z in combinations_with_replacement(range(5),5)
            if sum(z)==4 and sum(z[:3])==2]
    if full67!=[(0,1,1,1,1)]: raise RuntimeError(('k5 full shape',full67))

    # Independent arithmetic on the law forced by the ordinary tree/column argument.
    caps={(0,0):F(1),(1,0):F(5,19),(0,1):F(5,19),(1,1):F(5,19),
          (2,0):F(1,19),(0,2):F(1,19),(2,1):F(1,19),(1,2):F(1,19),(2,2):F(1,19)}
    envelope=sum((2*a+1)*(2*b+1)*v for (a,b),v in caps.items())
    if envelope!=F(159,19) or envelope>=9: raise RuntimeError(('law-envelope',envelope))
    # Literal CRT realization of the forced nineteen-point PRIVATE LAW pattern.
    # This subset is not claimed to satisfy the tree hypotheses by itself.
    crt=lambda x,y: x+25*((y-x)*pow(25,-1,49)%49)
    law={}
    for r,n in enumerate(N,start=1):
        g=r+1
        for c in range(n):
            law[crt(r+5*c,g+7*c)]=F(1,19)
    if len(law)!=19 or sum(law.values())!=1: raise RuntimeError('private law')
    divs=sorted(5**a*7**b for a,b in caps)
    actual_caps={}
    cylinder_checks=0
    for d in divs:
        masses=[sum((v for x,v in law.items() if x%d==phase),F()) for phase in range(d)]
        cylinder_checks+=len(masses)
        actual_caps[d]=max(masses)
        target=caps[next((a,b) for a,b in caps if 5**a*7**b==d)]
        if actual_caps[d]!=target: raise RuntimeError(('literal cap',d,actual_caps[d],target))
    literal_envelope=sum(actual_caps[lcm(d,e)] for d in divs for e in divs)
    center=crt(2,3)
    centered_value=sum(v*sum(x%d==center%d for d in divs)**2 for x,v in law.items())
    if literal_envelope!=envelope or centered_value!=envelope: raise RuntimeError('literal envelope')
    if partial_four_min!=68: raise RuntimeError(('partial profile minimum',partial_four_min))
    result={'relaxed_profile_checks':profiles,'min_by_eligible_count':min_by_eligible,'partial_four_eligible_min':partial_four_min,
            'lower_profiles_at_most66':small,'compatible_cut66_profile':cut66,
            'compatible_cut67_profiles':compatible67,'cut67_k5_p_attainers':p67,
            'cut67_k5_full_shape':full67,'private_p_attainers':attainers,'sorted_child_shapes':shapes,
            'common_law_lcm_envelope':str(envelope),'margin_below9':str(9-envelope),
            'literal_private_law_atoms':len(law),'literal_cylinder_checks':cylinder_checks,
            'literal_caps':{str(d):str(v) for d,v in actual_caps.items()},
            'literal_ordered_lcm_pairs':len(divs)**2,'literal_centered_lower':str(centered_value),
            'cut66_nonempty_source_control':literal_source_control(),
            'scope':'Necessary relaxed cut profiles and a canonical nineteen-point private-law pattern; actual private-column forcing is proved in companion text. The private subset is not claimed to satisfy the tree premises, and no source realization follows from the profile enumeration.'}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).with_suffix(".json"),
        help="exact result path (default: sibling .json)",
    )
    args = parser.parse_args()
    result = verify()
    payload = json.dumps(result, indent=2) + "\n"
    args.output.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
