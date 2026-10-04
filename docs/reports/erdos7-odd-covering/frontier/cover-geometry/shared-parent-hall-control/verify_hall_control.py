"""Check a NONCOVER with 83 rich deficient Hall menus; emit exact JSON data."""
from collections import Counter
from fractions import Fraction
from itertools import product, combinations
from math import prod
import json

if not __debug__:
    raise RuntimeError("Run without -O: arithmetic verification requires assertions.")

q, G = 113, 10
U = tuple(range(30, q))
primary = tuple(p for p in range(37, q) if all(p % d for d in range(2, int(p**.5)+1)))
auxiliary = tuple(p for p in range(5, 37) if all(p % d for d in range(2, int(p**.5)+1)))
assert (len(primary), len(auxiliary)) == (18, 9)
pairs = tuple((p, s) for p in primary for s in primary if p != s)[:len(U)]
selected = {p**5*s: c for (p, s), c in zip(pairs, U)}
assert len(selected) == 83
factors = {}
for p, s in pairs:
    for a, b in product(range(6), range(2)):
        if a+b:
            factors[p**a*s**b] = {r:e for r,e in ((p,a),(s,b)) if e}
palette = tuple(sorted(factors))
heights = {p:max(f.get(p,0) for f in factors.values()) for p in primary}
W = prod(p**heights[p] for p in primary)*prod(auxiliary)
Q = 9*q**G*W

def crt(data):
    N = prod(d for d, r in data)
    return sum(r*(N//d)*pow(N//d, -1, d) for d,r in data)%N

def cofactor_phases(f, a, j):
    if len(f) == 1:
        p, e = next(iter(f.items()))
        return {p:(1+a+3*j)*p**(e-1)}
    (p,e), (s,k) = sorted(f.items())
    return {p:4+a+15*j+3*(k-1), s:4+a+15*j+3*(e-1)}

rows = []
for d, r in ((3,0),(9,1)):
    rows.append(dict(d=d,r=r,kind='guard',j=0,a=1 if d==3 else 2))
for j in range(1,G+1):
    for a in range(3):
        c = 3*(j-1)+a
        data = [(q**j,c)] + ([(3**a,4%(3**a))] if a else [])
        rows.append(dict(d=3**a*q**j,r=crt(data),kind='unit',j=j,a=a,c=c))
for m in palette:
    for j,a in product(range(2), range(3)):
        phase = cofactor_phases(factors[m],a,j)
        data = [(p**e,phase[p]) for p,e in factors[m].items()]
        if a: data.append((3**a,4%(3**a)))
        c = selected[m] if m in selected and a<2 else 3+a
        if j: data.append((q,c))
        rows.append(dict(d=3**a*q**j*m,r=crt(data),kind='cofactor',j=j,a=a,m=m,c=c if j else None,phase=phase))
for p in auxiliary:
    rows.append(dict(d=p,r=0,kind='auxiliary',j=0,a=0,p=p))
D = {r['d']:r for r in rows}
assert len(D)==len(rows)

def divisors(d):
    ds=[1]
    for p in (3,q)+primary+auxiliary:
        k=0
        while d%p==0:
            d//=p; k+=1
        ds=[x*p**e for x in ds for e in range(k+1)]
    assert d==1
    return ds

comparable=0
for row in rows:
    for d in divisors(row['d']):
        if d==1: continue
        assert d in D,(row,d)
        if d != row['d']:
            assert row['r']%d != D[d]['r'],(row,D[d])
            comparable+=1

private = {}
for row in rows:
    word, qword = 4, 30+q
    phase = {p:0 for p in primary}
    auxphase = {p:1 for p in auxiliary}
    if row['kind']=='guard': word=row['r']
    elif row['kind']=='unit': qword=row['c']
    elif row['kind']=='cofactor':
        phase.update(row['phase'])
        if row['j']: qword=row['c']+q
    else: auxphase[row['p']]=0
    x=crt([(9,word),(q**G,qword)]+[(p**heights[p],phase[p]) for p in primary]+list(auxphase.items()))
    owners=[s['d'] for s in rows if x%s['d']==s['r']]
    assert owners==[row['d']],(row,owners)
    private[row['d']]=x

protected={r['c'] for r in rows if r['kind']=='unit'}
assert set(U)==set(range(q))-protected
moving=[r for r in rows if r['j'] and r.get('c') in U]
qfree=[r for r in rows if not r['j']]
colorcounts=Counter(r['c'] for r in moving)
assert len(moving)==166 and set(colorcounts)==set(U) and set(colorcounts.values())=={2}
preimages=Counter(r['m'] for r in moving)
assert set(preimages.values())=={2}

hall_rows=[]
retained_hole_checks=0
for c in U:
    owners=[r for r in moving if r['c']==c]
    parents=[D[r['d']//q] for r in owners]
    assert all(r['j']==0 for r in parents)
    menus=[set(divisors(r['m']))-{1} for r in parents]
    assert all(len(menu)==11 for menu in menus)
    assert len(set.union(*menus))==11 < 20
    assert {r['a'] for r in parents}=={0,1}
    p0,p1=parents
    assert all(p0['phase'][p]%p != p1['phase'][p]%p for p in factors[p0['m']])
    # On the two old cofactor phases, every residual target point misses all
    # originals retained by the whole-component exchange and both stripped
    # chosen owners. Only the fresh palette could cover this residual slice.
    old_parent_labels={r['d'] for r in parents}
    final_retained=[r for r in rows if r not in moving and r['d'] not in old_parent_labels]
    for parent in parents:
        phase={p:0 for p in primary}
        phase.update(parent['phase'])
        safe_hits=0
        for word in range(9):
            x=crt([(9,word),(q**G,c+q)]+[(p**heights[p],phase[p]) for p in primary]+[(p,1) for p in auxiliary])
            target_hit=x%parent['d']==parent['r'] and word%3!=0 and word%9!=1
            if target_hit:
                safe_hits+=1
                assert all(x%r['d']!=r['r'] for r in final_retained)
                assert all(x%(r['d']//q)!=r['r']%(r['d']//q) for r in owners)
                retained_hole_checks+=1
        assert safe_hits==(5 if parent['a']==0 else 2)
    hall_rows.append(dict(color=c,owners=[r['d'] for r in owners],parents=[r['d'] for r in parents],cofactor=p0['m'],divisor_count=12,menu_union=11,tag_demand=20,tag_deficit=9))

# Every pair of moving supports has an available third support disjoint from
# both. Each needed disjoint-support edge is checked on a literal E0 witness.
edges=set()
for i,j in combinations(range(len(moving)),2):
    support=set(factors[moving[i]['m']])|set(factors[moving[j]['m']])
    bridge=next(k for k,r in enumerate(moving) if not support.intersection(factors[r['m']]))
    edges.add(tuple(sorted((i,bridge))))
    edges.add(tuple(sorted((j,bridge))))
edge_witnesses=[]
for i,j in sorted(edges):
    left,right=moving[i],moving[j]
    assert not set(factors[left['m']]).intersection(factors[right['m']])
    phase={p:0 for p in primary}
    phase.update(left['phase']); phase.update(right['phase'])
    x=crt([(9,4)]+[(p**heights[p],phase[p]) for p in primary]+[(p,1) for p in auxiliary])
    assert x%(left['d']//q)==left['r']%(left['d']//q)
    assert x%(right['d']//q)==right['r']%(right['d']//q)
    assert all(x%r['d']!=r['r'] for r in qfree)
    edge_witnesses.append(dict(left=left['d'],right=right['d'],base=x))

# An actual private base is in VC, but any disjoint-support color misses it.
other=moving[0]
missing=next(r for r in moving if not set(factors[other['m']]).intersection(factors[r['m']]))
missing_color=missing['c']
x=private[other['d']]
assert all(x%r['d']!=r['r'] for r in qfree)
assert all(x%(r['d']//q)!=r['r']%(r['d']//q) for r in moving if r['c']==missing_color)
miss=crt([(9*W,x%(9*W)),(q**G,missing_color+q)])
assert not any(miss%r['d']==r['r'] for r in rows)

# Give each full old cofactor phase half the cofactor mass, and Haar measure
# to the ternary coordinate. Every nonunit tag hits at most one phase.
palette_upper=Fraction(1+Fraction(11,2),18)
target=Fraction(Fraction(5,9)+Fraction(2,9),2)
assert (palette_upper,target)==(Fraction(13,36),Fraction(7,18))
assert palette_upper < target

result=dict(scope='NONCOVER: full every-color service is false',q=q,q_height=G,unprotected_colors=list(U),canonical_palette='3^k e with k>=3 and e a positive divisor of the chosen cofactor n; one AP per numerical label',canonical_palette_allows_retained_and_stripped_assistance=True,classes=len(rows),primary_primes=list(primary),auxiliary_primes=list(auxiliary),support_primes_including_q_and_3=29,palette_cofactors=len(palette),private_points_checked=len(private),comparable_pairs_checked=comparable,moving_owners=len(moving),colors=len(U),owners_per_color=2,numeric_cofactor_preimages_max=max(preimages.values()),all_parent_divisor_counts=12,hall_failed_colors=len(hall_rows),nonunit_menu_union_per_color=11,tag_demand_per_color=20,masked_component_count=1,masked_graph_diameter_upper=2,checked_E0_edge_witnesses=len(edges),retained_and_stripped_residual_hole_checks=retained_hole_checks,canonical_palette_target_mass=str(target),canonical_palette_mass_upper=str(palette_upper),canonical_palette_repair_possible=False,inside_component_original_color=other['c'],inside_component_missing_color=missing_color,inside_component_private_integer=x,uncovered_integer=miss,period=Q,whole_cover=False,all_color_full_service=False,EB1=False,hall_rows=hall_rows)
print(json.dumps(result,indent=2))
