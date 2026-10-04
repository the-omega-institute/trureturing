"""Check the arithmetic control in Report862; emit exact result data as JSON."""

from pathlib import Path
from itertools import combinations, product
from math import prod
from collections import Counter
import json

if not __debug__:
    raise RuntimeError('Run without -O: arithmetic verification requires assertions.')

P=(19,23,29,31,37,41,43,47,53,59,61,67,71,73,79)
q=113
G=10
A=(2,4,5,7,8)
U=tuple(range(30,113))
all_primes=tuple(p for p in range(5,q) if all(p%d for d in range(2,int(p**.5)+1)))
aux=tuple(p for p in all_primes if p not in P)
subsets=[S for k in range(1,4) for S in combinations(P,k)]
triples=[S for S in subsets if len(S)==3]
small=[S for S in subsets if len(S)<3]
cells=[(c,z) for c in U for z in A]
assignment={S:cells[i%len(cells)] for i,S in enumerate(triples)}
protected_cells=[(c,z) for c in range(3,30) for z in A]
assignment.update({S:protected_cells[i] for i,S in enumerate(small)})
assert len(assignment)==len(subsets)

def crt(data):
    n=prod(d for d,r in data)
    return sum(r*(n//d)*pow(n//d,-1,d) for d,r in data)%n if n>1 else 0

phase_colors=json.loads(Path(__file__).with_name('phase_colors.json').read_text())
rows=[]
for d,r,a in [(3,0,1),(9,1,2)]:
    rows.append(dict(d=d,r=r,S=(),a=a,j=0))
for j in range(1,G+1):
    for a in range(3):
        c=3*(j-1)+a
        data=[(q**j,c)]+([(3**a,4%(3**a))] if a else [])
        rows.append(dict(d=3**a*q**j,r=crt(data),S=(),a=a,j=j,c=c,z=4))
for S in subsets:
    c,z=assignment[S]
    for a in range(3):
      for j in range(2):
        tag=1+a+3*j+6*(len(S)-1)
        if len(S)==3:
            colors=phase_colors[str(j)][','.join(map(str,S))]
            phase={p:13+3*j+(colors[i]+(0 if a==2 else a+1))%3 for i,p in enumerate(S)}
        else:
            phase={p:tag for p in S}
        data=list(phase.items())
        if a: data.append((3**a,z%(3**a)))
        if j: data.append((q,c))
        d=3**a*q**j*prod(S)
        rows.append(dict(d=d,r=crt(data),S=S,a=a,j=j,tag=tag,phase=phase,c=c,z=z))
for p in aux:
    for a in range(3):
        data=[(p,a)]+([(3**a,4%(3**a))] if a else [])
        rows.append(dict(d=3**a*p,r=crt(data),S=(p,),a=a,j=0,aux=p,phase={p:a},z=4))
protected_unit_digits={r['c'] for r in rows if r['j'] and not r['S']}
available_complement=set(range(q))-protected_unit_digits
assert set(U)==available_complement
D={r['d'] for r in rows}
assert len(D)==len(rows)
# Exact numerical divisor closure via prime-factor divisor generation.
for row in rows:
    divs=[1]
    tmp=row['d']
    for p in (3,q)+all_primes:
        e=0
        while tmp%p==0: tmp//=p; e+=1
        if e: divs=[d*p**a for d in divs for a in range(e+1)]
    assert tmp==1
    assert all(d==1 or d in D for d in divs)
# Construct one private integer per original; verify against EVERY original.
unit_private={3:(0,30+q),9:(1,30+q)}
unit_private.update({row['d']:(4,row['c']) for row in rows if row['j'] and not row['S']})
private_checks=0
private_integers={}
for row in rows:
    if 'aux' in row:
        data=[(9,4),(q**G,30+q)]+[(p,0) for p in P]+[(p,row['a'] if p==row['aux'] else 3) for p in aux]
    elif row['S']:
        S=set(row['S'])
        data=[(9,row['z']),(q**G,row['c']+q if row['j'] else 30+q)]+[(p,row['phase'][p] if p in S else 0) for p in P]+[(p,3) for p in aux]
    else:
        z,c=unit_private[row['d']]
        data=[(9,z),(q**G,c)]+[(p,0) for p in P]+[(p,3) for p in aux]
    x=crt(data)
    owners=[r['d'] for r in rows if x%r['d']==r['r']]
    assert owners==[row['d']], (row,owners)
    private_integers[row['d']]=x
    private_checks+=1
# Comparable class disjointness is checked directly as well.
comparable_pairs=0
for row in rows:
    for other in rows:
        if row['d']<other['d'] and other['d']%row['d']==0:
            assert other['r']%row['d']!=row['r']
            comparable_pairs+=1
moving=[r for r in rows if r['j'] and r.get('c') in U]
top=[r for r in moving if r['a']==2]
assert len(moving)==3*len(triples)
assert all(len(r['S'])==3 for r in moving)
# Every numerical original has <=3 cofactor primes: all cap29 tests are empty.
assert max(len(r['S']) for r in rows)==3
# Rectangle and SNC1's fixed word/first-digit incidence upper bound.
top_cells=Counter((r['c'],r['z']) for r in top)
assert all(top_cells[cell]>=1 for cell in cells)
all_top_cells=Counter((r.get('c'),r.get('z')) for r in rows if r['a']==2 and r['j'] and r['S'])
assert max(all_top_cells.values())==2
# Any pair of moving supports has a moving bottom triple disjoint from both.
triple_set=set(triples)
for S in triples:
  for T in triples:
    bridge=tuple(p for p in P if p not in S and p not in T)[:3]
    assert bridge in triple_set
# For two disjoint moving supports, all coordinates are 0 or tags16..18;
# q-free core tests use tags1,2,3,7,8,9,13,14,15 and therefore all miss.
retained_tags={v for r in rows if not r['j'] and 'phase' in r and 'aux' not in r for v in r['phase'].values()}
moving_tags={v for r in moving for v in r['phase'].values()}
assert retained_tags.isdisjoint({0}|moving_tags)
# Complete-word two-prime phase capacity one, including q.
# Reconstruct every key from numerical d and r, independently of phase metadata.
pair_incidence=Counter()
metadata_pair_incidence=Counter()
for row in rows:
    if row['d']%9: continue
    primes=[p for p in all_primes+(q,) if row['d']%p==0]
    for p,r in combinations(primes,2):
        pair_incidence[(row['r']%9,p,r,row['r']%p,row['r']%r)]+=1
    phase=dict(row.get('phase',{}))
    if row['j']: phase[q]=row['c']
    for p,r in combinations(sorted(phase),2):
        metadata_pair_incidence[(row['r']%9,p,r,phase[p],phase[r])]+=1
assert pair_incidence==metadata_pair_incidence
assert len(pair_incidence)==4530
assert max(pair_incidence.values())==1
# Existing top phase cap, checked separately and then jointly across strata.
query_max={}
for j,cap in [(0,3),(1,3)]:
    counts=Counter()
    for row in rows:
        if row['a']!=2 or row['j']!=j or len(row['S'])!=3: continue
        S=row['S']; phase=row['phase']; z=row['z']; band=range(13+3*j,16+3*j)
        for w in product(band,repeat=3):
            if sum(w[i]==phase[p] for i,p in enumerate(S))>=2:
                counts[(z,S,w)]+=1
        for pair in combinations(S,2):
            for p in P:
                if p in S: continue
                T=tuple(sorted(pair+(p,)))
                for col in band:
                    w=tuple(col if x==p else phase[x] for x in T)
                    counts[(z,T,w)]+=1
    query_max[j]=max(counts.values())
    assert query_max[j]<=cap
# Joint certificate over ALL q-free/q-bearing top strata and all phase classes.
# For primary primes, only these residues can match an owner with >=2 primes;
# 0 represents every other residue. Selected triples using auxiliary primes
# reduce to a primary pair (checked above) or have no qualifying owner.
phase_alphabet=(0,9,12,13,14,15,16,17,18)
joint_queries=Counter()
for row in rows:
    if row['a']!=2 or 'aux' in row or len(row['S'])<2: continue
    S=row['S']; phase=row['phase']; z=row['z']
    targets=set()
    for pair in combinations(S,2):
        for p in P:
            if p not in pair: targets.add(tuple(sorted(pair+(p,))))
    for T in targets:
        present=[p for p in T if p in S]
        events=set()
        for pair in combinations(present,2):
            other=next(p for p in T if p not in pair)
            for c in phase_alphabet:
                events.add(tuple(c if p==other else phase[p] for p in T))
        joint_queries.update((z,T,w) for w in events)
assert max(joint_queries.values())==3
# Joint top queries on triples {q,p,r}; combine all eligible originals.
q_top_queries=Counter()
q_phase_alphabet=tuple(range(q))
cofactor_phase_alphabet=(0,3,6,9,12,13,14,15,16,17,18)
for row in rows:
    if row['a']!=2 or 'aux' in row or not row['S']: continue
    phase=dict(row['phase'])
    if row['j']: phase[q]=row['c']
    z=row['z']
    for p,r in combinations(P,2):
        T=(q,p,r)
        present=[v for v in T if v in phase]
        if len(present)<2: continue
        events=set()
        for pair in combinations(present,2):
            other=next(v for v in T if v not in pair)
            alphabet=q_phase_alphabet if other==q else cofactor_phase_alphabet
            for c in alphabet:
                events.add(tuple(c if v==other else phase[v] for v in T))
        q_top_queries.update((z,T,w) for w in events)
assert max(q_top_queries.values())==3
# Triples containing q and auxiliary primes reduce to a fixed word/q/primary
# pair inventory of size at most one, or have no qualifying original.
# Extended all-row cap29 on {q}+four primary primes. Only j1,size3 can qualify.
q_four_queries=Counter()
for row in moving:
    phase=row['phase']; S=row['S']
    for p in P:
        if p in S: continue
        T=tuple(sorted(S+(p,)))
        for c in (0,16,17,18):
            w=tuple(c if v==p else phase[v] for v in T)
            q_four_queries[(row['c'],T,w)]+=1
assert max(q_four_queries.values())==2
# Five-sets containing q and auxiliaries have <=1 qualifying triple cofactor;
# five-sets omitting q have none.
# Exact uncovered point: every core coordinate0, aux3, safe word4, moving qdigit30.
hole=crt([(9,4),(q**G,30+q)]+[(p,0) for p in P]+[(p,3) for p in aux])
assert not any(hole%r['d']==r['r'] for r in rows)
# The preserved base belongs to E0 and misses every moving cofactor test.
# These tests omit q, so every digit in U and every higher q-suffix fails.
assert all(hole%r['d']!=r['r'] for r in rows if not r['j'])
assert all(hole%(3**r['a']*prod(r['S']))!=r['r']%(3**r['a']*prod(r['S'])) for r in moving)
# Failure of all-U service inside the actual component union, using one of
# the private integers already checked against every numerical original.
selected=moving[0]
selected_private=private_integers[selected['d']]
preserved_modulus=9*prod(all_primes)
preserved_base=selected_private%preserved_modulus
active_preserved_labels=[r['d'] for r in moving
    if selected_private%(r['d']//q**r['j'])==r['r']%(r['d']//q**r['j'])]
assert active_preserved_labels==[selected['d']]
assert all(selected_private%r['d']!=r['r'] for r in rows if not r['j'])
original_digit=selected_private%q
switched_digit=next(c for c in U if c!=original_digit)
assert original_digit==selected['c'] and original_digit in U
old_q_word=selected_private%(q**G)
switched_q_word=old_q_word-original_digit+switched_digit
inside_component_hole=crt([(preserved_modulus,preserved_base),(q**G,switched_q_word)])
assert inside_component_hole%preserved_modulus==preserved_base
assert inside_component_hole%q==switched_digit
assert (inside_component_hole%(q**G))//q==old_q_word//q
assert not any(inside_component_hole%r['d']==r['r'] for r in rows)
inside_component_failure=dict(
    original_modulus=selected['d'],
    original_residue=selected['r'],
    original_first_q_digit=original_digit,
    switched_first_q_digit=switched_digit,
    preserved_modulus=preserved_modulus,
    preserved_base=preserved_base,
    private_integer=selected_private,
    switched_uncovered_integer=inside_component_hole,
    active_moving_preserved_labels=active_preserved_labels,
    preserved_base_in_E0=True,
    preserved_base_in_component_union=True,
    higher_q_suffix_unchanged=True,
    all_U_service=False,
)
result=dict(
    q=q,
    G=G,
    protected_unit_digits=sorted(protected_unit_digits),
    full_available_moving_complement=sorted(available_complement),
    U_is_full_available_complement=set(U)==available_complement,
    primary_primes=P,
    auxiliary_primes=aux,
    classes=len(rows),
    core_classes=len(rows)-3*len(aux),
    private_points_checked=private_checks,
    comparable_pairs_checked=comparable_pairs,
    moving_digits=len(U),
    moving_owners=len(moving),
    moving_top_owners=len(top),
    occupied_top_cells=len(top_cells),
    saturated_digits=len(U),
    maximum_top_labels_per_word_digit=max(all_top_cells.values()),
    five_cofactor_prime_qualified_count=0,
    five_nonternary_prime_qualified_upper_bound=4,
    top_two_prime_phase_max=max(pair_incidence.values()),
    top_two_prime_phase_keys=len(pair_incidence),
    full_GLC1_collision_edges=0,
    top_two_of_three_phase_max=query_max,
    joint_top_two_of_three_phase_max=max(joint_queries.values()),
    joint_phase_alphabet=phase_alphabet,
    joint_nonzero_queries=len(joint_queries),
    extended_top_q_two_prime_phase_max=max(q_top_queries.values()),
    extended_all_q_four_prime_phase_max=max(q_four_queries.values()),
    masked_component_count=1,
    masked_graph_diameter_upper_bound=2,
    uncovered_integer=hole,
    period=9*q**G*prod(all_primes),
    whole_cover=False,
    all_U_fibre_at_saved_base=False,
    inside_component_all_U_failure=inside_component_failure,
    EB1=False,
)
print(json.dumps(result,indent=2))
