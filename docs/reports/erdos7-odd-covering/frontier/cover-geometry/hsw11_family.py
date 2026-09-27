#!/usr/bin/env python3
"""Literal finite-family reconstruction of HSW 2104.00602v1 Figures 18--22.

The auxiliary closing prime is 23. Power branches have every height 1..22.
A small parameterized AP family represents all actual moduli and residues;
no exhaustive check over the enormous complete period is claimed.
"""
from collections import Counter
from itertools import combinations
from math import gcd, prod
import json
import random

ROOT = 11
CLOSING = 23
HEIGHT = CLOSING-1
POWER_PRIMES = (3, 5, 7, 13, 17, 19)
ALL_PRIMES = tuple(sorted((ROOT, CLOSING)+POWER_PRIMES))


def require(ok, message):
    if not ok:
        raise ValueError(message)


def crt_pair(a, m, b, n):
    require(gcd(m, n) == 1, 'noncoprime CRT')
    return (a+m*(((b-a)*pow(m, -1, n)) % n)) % (m*n), m*n


def crt_coordinates(coordinates, moduli):
    a, m = 0, 1
    for p in sorted(moduli):
        a, m = crt_pair(a, m, coordinates[p], moduli[p])
    return a, m


def support(m):
    out = []
    for p in ALL_PRIMES:
        if m % p == 0:
            m //= p
            require(m % p != 0, 'diagram base leaf unexpectedly has a square factor')
            out.append(p)
    require(m == 1, 'unknown factor in a literal diagram leaf')
    return tuple(out)


def leaf(m, source):
    return dict(kind='leaf', modulus=m, source=source)


def wedge(optional, factor, source, take=None):
    values = sorted(factor*prod(subset) for n in range(len(optional)+1)
                    for subset in combinations(optional, n))
    require(len(set(values)) == len(values), 'wedge repeats a modulus')
    if take is not None:
        values = values[:take]
    return [leaf(m, source) for m in values]


def power(p, tail, source):
    require(len(tail) == p-1, f'{source}: incomplete {p}-node nonzero children')
    return dict(kind='power', prime=p, tail=tail, source=source)


def build_tree():
    # Wedges are expanded in increasing BASE modulus order, before any
    # power substitution. Later power levels preserve those child positions.
    a13 = power(13, wedge((11,3,5),13,'F19 T1 left13 wedgeA')
                +wedge((11,3),7*13,'F19 T1 left13 wedgeB'), 'F19 T1 left13')
    b13 = power(13, wedge((11,3,5),13,'F19 T1 right13 wedgeA')
                +wedge((11,3),5*7*13,'F19 T1 right13 wedgeB'), 'F19 T1 right13')
    t1 = power(7, wedge((3,),7,'F19 T1 wedgeA')
               +wedge((3,),5*7,'F19 T1 wedgeB')+[a13,b13], 'F19 T1')
    a17 = power(17, wedge((11,3,5,7),17,'F20 T2 left17 wedge'), 'F20 T2 left17')
    c13 = power(13, wedge((11,3,5,7),19*13,'F20 T2 13 smallest12',take=12),
                'F20 T2 13')
    b17 = power(17, wedge((11,3,5,7),19*17,'F20 T2 right17 wedge'),
                'F20 T2 right17')
    p19 = power(19, [c13,b17]+wedge((11,3,5,7),19,'F20 T2 19 wedge'), 'F20 T2 19')
    t2 = power(7, wedge((3,),7,'F20 T2 wedgeA')
               +wedge((3,),5*7,'F20 T2 wedgeB')+[a17,p19], 'F20 T2')
    t3 = power(7, wedge((3,),7,'F21 T3 wedgeA')
               +wedge((3,),11*5*7,'F21 T3 wedgeB')
               +wedge((3,),11*7,'F21 T3 wedgeC'), 'F21 T3')
    t4 = power(7, wedge((3,),7,'F22 T4 wedgeA')
               +wedge((3,),5*7,'F22 T4 wedgeB')
               +wedge((3,),11*7,'F22 T4 wedgeC'), 'F22 T4')
    p5a = power(5, wedge((3,),5,'F18 root1 5 wedge')+[leaf(55,'F18 11*5'),t1],
                'F18 root1 5')
    p5b = power(5, wedge((3,),5,'F18 root2 5 wedge')+[leaf(165,'F18 11*3*5'),t2],
                'F18 root2 5')
    p5c = power(5, wedge((3,),5,'F18 root3 5 wedge')+[t3,t4], 'F18 root3 5')
    branches = [power(3,wedge((11,),3,'F18 root0 3 wedge'),'F18 root0 3'),
                power(3,[leaf(3,'F18 root1 3'),p5a],'F18 root1 3'),
                power(3,[leaf(3,'F18 root2 3'),p5b],'F18 root2 3'),
                power(3,[leaf(3,'F18 root3 3'),p5c],'F18 root3 3')]
    branches += [leaf(11,f'F18 pure11 root{r}') for r in range(4,11)]
    require(len(branches) == 11, 'incomplete Figure18 root')
    return dict(kind='root', prime=11, children=branches, source='F18')


def build_family():
    tree = build_tree()
    families = {}
    power_nodes = []
    leaf_occurrences = []
    closing_primes = set()

    def visit(node, digits, path):
        if node['kind'] == 'power':
            p = node['prime']
            require(p not in digits, 'same prime reappears on a symbolic path')
            require(p in POWER_PRIMES and len(node['tail']) == p-1,
                    'incomplete finite power branch')
            closing_primes.add(p)
            power_nodes.append(dict(source=node['source'], prime=p,
                                    height_range=[1,HEIGHT],
                                    nonzero_children=p-1,
                                    final_closing_children=CLOSING))
            for d, child in enumerate(node['tail'],1):
                visit(child,{**digits,p:d},
                      path+[(p,d)])
            return
        require(node['kind'] == 'leaf','unknown tree node')
        primes = support(node['modulus'])
        require(set(primes) <= set(digits), 'leaf factor is absent from its source path')
        key = (primes,tuple(digits[p] for p in primes))
        occurrence = dict(source=node['source'], path=[list(x) for x in path],
                          base_modulus=node['modulus'])
        leaf_occurrences.append(occurrence)
        if key not in families:
            families[key] = dict(primes=list(primes),
                                 digits={str(p):digits[p] for p in primes},
                                 exponent_ranges={str(p):([1,1] if p==ROOT else [1,HEIGHT])
                                                  for p in primes},
                                 tree_occurrences=[])
        families[key]['tree_occurrences'].append(occurrence)
    for r, child in enumerate(tree['children']):
        visit(child,{11:r},[(11,r)])
    require(closing_primes == set(POWER_PRIMES), 'wrong literal power-prime support')
    rows = sorted(families.values(),key=lambda row:(prod(row['primes']),row['primes'],
                                                   list(row['digits'].values())))
    shapes = {}
    for i,row in enumerate(rows):
        row['id'] = f'F{i:03d}'
        key=tuple(row['primes'])
        previous=shapes.setdefault(key,[])
        require(not previous or key==(11,), 'same numeric modulus family has different residues')
        previous.append(row)
        row['expanded_label_count'] = HEIGHT**sum(p!=ROOT for p in key)
    require(len(shapes[(11,)])==7,'wrong pure11 repetition count')
    # Distinct prime supports distinguish every other normal family. All
    # closing classes contain 23 and normal classes do not. Closing families
    # for different primes meet only at the single shared 0 mod23 class.
    require(all(CLOSING not in row['primes'] for row in rows),'normal label contains closing prime')
    def tree_leaves(node):
        if node['kind']=='leaf':
            return 1
        if node['kind']=='root':
            return sum(map(tree_leaves,node['children']))
        return CLOSING+HEIGHT*sum(map(tree_leaves,node['tail']))
    original_count=sum(row['expanded_label_count'] for row in rows)+1+len(POWER_PRIMES)*HEIGHT
    period_factors={str(p):(1 if p in (ROOT,CLOSING) else HEIGHT) for p in ALL_PRIMES}
    return dict(tree=tree, normal_families=rows,
                closing_families=[dict(prime=p, exponent_range=[1,HEIGHT],
                                       modulus='23*p^j',p_residue=0,q_residue='j')
                                  for p in POWER_PRIMES],
                shared_closing_class=[0,23], power_nodes=power_nodes,
                symbolic_leaf_occurrences=len(leaf_occurrences),
                expanded_tree_leaf_occurrences=tree_leaves(tree),
                expanded_original_label_count=original_count,
                period_factorization=period_factors,
                period=prod(p**int(period_factors[str(p)]) for p in ALL_PRIMES),
                pure11_roots=list(range(4,11)),nonpure_roots=list(range(4)),
                odd_nonunit=True,only_repeated_modulus=11,repeated_modulus_count=7,
                full_cover_certificate='complete finite prime-branch tree; each leaf AP contains its full path cylinder')


def local_height_digit(value,p):
    value %= p**HEIGHT
    if value==0:
        return None
    h=1
    while value%p==0:
        value//=p
        h+=1
    return h,value%p


def instantiate_normal(row, heights):
    residues={}
    moduli={}
    for p in row['primes']:
        d=int(row['digits'][str(p)])
        if p==ROOT:
            residues[p]=d
            moduli[p]=p
        else:
            h=heights[p]
            require(1<=h<=HEIGHT,'normal exponent outside literal power range')
            residues[p]=d*p**(h-1)
            moduli[p]=p**h
    a,m=crt_coordinates(residues,moduli)
    return dict(family=row['id'],residue=a,modulus=m,
                coordinates={str(p):[residues[p],moduli[p]] for p in row['primes']})


def active_classes(coordinates, family=None):
    if family is None:
        family=build_family()
    info={p:local_height_digit(coordinates[p],p) for p in POWER_PRIMES}
    active=[]
    for row in family['normal_families']:
        match=True
        heights={}
        for p in row['primes']:
            d=int(row['digits'][str(p)])
            if p==ROOT:
                match=coordinates[p]%p==d
            elif info[p] is None:
                match=False
            else:
                h,digit=info[p]
                match=digit==d
                heights[p]=h
            if not match:
                break
        if match:
            active.append(instantiate_normal(row,heights))
    j=coordinates[CLOSING]%CLOSING
    if j==0:
        active.append(dict(family='closing-common',residue=0,modulus=23))
    else:
        for p in POWER_PRIMES:
            if coordinates[p]%(p**j)==0:
                a,m=crt_pair(0,p**j,j,23)
                active.append(dict(family=f'closing-{p}',height=j,residue=a,modulus=m))
    return active


def tree_witness(coordinates, family):
    node=family['tree']['children'][coordinates[11]%11]
    heights={}
    while node['kind']=='power':
        p=node['prime']
        info=local_height_digit(coordinates[p],p)
        if info is None:
            j=coordinates[23]%23
            a,m=crt_pair(0,p**j,j,23)
            return a,m
        h,d=info
        heights[p]=h
        node=node['tail'][d-1]
    residue={}
    moduli={}
    for p in support(node['modulus']):
        moduli[p]=p if p==ROOT else p**heights[p]
        residue[p]=coordinates[p]%moduli[p]
    return crt_coordinates(residue,moduli)


def hole_after_deleting_G(root, family):
    # All chosen first digits are nonzero. Thus only height-one normal APs
    # can meet this cylinder, and no 23 closing AP meets it when x23=1.
    good=[]
    for row in family['normal_families']:
        primes=row['primes']
        if 3 in primes and 11 not in primes:
            continue
        if 11 in primes and int(row['digits']['11'])!=root:
            continue
        pattern={p:int(row['digits'][str(p)]) for p in primes if p!=11}
        good.append(pattern)
    variables=POWER_PRIMES
    def search(assigned, forbidden):
        live=[]
        for pattern in forbidden:
            if any(p in assigned and assigned[p]!=d for p,d in pattern.items()):
                continue
            if all(p in assigned for p in pattern):
                return None
            live.append(pattern)
        if len(assigned)==len(variables):
            return assigned
        p=next(p for p in variables if p not in assigned)
        for d in range(1,p):
            found=search({**assigned,p:d},live)
            if found is not None:
                return found
        return None
    digits=search({3:1},good)
    require(digits is not None, f'no G-deletion witness found in nonzero-digit search on root{root}')
    coords={**digits,11:root,23:1}
    active=active_classes(coords,family)
    require(bool(active),'reconstructed original cover misses its own search witness')
    require(all(item['modulus']%3==0 and item['modulus']%11!=0 for item in active),
            'claimed G-deletion hole is still covered by a retained original')
    a,m=crt_coordinates(coords,{p:p for p in ALL_PRIMES})
    require(all((a-item['residue'])%item['modulus']==0 for item in active),
            'literal witness does not meet reported original labels')
    return dict(root=root,first_digits={str(p):coords[p] for p in ALL_PRIMES},
                private_cylinder_residue=a,private_cylinder_modulus=m,
                cylinder_density=f'1/{m}',active_original_classes=active,
                whole_G_removed_uncovered=True,
                region_reason='all six power-prime first digits nonzero; only height-one normal labels can meet this entire cylinder, and no closing label can meet it')


def validate_tree_samples(family):
    rng=random.Random(210400602)
    values=[]
    for _ in range(1024):
        point={11:rng.randrange(11),23:rng.randrange(23)}
        for p in POWER_PRIMES:
            h=rng.randrange(1,HEIGHT+2)
            point[p]=0 if h==HEIGHT+1 else rng.randrange(1,p)*p**(h-1)
        values.append(point)
    # Explicit maximum-height and all-zero closing cases.
    values += [{**{p:p**(HEIGHT-1) for p in POWER_PRIMES},11:r,23:22}
               for r in range(4)]
    values += [{**{p:0 for p in POWER_PRIMES},11:r,23:j}
               for r in range(4) for j in range(23)]
    for point in values:
        a,m=tree_witness(point,family)
        actual=active_classes(point,family)
        require(any(item['residue']==a and item['modulus']==m for item in actual),
                'complete-tree covering witness is absent from canonical AP families')
    return len(values)


def main():
    family=build_family()
    family['source']='HSW arXiv:2104.00602v1, Theorem4.2, Figures18--22, printed pp11--12; tree conventions pp4--6'
    family['auxiliary_closing_prime']=23
    family['sampled_exact_tree_witness_checks']=validate_tree_samples(family)
    family['root_G_deletion_witnesses']=[hole_after_deleting_G(r,family) for r in range(4)]
    family['G_normal_family_count']=sum(3 in row['primes'] and 11 not in row['primes']
                                        for row in family['normal_families'])
    family['G_expanded_label_count']=sum(row['expanded_label_count'] for row in family['normal_families']
                                        if 3 in row['primes'] and 11 not in row['primes'])+HEIGHT
    print(json.dumps(family,sort_keys=True,indent=2))


if __name__=='__main__':
    main()
