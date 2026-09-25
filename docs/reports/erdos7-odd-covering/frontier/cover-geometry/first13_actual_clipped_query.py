#!/usr/bin/env python3
"""One fixed 51-cylinder query refutes the H5 uniform clipped-query cut.

Reconstruct the literal 70+200-original source. This is a query
counterexample, not an actual row13 loss or an odd covering system.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from math import lcm, prod
from pathlib import Path
import hashlib
import json
import re


# One global CRT phase per nonunit numerical cofactor. The unit is
# included separately, exactly once. Rows are (a,b,c,r5,r7,r11).
QUERY = (
    (0,0,1,0,0,9), (0,0,2,0,0,9),
    (0,1,0,0,6,0), (0,1,1,0,5,9), (0,1,2,0,5,53),
    (0,2,0,0,34,0), (0,2,1,0,6,1), (0,2,2,0,47,20),
    (0,3,0,0,41,0), (0,3,1,0,6,1), (0,3,2,0,47,31),
    (1,0,0,4,0,0), (1,0,1,4,0,9), (1,0,2,4,0,109),
    (1,1,0,3,6,0), (1,1,1,3,5,9), (1,1,2,4,3,109),
    (1,2,0,3,6,0), (1,2,1,4,3,5), (1,2,2,3,19,31),
    (1,3,0,3,48,0), (1,3,1,3,68,9), (1,3,2,3,19,20),
    (2,0,0,14,0,0), (2,0,1,19,0,0), (2,0,2,4,0,109),
    (2,1,0,15,6,0), (2,1,1,4,4,4), (2,1,2,4,3,53),
    (2,2,0,3,20,0), (2,2,1,4,3,5), (2,2,2,3,19,42),
    (2,3,0,3,13,0), (2,3,1,3,33,9), (2,3,2,3,19,64),
    (3,0,0,109,0,0), (3,0,1,74,0,0), (3,0,2,24,0,109),
    (3,1,0,20,6,0), (3,1,1,4,3,9), (3,1,2,4,3,20),
    (3,2,0,3,27,0), (3,2,1,124,27,5), (3,2,2,59,38,75),
    (3,3,0,9,4,0), (3,3,1,3,19,9), (3,3,2,3,19,75),
    (4,0,0,184,0,0), (4,0,1,49,0,0), (4,0,2,49,0,0),
    (4,1,0,45,6,0),
)
checks = {}


def check(name, value):
    if name in checks or not value:
        raise ValueError(name)
    checks[name] = True


def auxiliary(x, y):
    # All-height mean plus the low atoms: no geometric tail truncation.
    mass, mean, atoms = F(1), F(1), {1: F(1)}
    bound = x * y - F(1, 12)
    hinges = {}
    for p, total, cap in ((5,x,F(1)), (7,y,F(1)), (11,F(1),F(5,3)),
                          (13,F(1),F(3,2)), (17,F(1),F(2)),
                          (19,F(1),F(9,5))):
        if p >= 11:
            t = 2 if p <= 13 else 4
            hinges[p] = mean - t * mass + sum(
                (t-i)*w for i,w in atoms.items() if i < t)
            bound -= 2 * cap / (p-1) * hinges[p]
        low = {1: total-cap/p, 2: cap*(p-1)/p**2,
               3: cap*(p-1)/p**3}
        nxt = defaultdict(F)
        for i, w in atoms.items():
            for j, v in low.items():
                if i*j < 4:
                    nxt[i*j] += w*v
        mass *= total
        mean *= total + cap/(p-1)
        atoms = nxt
    phi = mean - 3*mass + sum((3-i)*w for i,w in atoms.items() if i < 3)
    return bound, phi, hinges


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path(__file__).resolve().parents[2]
                        / 'profile-notes/arithmetic/558-first-eleven-inventory-and-an-actual-phase-counterexample.md')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    pattern = re.compile(r'^\|\s*\((\d+),(\d+)\)\s*\|\s*\((\d+),(\d+),(\d+)\)\s*\|\s*\((\d+),(\d+),(\d+)\)\s*\|$')
    rows = [tuple(map(int, m.groups())) for line in args.source.read_text().splitlines()
            if (m := pattern.match(line))]
    check('literal25rows', len(rows) == 25 and
          {(r[0],r[1]) for r in rows} == set(product(range(5), repeat=2)))
    slots = [(a,b,*s) for a,b,*v in rows for s in (v[:3],v[3:])]
    for i,(a,b,r5,r7,g) in enumerate(slots):
        check('original_phase_'+str(i), 0 <= r5 < 5**a and 0 <= r7 < 7**b
              and 0 <= g < 10)
    check('query51_distinct', len(QUERY) == len({r[:3] for r in QUERY}) == 51)
    full_queries = []
    for i,row in enumerate(QUERY):
        exponents, phases = row[:3], row[3:]
        moduli = tuple(p**e for p,e in zip((5,7,11),exponents))
        check('query_phase_'+str(i), any(exponents) and
              all(0 <= r < m for r,m in zip(phases,moduli)))
        modulus = prod(moduli)
        residue = sum(r*(modulus//m)*pow(modulus//m,-1,m)
                      for r,m in zip(phases,moduli) if m > 1) % modulus
        check('query_crt_'+str(i), all(residue % m == r for m,r in zip(moduli,phases)))
        full_queries.append(dict(exponents=exponents, components=phases,
                                 modulus=modulus, residue=residue))

    # Compress only exact incidence signatures, retaining mixed-deletion
    # status, original colors and every fixed query phase jointly.
    coordinates = {}
    for axis,p in enumerate((5,7)):
        hist = Counter()
        for z in range(p**5):
            if any(z % p**e in (p**(e-1),2*p**(e-1)) for e in range(1,6)):
                continue
            mixed = any(z % p**e in tuple(j*p**(e-1) for j in
                        ((3,) if p == 5 else (3,4))) for e in range(1,6))
            originals = sum(1 << i for i,s in enumerate(slots)
                            if z % p**s[axis] == s[axis+2])
            queries = sum(1 << i for i,r in enumerate(QUERY)
                          if z % p**r[axis] == r[axis+3])
            hist[originals,queries,mixed] += 1
        check('pure_count_'+str(p), sum(hist.values()) == {5:1563,7:11205}[p])
        coordinates[p] = hist
    profiles = Counter()
    for (o5,q5,m5),n5 in coordinates[5].items():
        for (o7,q7,m7),n7 in coordinates[7].items():
            if m5 and m7:
                continue
            active = o5 & o7
            colors = 0
            while active:
                bit = active & -active
                colors |= 1 << slots[bit.bit_length()-1][4]
                active -= bit
            profiles[colors,q5&q7] += n5*n7
    period = 5**5 * 7**5
    oldmass = F(sum(profiles.values()),period)
    check('old_source_mass', oldmass == F(13138253,52521875))

    masks = {mask for mask,_ in profiles}
    allowed = {}
    eleven_period = 11**4
    for mask in sorted(masks):
        counts = [0]*121
        # Direct literal current11 comb membership, independent of the
        # closed formula for the 121-cell projection.
        for z in range(eleven_period):
            if not any(mask >> g & 1 and
                       any(z % 11**c == 11**(c-1)-1+g*11**(c-1)
                           for c in range(1,5)) for g in range(10)):
                counts[z % 121] += 1
        k = mask.bit_count()
        check('allowed_mass_'+str(mask), sum(counts) == eleven_period-1464*k)
        formula = [0 if mask >> (z%11) & 1 or
                   (z%11 == 10 and mask >> (z//11) & 1)
                   else 121-12*k if z == 120 else 121 for z in range(121)]
        check('allowed_projection_'+str(mask), counts == formula)
        allowed[mask] = counts
    factors = {k: min(F(5,3),F(eleven_period,eleven_period-1464*k))/eleven_period
               for k in {mask.bit_count() for mask in masks}}
    common = lcm(*(v.denominator for v in factors.values()))
    multipliers = {k: int(v*common) for k,v in factors.items()}
    denominator = period*common
    histogram = Counter()
    loads = {}
    for (mask,query_bits),count in profiles.items():
        if query_bits not in loads:
            load = [1]*121
            for i,(_,_,c,_,_,phase) in enumerate(QUERY):
                if query_bits >> i & 1:
                    for z in range(phase,121,11**c):
                        load[z] += 1
            loads[query_bits] = load
        factor = count*multipliers[mask.bit_count()]
        for load,n in zip(loads[query_bits],allowed[mask]):
            histogram[load] += factor*n
    masses = {k:F(n,denominator) for k,n in sorted(histogram.items()) if n}
    mass = sum(masses.values())
    clip = sum(w*min(F(1),F(max(k-2,0),4)) for k,w in masses.items())
    check('actual_lambda11_mass', mass == F(19543635187,92276732625))
    x,y = F(1563,3125),F(11205,16807)
    bound,phi,hinges = auxiliary(x,y)
    target = F(257,51)
    def gap(x,y):
        lower,phi,_ = auxiliary(x,y)
        return (target-2)*lower-phi
    basegap = gap(F(1,2),F(2,3))
    kreq = -basegap/(target-2)
    mixed = x*y-oldmass
    credit = (gap(x,y)-basegap)/(target-2)+F(1,12)-mixed
    saving11 = hinges[11]/3-oldmass+mass
    cut = credit+saving11+hinges[13]/4-kreq
    check('NC4_strict_hard_region', (target-2)*bound-phi < 0)
    check('exact_F13', hinges[13] == F(16293608641,83194650000))
    check('exact_cut', cut == F(649004327923538200529792761,
                              14267500448564292689760000000))
    check('fixed_query_above_cut', clip > cut)
    result = dict(scope=__doc__, source_sha256=hashlib.sha256(args.source.read_bytes()).hexdigest(),
                  old_originals=70, first11_originals=200, query_count=51, unit_count=1,
                  queries=full_queries, profiles=len(profiles), active_masks=len(masks),
                  x=x,y=y,oldmass=oldmass,lambda11=mass,credit=credit,S11=saving11,
                  F13=hinges[13],kreq=kreq,cut=cut,clip=clip,excess=clip-cut,
                  clip_decimal=float(clip),excess_decimal=float(clip-cut),
                  histogram=masses, checks=checks,check_count=len(checks))
    args.output.write_text(json.dumps(result,default=str,indent=2)+'\n')
    print('clip',clip,float(clip))
    print('cut',cut,float(cut))
    print('excess',clip-cut,float(clip-cut))
    print('checks',len(checks),'profiles',len(profiles))


if __name__ == '__main__':
    main()
