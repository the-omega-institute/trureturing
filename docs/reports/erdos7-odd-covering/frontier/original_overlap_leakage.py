"""Exact original-AP geometry checks for the quantitative FK leakage bound.

This validates finite fixtures and rational reductions. The published
Filaseta--Kalogirou Lemma3 numerical estimate is a literature input,
not recomputed by this program.
"""
from fractions import Fraction as F
from math import lcm
import random


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    rng = random.Random(731905)
    counts = dict(families=0, point_checks=0, strict_leakage_instances=0,
                  slack_checks=0, stage_identity_checks=0)
    p = 5
    old_mods = (3,9)
    current_mods = (5,15,45,25,75,225)
    M = F(3,4)
    for _ in range(400):
        old = [(rng.randrange(d),d) for d in old_mods if rng.randrange(2)]
        rows = [(rng.randrange(d),d) for d in current_mods if rng.randrange(2)]
        if not rows:
            continue
        mins = [(a,d) for a,d in rows
                if all(e == d or d % e != 0 for _,e in rows)]
        Q = lcm(1, *(d for a,d in old+rows))
        O = {x for x in range(Q) if any(x%d == a for a,d in old)}
        B = {x for x in range(Q) if any(x%d == a for a,d in rows)}
        Bmin = {x for x in range(Q) if any(x%d == a for a,d in mins)}
        E = {x for x in range(Q)
             if any(x%(d//p) == a%(d//p) for a,d in mins)}
        measure = lambda event: F(len(event),Q)
        S = sum((F(1,d) for a,d in rows),F(0))
        u,v = measure(Bmin&O), measure(B&O)
        r,U,Un = S-measure(B), 1-measure(O), 1-measure(O|B)
        eO,eR = measure(E&O), measure(E-O)
        require(eO <= p*u, 'Prime-prefix dilation')
        require(S <= M*measure(E), 'Upward ideal plus Rogers bound')
        delta,z,ell = p*u-eO, U-eR, M*measure(E)-S
        require(Un == (1-M)*U-p*M*u+v+r+M*delta+M*z+ell,
                'Exact signed slack identity')
        require(Un >= (1-M)*U-(p*M-1)*(r+v), 'Coarse leakage bound')
        counts['strict_leakage_instances'] += int(u > 0)
        counts['families'] += 1
        counts['point_checks'] += Q
        counts['slack_checks'] += 3
    for _ in range(150):
        rows = [(rng.randrange(d),d) for d in (3,5,9,15,25,45,75,225)
                if rng.randrange(2)]
        Q = lcm(1, *(d for a,d in rows))
        O,total = set(),F(0)
        for pp in (3,5):
            stage = [(a,d) for a,d in rows
                     if d%pp == 0 and not(pp == 3 and d%5 == 0)]
            B = {x for x in range(Q) if any(x%d == a for a,d in stage)}
            r = sum((F(1,d) for a,d in stage),F(0))-F(len(B),Q)
            v = F(len(B&O),Q)
            total += r+v
            O |= B
        excess = F(sum(max(0,sum(x%d == a for a,d in rows)-1)
                       for x in range(Q)),Q)
        require(total == excess, 'Each repeat charged exactly once')
        counts['stage_identity_checks'] += 1
    require(F(1,3) == 5*F(1,15),
            'Dilation factor p attained: old 0 mod3, current 0 mod15')
    # A literal private odd family forbids arbitrary source transport.
    p,oldperiod,M = 7,15**6,F(5,8)
    rows=[]
    for i in range(p):
        d = 3**i*5**(6-i)
        a = d*((i*pow(d,-1,p))%p)
        rows.append((a,p*d))
    for i in range(p):
        point = oldperiod*((i*pow(oldperiod,-1,p))%p)
        require([point%d == a for a,d in rows] == [i == j for j in range(p)],
                'Every source fixture label has an actual private point')
    # Sigma is old-coordinate delta_0 times Haar on the current coordinate.
    source_points = [oldperiod*((i*pow(oldperiod,-1,p))%p) for i in range(p)]
    source_sum = sum((F(sum(point%d == a for point in source_points),p)
                      for a,d in rows),F(0))
    expanded_mass = F(sum(any(point%(d//p) == a%(d//p) for a,d in rows)
                          for point in source_points),p)
    require(source_sum == expanded_mass == 1 and source_sum > M*expanded_mass,
            'The Haar denominator-ideal bound cannot be moved to an arbitrary old source')
    # Exact bridge from published Lemma3 and source equation(23).
    # e>8/3 follows from the first four exponential-series terms.
    N = 15320302*10**14
    require(N < F(8,3)**50, 'log N < 50')
    require(50 < F(8,3)**4, 'log log N < 4')
    require(F(107,2)*N < 10**23, 'Equation(23) gives p_N < 10^23')
    published_gap = F(47596769,10**57)
    require(published_gap/F(10**23) > F(1,10**73),
            'Published positive reserve divided by endpoint loss bound')
    require(93*F(5,10**52) < published_gap,
            'Published Euler product <94 yields the stronger 5e-52 gap')
    print(counts)
    print('PASS geometry, same-Haar repeat identity, source boundary and rational bridge')
    print('INPUTS NOT RECOMPUTED: published Lemma3 reserve > 4.7596769e-50 and page24 Euler product <94')


if __name__ == '__main__':
    main()
