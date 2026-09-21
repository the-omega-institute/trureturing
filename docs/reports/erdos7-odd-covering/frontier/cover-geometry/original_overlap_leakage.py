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
                  slack_checks=0, stage_identity_checks=0,
                  stage_period_points=0, localized_recurrence_checks=0,
                  prime_collision_checks=0, odd_ideal_checks=0,
                  odd_localized_recurrence_checks=0)
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
        require(Un >= (1-M)*U-(p*M-1)*u+(v-u)+r,
                'Only minimal-class cross-prime overlap pays the loss')
        require(Un >= (1-M)*U-(p*M-1)*v+r,
                'Internal bucket excess is a favorable correction')
        odd_M = M/2
        odd_ell = odd_M*measure(E)-S
        require(odd_ell >= 0, 'Odd upward ideal omits exactly the factor at 2')
        require(Un == (1-odd_M)*U-p*odd_M*u+v+r
                +odd_M*delta+odd_M*z+odd_ell,
                'Odd-only original-Haar signed slack identity')
        require(Un >= (1-odd_M)*U-(p*odd_M-1)*u+(v-u)+r,
                'Odd-only minimal-class cross-prime leakage bound')
        counts['odd_ideal_checks'] += 1
        counts['strict_leakage_instances'] += int(u > 0)
        counts['families'] += 1
        counts['point_checks'] += Q
        counts['slack_checks'] += 3
    for _ in range(150):
        rows = [(rng.randrange(d),d)
                for d in (3,5,7,9,15,21,25,35,45,63,75,105,175,225,315)
                if rng.randrange(2)]
        Q = lcm(1, *(d for a,d in rows))
        O,total = set(),F(0)
        cross,internal,minimal = F(0),F(0),F(0)
        prime_unions=[]
        localized_events=set()
        lower=F(0)
        prefix_factor=F(1)
        odd_lower=F(0)
        odd_prefix_factor=F(1)
        for pp in (3,5,7):
            stage = [(a,d) for a,d in rows
                     if d%pp == 0 and all(d%qq != 0 for qq in (3,5,7) if qq > pp)]
            B = {x for x in range(Q) if any(x%d == a for a,d in stage)}
            r = sum((F(1,d) for a,d in stage),F(0))-F(len(B),Q)
            v = F(len(B&O),Q)
            total += r+v
            cross += v
            internal += r
            if pp > 3:
                mins = [(a,d) for a,d in stage
                        if all(e == d or d % e != 0 for _,e in stage)]
                Bmin = {x for x in range(Q) if any(x%d == a for a,d in mins)}
                u = F(len(Bmin&O),Q)
                localized_events |= Bmin&O
                minimal += u
                coefficient = {5: F(3,4), 7: F(5,8)}[pp]
                lower = (1-coefficient)*lower-(pp*coefficient-1)*u+(v-u)+r
                prefix_factor *= 1-coefficient
                require(F(Q-len(O|B),Q) >= lower,
                        'Iterated minimal-class budget with rebates')
                odd_coefficient = coefficient/2
                odd_lower = ((1-odd_coefficient)*odd_lower
                             -(pp*odd_coefficient-1)*u+(v-u)+r)
                odd_prefix_factor *= 1-odd_coefficient
                require(F(Q-len(O|B),Q) >= odd_lower,
                        'Odd-only iterated minimal-class budget')
                require(odd_prefix_factor**2 >= prefix_factor,
                        'Odd prefix product dominates the full product square root')
                counts['localized_recurrence_checks'] += 1
                counts['odd_localized_recurrence_checks'] += 1
            O |= B
            prime_unions.append(B)
            if pp == 3:
                initial = lower = odd_lower = F(Q-len(O),Q)
        excess = F(sum(max(0,sum(x%d == a for a,d in rows)-1)
                       for x in range(Q)),Q)
        prime_overlap = F(sum(max(0,sum(x in B for B in prime_unions)-1)
                              for x in range(Q)),Q)
        inside_overlap = F(sum(sum(x%d == a for a,d in rows)
                               -sum(x in B for B in prime_unions)
                               for x in range(Q)),Q)
        require(total == excess, 'Each repeat charged exactly once')
        require(cross == prime_overlap and internal == inside_overlap,
                'Cross-prime and within-bucket pointwise decomposition')
        require(minimal <= cross <= excess,
                'Localized minimal-class budget is no larger than total excess')
        require(F(Q-len(O),Q) >= initial*prefix_factor-(7*F(5,8)-1)*minimal,
                'Uniform endpoint coefficient for the minimal-class budget')
        require(F(Q-len(O),Q) >= initial*odd_prefix_factor-(7*F(5,16)-1)*minimal,
                'Odd-only uniform endpoint coefficient')
        require(minimal <= 2*F(len(localized_events),Q),
                'Event union controls a sum with two eligible prime stages')
        counts['stage_identity_checks'] += 1
        counts['prime_collision_checks'] += 1
        counts['stage_period_points'] += Q
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
    require((N-3)*F(1,10**64) < F(2,10**43),
            'Minimal-class overlap sum forces union mass greater than 1e-64')
    # Section 7: a smooth reciprocal tail cannot carry the new overlap union.
    P, tilt, degree, cutoff_power = 25*10**9, F(13,5), 5, 69
    require(1 < tilt < 3 < P < N+1,
            'Tilt converges at every odd prime; P is below the cited p_N')
    require(sum((F(2,3)**j for j in range(degree)), F(0)) == F(211,81),
            'Exact five-term lower bound for the Bernoulli comparison')
    require(tilt < F(211,81), 'Tilt is bounded by the five-term sum')
    smooth_tail_upper = 47**degree / tilt**cutoff_power
    require(smooth_tail_upper < F(1,10**20),
            'Original smooth reciprocal tail is smaller than the forced overlap union')
    require(P**cutoff_power < 10**718,
            'Both members of the required intersecting pair are below 10^718')
    print(counts)
    print('PASS geometry, cross-prime budgets, localized recurrence, source boundary, rational bridge and bounded-pair tail')
    print('INPUTS NOT RECOMPUTED: published Lemma3 reserve > 4.7596769e-50 and page24 Euler product <94')


if __name__ == '__main__':
    main()
