#!/usr/bin/env python3
"""Exact controls for Q-dependent branch capacities and one actual finite family.

Python 3.9+ standard library only; floats are display-only. Place beside the
two pinned JSON inputs, or pass --source-dir from another directory.
Ordinary proofs supply arbitrary-source and all-height
quantifiers. The 40-original fixture fails the specified Report580 source gate and
separates the uniform no-loss fixed-clip budget from an adaptive budget;
it does not separate all older certificates or settle unrestricted Erdos7.
"""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import gcd, lcm, prod
from pathlib import Path
import json

DIGESTS = {
 'height_three_clipping_envelope.json': '276d7e266a86ed8e5a1c9da2982b219725c2738bc4ad19da1243bf8575543685',
 'four_level_query_hinge_lift.json': 'b224c79716585f16b52aeda277810a1a001a4f2d92d3e092cfc1cc41345dbcfd',
}
Q = (5, 7, 11, 13, 17, 19)
D = prod(Q)


def ex(x):
    x = F(x)
    return {'exact': str(x), 'decimal': float(x)}


def crt(a, m, b, n):
    if gcd(m, n) != 1:
        raise ValueError('noncoprime CRT input')
    return (a + m * (((b-a) * pow(m, -1, n)) % n)) % (m*n)


def main():
    ap = ArgumentParser(description=__doc__)
    ap.add_argument('--source-dir', type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = ap.parse_args()
    checks, provenance, sources = [], [], {}

    def need(name, condition):
        if not condition:
            raise ValueError('FAILED: '+name)
        checks.append(name)

    for name, digest in DIGESTS.items():
        raw = (args.source_dir/name).read_bytes()
        need('source digest '+name, sha256(raw).hexdigest() == digest)
        provenance.append({'path':name, 'sha256':digest})
        sources[name] = json.loads(raw)
    env = sources['height_three_clipping_envelope.json']
    fh = sources['four_level_query_hinge_lift.json']
    B, target = F(env['B']), F(env['target'])
    alpha = min(F(c['alpha']['exact']) for c in fh['corners'])
    kvals = [max(F(c['K_integer'][i]) for c in env['corners']) for i in range(8)]
    need('existing B and K3 agree', B == F(fh['B']['exact']) and kvals[3] == F(fh['K']['exact']))
    need('complete source mass corners agree', {F(c['alpha']) for c in env['corners']} == {F(c['alpha']['exact']) for c in fh['corners']})
    need('target is same 23/29 continuation target', target == F(566,49))
    need('six-prime product', D == 1616615)

    # One explicit selected PA source. The only nonproduct root step is at11.
    prefix = []
    for r5, r7 in product(range(2,5), range(2,7)):
        roots11 = [r for r in range(2,11) if not (r5 == r7 == r == 4)]
        need('actual row11 normalized '+str((r5,r7)), sum((F(1,len(roots11)) for _ in roots11),F(0)) == 1)
        need('actual row11 cap '+str((r5,r7)), F(11,len(roots11)) < F(5,3))
        for r11 in roots11:
            prefix.append(((r5,r7,r11), F(1,15*len(roots11))))
    need('134 actual source prefix atoms', len(prefix) == 134)
    need('actual source prefix mass one', sum((p for _,p in prefix),F(0)) == 1)
    for q, cap in ((13,F(3,2)),(17,F(2)),(19,F(9,5))):
        need('later actual row cap '+str(q), F(q,q-2) < cap)
    need('initial old-coordinate Haar mass', F(3,5)*F(5,7) == F(3,7))
    root11_2 = sum((p for roots,p in prefix if roots[2] == 2), F(0))
    need('actual eleventh-root2 marginal', root11_2 == F(121,1080))
    dist = defaultdict(F)
    for roots, p in prefix:
        dist[sum(r == 2 for r in roots)] += p
    for q in Q[3:]:
        nxt = defaultdict(F)
        for count,p in dist.items():
            nxt[count+1] += p/F(q-2)
            nxt[count] += p*F(q-3,q-2)
        dist = nxt
    rho = sum((F(k)*p for k,p in dist.items()), F(0))
    need('full A count law normalized', sum(dist.values(),F(0)) == 1)
    need('actual A source first moment', rho == F(174043,201960))
    all2 = F(1,15*9*11*15*17)
    need('all root2 source mass', all2 == F(1,378675))
    need('full A count law all2 mass', dist[6] == all2)
    for root in (2,3):
        prefix_mass = sum((p for roots,p in prefix if roots == (root,)*3),F(0))
        need('actual all-roots cylinder mass '+str(root),
             prefix_mass/F(11*15*17) == all2)

    # Compute this source's ACTUAL full-height query norm. The generic
    # supplier bound B is deliberately retained in the class-wide theorem;
    # it must not be mistaken for the exact norm of this finite fixture.
    source_projections = []
    prefix_query_sum = F(0)
    expected_maxima = {1:F(1),5:F(1,3),7:F(1,5),11:F(121,1080),
                       35:F(1,15),55:F(41,1080),77:F(5,216),385:F(1,120)}
    for mask in range(8):
        indices = [i for i in range(3) if mask & (1<<i)]
        projected = defaultdict(F)
        for roots,p in prefix:
            projected[tuple(roots[i] for i in indices)] += p
        modulus = prod(Q[i] for i in indices)
        maximum = max(projected.values())
        tail_weight = prod((F(Q[i],Q[i]-1) for i in indices),start=F(1))
        need('actual source projected maximum d='+str(modulus),maximum==expected_maxima[modulus])
        prefix_query_sum += maximum*tail_weight
        source_projections.append({'modulus':modulus,'maximum_mass':ex(maximum),
                                   'all_height_weight':ex(tail_weight)})
    independent_tail_factor = prod((1+F(q,(q-1)*(q-2)) for q in Q[3:]),start=F(1))
    actual_RQ = prefix_query_sum*independent_tail_factor-1
    actual_fixed_bound = actual_RQ+F(487,444)*(1+actual_RQ)
    need('actual source complete finite-head query sum',prefix_query_sum==F(509519,259200))
    need('actual source remaining independent coordinate factor',independent_tail_factor==F(2422225,1938816))
    need('actual source exact full-height query norm',actual_RQ==F(29265142103,20101644288))
    need('actual source supports a successful older fixed-root certificate',
         actual_fixed_bound==F(37035348066149,8925130063872) and actual_fixed_bound<target)

    def new_original(e,d,t,r,label):
        m = 3**e*d
        phase = r % d if e == 0 else (t % (3**e) if d == 1 else crt(t,3**e,r,d))
        return {'e':e,'d':d,'t':t,'r':r,'label':label,'m':m,'phase':phase}

    def base():
        rows = [new_original(1,1,1,0,'pure3'),new_original(2,1,3,0,'pure9')]
        for q in Q:
            rows.extend((new_original(0,q,0,0,'q'+str(q)+'e0'),new_original(1,q,2,1,'q'+str(q)+'e1')))
        rows.append(new_original(0,385,0,4,'Q385'))
        return rows

    family40 = base()
    for q,t in zip(Q,(0,6,9,15,18,24)):
        family40.append(new_original(4,q,t,2,'Aq'+str(q)))
    for j,(e,t) in enumerate(((5,27),(5,33),(6,36),(6,42))):
        family40.append(new_original(e,D*5**j,t,2,'Adeep'+str(j)))
    for j in range(13):
        family40.append(new_original(4,D*5**(j+4),2+3*j,3,'B'+str(j)))
    family40.append(new_original(5,D*5**17,41,3,'B13'))
    family40.append(new_original(6,D*5**18,44,3,'B14'))

    def original_point(o, family, level):
        # The high-power fifth coordinate is explicitly represented, not sampled.
        roots = {q:3 for q in Q}
        t = o['t']
        if o['label'] == 'Q385':
            roots.update({5:4,7:4,11:4})
            t = 0
        elif o['d'] in Q:
            roots[o['d']] = o['r']
        elif o['d'] > 385:
            roots = {q:o['r'] for q in Q}
        max5 = max(valuation(r['d'],5) for r in family)
        value, modulus = t % (3**level), 3**level
        for q in Q:
            power = q**max5 if q == 5 else q
            value = crt(value,modulus,roots[q],power)
            modulus *= power
        return value, modulus

    def valuation(n,p):
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        return e

    def audit_family(name, family, level, expected, a_max, b_max):
        need(name+' original count', len(family) == expected)
        need(name+' distinct odd nonunit labels', len({o['m'] for o in family}) == expected and all(o['m'] > 1 and o['m'] % 2 for o in family))
        need(name+' exactly two pure3 originals', [(o['m'],o['phase']) for o in family if o['d']==1] == [(3,1),(9,3)])
        selections = {q:{0,1} for q in Q}
        selections[385] = {4}
        need(name+' one through3 selected source', all(o['r'] % o['d'] in selections.get(o['d'],set()) for o in family if o['d'] > 1 and o['e'] <= 3))
        witnesses = []
        for o in family:
            x,period = original_point(o,family,level)
            hits = [r['label'] for r in family if x % r['m'] == r['phase']]
            need(name+' private CRT '+o['label'], hits == [o['label']])
            witnesses.append({'label':o['label'],'point':str(x),'period':str(period)})
        a_rows = [o for o in family if o['e'] >= 4 and o['t']%9 in (0,6)]
        b_rows = [o for o in family if o['e'] >= 4 and o['t']%3 == 2]
        need(name+' actual branch original counts', len(a_rows)==a_max and len(b_rows)==b_max)
        need(name+' disjoint A ternary cylinders', all((u['t']-v['t']) % (3**min(u['e'],v['e'])) != 0 for i,u in enumerate(a_rows) for v in a_rows[i+1:]))
        need(name+' disjoint B ternary cylinders', all((u['t']-v['t']) % (3**min(u['e'],v['e'])) != 0 for i,u in enumerate(b_rows) for v in b_rows[i+1:]))
        need(name+' A incidences exclude every B incidence', all(o['r']==2 for o in a_rows) and all(o['r']==3 and o['d']%D==0 for o in b_rows) and all(o['d'] in Q or o['d']%D==0 for o in a_rows))
        # Two explicit positive source cylinders, and exact fibre union masks.
        extrema = []
        for root, desired in ((2,'A'),(3,'B')):
            high_rows = a_rows if root == 2 else b_rows
            qperiod = lcm(*(o['d'] for o in high_rows))
            live = []
            for t in range(3**level):
                if not any(t % (3**o['e']) == o['t'] % (3**o['e']) and (o['d']==1 or root % o['d'] == o['r'] % o['d']) for o in family):
                    live.append(t)
            cA = F(sum(t%9 in (0,6) for t in live),2*3**(level-2))
            cB = F(sum(t%3 == 2 for t in live),3**(level-1))
            mass = all2/F(qperiod//D)
            need(name+' positive extreme '+desired, mass > 0 and qperiod % D == 0)
            extrema.append({'branch':desired,'Q_phase':root,'Q_period':str(qperiod),'source_mass':ex(mass),'cA':ex(cA),'cB':ex(cB)})
        need(name+' A extreme exact survival', F(extrema[0]['cA']['exact']) == 1-sum((F(9,2*3**o['e']) for o in a_rows),F(0)) and F(extrema[0]['cB']['exact']) == 1)
        need(name+' B extreme exact survival', F(extrema[1]['cA']['exact']) == 1 and F(extrema[1]['cB']['exact']) == 1-sum((F(3,3**o['e']) for o in b_rows),F(0)))
        yA = sum((F(54,3**o['e']) for o in a_rows),F(0))
        yB = sum((F(54,3**o['e']) for o in b_rows),F(0))
        return {'original_count':len(family),'originals':family,'private_CRT_witnesses':witnesses,'extreme_fibres':extrema,'YA_max':ex(yA),'YB_max':ex(yB),'pointwise_total_max':ex(max(yA,yB))}

    fixtures = {'40_originals':audit_family('40',family40,6,40,10,15)}
    need('40 actual load maxima', F(fixtures['40_originals']['YA_max']['exact'])==F(124,27) and F(fixtures['40_originals']['YB_max']['exact'])==F(242,27))
    need('40 load domain', F(124,27)<=F(93,20) and F(242,27)<=9)
    need('40 has same actual fourth-layer A law', [(o['d'],o['r']) for o in family40 if o['e']==4 and o['t']%9 in (0,6)]==[(q,2) for q in Q])

    def capacity_record(name,M,lam,load_vertices):
        need(name+' cap parameters', F(1,2)<=M<=1 and lam>0)
        controls = []
        for yA,yB in load_vertices:
            cA,cB = 1-yA/12,1-yB/18
            aB = min(M,18*lam*cB)
            aA = 1-aB
            need(name+' capacity corner '+str((yA,yB)), min(M,12*lam*cA)+min(M,18*lam*cB)>=1 and 0<aA<=M and 0<aB<=M and aA<=12*lam*cA and aB<=18*lam*cB)
            controls.append({'YA':ex(yA),'YB':ex(yB),'cA':ex(cA),'cB':ex(cB),'aA':ex(aA),'aB':ex(aB)})
        for h in (2,4,6,12,30):
            need(name+' all-height query sum '+str(h), sum((54*lam/F(3**e) for e in range(2,h+1)),F(0))+27*lam/F(3**h)==9*lam)
            need(name+' equal deep cylinder coefficients '+str(h),F(9,2)*12*lam/F(3**h)==3*18*lam/F(3**h))
        coefficient = M+9*lam
        N = B+coefficient*(1+B)
        density = 486*lam/alpha
        haar = alpha*(566-49*N)/(486*lam*616)
        need(name+' strict all-height query gate',N<target)
        need(name+' density from disjoint roots',density==9/alpha*F(9,2)*12*lam and density==9/alpha*3*18*lam)
        need(name+' continuation uses same joint law',haar==((566-49*N)/567)/(density*F(616,567)) and haar>0)
        return {'M':ex(M),'lambda':ex(lam),'coefficient':ex(coefficient),'query_upper':ex(N),'query_margin':ex(target-N),'density_upper':ex(density),'full_survivor_Haar_lower':ex(haar),'capacity_vertices':controls}

    capacities = {
      'M3_5_lambda1_20':capacity_record('old capacity',F(3,5),F(1,20),[(F(0),F(0)),(F(4),F(0)),(F(4),F(6)),(F(0),F(10))]),
      'M13_20_lambda1_21':capacity_record('new capacity',F(13,20),F(1,21),[(F(0),F(0)),(F(93,20),F(0)),(F(93,20),F(87,20)),(F(0),F(9))]),
      '40_tight_envelope':capacity_record('40 tight envelope',F(46,71),F(27,568),[(F(0),F(0)),(F(124,27),F(0)),(F(124,27),F(118,27)),(F(0),F(242,27))]),
    }
    # Include zero reserves, saturation boundaries and infeasible capacities.
    capacity_controls = 0
    for M,lam,cA,cB in product((F(1,2),F(3,5),F(1)),
                               (F(0),F(1,30),F(1,21),F(1,12)),
                               (F(0),F(1,2),F(1)),(F(0),F(1,2),F(1))):
        capA,capB = min(M,12*lam*cA),min(M,18*lam*cB)
        feasible = capA+capB>=1
        linear = (12*lam*cA>=1-M and 18*lam*cB>=1-M and
                  lam*(12*cA+18*cB)>=1)
        if feasible != linear:
            raise ValueError('capacity equivalence control failed')
        if feasible and not (0<=1-capB<=capA and 0<=capB<=1 and
                             (cA>0 or 1-capB==0) and (cB>0 or capB==0)):
            raise ValueError('zero-reserve allocation control failed')
        capacity_controls += 1
    need('capacity equivalence and zero reserve controls',capacity_controls==108)
    # Full geometric branch-load completion, independently of the fixture heights.
    for h in (4,5,6,12,30):
        need('all original-height load weights '+str(h),sum((F(54,3**e) for e in range(4,h+1)),F(0))+F(1,3**(h-3))==1)

    def fixed_clip_opt(cA,cB):
        u,v = F(3,4)/cA,F(1,2)/cB
        vertices = (F(0),F(1,2),F(1),v/(u+v))
        values = [(max(w,1-w)+max(u*w,v*(1-w)),w) for w in vertices]
        coeff,w = min(values)
        return {'cA':ex(cA),'cB':ex(cB),'weight_A':ex(w),'coefficient':ex(coeff),'query_upper':ex(B+coeff*(1+B)),'piecewise_breakpoints':[ex(w) for w in sorted(set(vertices))]}
    fixed = {
      '40_originals':fixed_clip_opt(F(50,81),F(122,243)),
      'full_new_load_domain':fixed_clip_opt(F(49,80),F(1,2)),
    }
    need('40 uniform no-loss clip budget fails gate',F(fixed['40_originals']['coefficient']['exact'])==F(487,444) and F(fixed['40_originals']['query_upper']['exact'])>target)
    need('new domain uniform no-loss clip budget fails gate',F(fixed['full_new_load_domain']['coefficient']['exact'])==F(120,109) and F(fixed['full_new_load_domain']['query_upper']['exact'])>target)

    # The two minima are reached at different actual fibres. These extrema
    # and disjointness establish the whole finite family, not sampled points.
    reserve_a,reserve_b,beta = F(200,27),F(244,27),F(568,27)
    reserve_r = min(reserve_a,reserve_b)
    adaptive_coefficient = 1+(9-reserve_r)/beta
    fixed_coefficient = 1+(9-reserve_r)/(reserve_a+reserve_b)
    need('40 exact minimum common-fibre reserve',
         beta == 30-max(F(124,27),F(242,27)) and beta>reserve_a+reserve_b)
    need('40 analytic adaptive attainer',
         1-reserve_r/beta == F(46,71) and 1/beta == F(27,568) and
         adaptive_coefficient == F(611,568))
    need('40 analytic constant-root attainer',
         reserve_a/(reserve_a+reserve_b) == F(50,111) and
         fixed_coefficient == F(487,444))
    need('40 retained correlation gain',
         fixed_coefficient-adaptive_coefficient ==
         (9-reserve_r)*(beta-reserve_a-reserve_b)/(beta*(reserve_a+reserve_b)) ==
         F(1333,63048))
    need('new sufficient class continuation bound exceeds one over 40000',
         F(capacities['M13_20_lambda1_21']['full_survivor_Haar_lower']['exact'])>F(1,40000))
    need('optimized actual family continuation bound exceeds one over 32000',
         F(capacities['40_tight_envelope']['full_survivor_Haar_lower']['exact'])>F(1,32000))

    # Degenerate, balanced and unequal-reserve cases of the ordinary
    # piecewise-affine optimizer. This does not optimize actual query laws.
    optimizer_cases = []
    for ca,cb,joint in ((F(0),F(0),F(12)),(F(0),F(6),F(6)),
                       (F(6),F(8),F(18)),(F(9),F(12),F(24)),
                       (F(10),F(12),F(24)),(F(12),F(18),F(30)),
                       (reserve_a,reserve_b,beta)):
        r = min(ca,cb)
        need('optimizer consistent reserves '+str((ca,cb,joint)),
             0<=ca<=12 and 0<=cb<=18 and ca+cb<=joint<=min(ca+18,12+cb))
        M,lam = ((1-r/joint,1/joint) if r<=9 else (F(1,2),1/(2*r)))
        C = (1+(9-r)/joint if r<=9 else F(1,2)+F(9,2)/r)
        need('optimizer attainer '+str((ca,cb,joint)),
             F(1,2)<=M<=1 and lam*ca>=1-M and lam*cb>=1-M and
             lam*joint>=1 and M+9*lam==C)
        candidates = (F(1),) if r==0 else (F(1,2),1-r/joint,F(1))
        need('optimizer covers every affine breakpoint '+str((ca,cb,joint)),
             all(m+9*max((1-m)/r,1/joint)>=C for m in candidates) if r else M==1)
        optimizer_cases.append({'a':ex(ca),'b':ex(cb),'beta':ex(joint),
                                'M':ex(M),'lambda':ex(lam),'coefficient':ex(C)})

    # 580's specific Gamma gate, for the SAME explicitly selected PA source.
    N580 = B+F(10,11)*(1+B)
    gamma_star = 22*(1-N580/target)-kvals[7]
    rho_star = 33*(1-N580/target-kvals[3]/66-kvals[7]/22)
    need('40 rho exceeds specific 580 first-moment gate',rho>rho_star)
    dominant = max(range(len(env['corners'])),key=lambda j:F(env['corners'][j]['K_integer'][0]))
    need('same K corner dominates at all four integer endpoints',all(F(env['corners'][dominant]['K_integer'][i])==kvals[i] for i in range(4)))
    gamma_rows = []
    for s in (F(0),F(1,2),F(1),F(3,2)):
        hinge = sum((max(F(k)-s,F(0))*p for k,p in dist.items()),F(0))
        gamma = F(2,3)*hinge+kvals[int(3-2*s)]/3
        need('40 complete Gamma test fails at s='+str(s),gamma>gamma_star)
        gamma_rows.append({'s':ex(s),'hinge':ex(hinge),'Gamma':ex(gamma),'margin_above_gate':ex(gamma-gamma_star)})

    # A finite INTEGER same-source moment relaxation, explicitly not an
    # actual congruence family, also obstructs lossy uniform-cap allocation.
    p = kvals[3]/3
    aux_charge = F(81,74)*(1+B)
    aux_barrier = B+aux_charge
    need('auxiliary atom probability and first moment',0<p<1 and 6*p<B)
    need('same K corner controls all integer auxiliary knots',
         all(F(env['corners'][dominant]['K_integer'][i])==kvals[i] for i in range(7)))
    need('auxiliary integer layers obey complete K spectrum',
         all(kvals[i]>=p*max(6-i,0) for i in range(7)))
    need('auxiliary adaptive dual has positive slack',p*aux_barrier>aux_charge)
    need('auxiliary adaptive certificate barrier exceeds target',aux_barrier>target)
    aux_controls = 0
    for M,lam in product((F(0),F(1,4),F(1,2),F(3,5),F(27,37),F(9,10),F(1)),
                         (F(0),F(1,60),F(1,40),F(3,74),F(1,20),F(1,10),F(1))):
        v = min(F(1),min(M,F(20,3)*lam)+min(M,18*lam))
        s_zero = min(F(1),min(M,12*lam)+min(M,18*lam))
        mass = p*v+(1-p)*s_zero
        N = B+(M+9*lam)*(1+B)
        if not (M+9*lam>=F(81,74)*v and
                N-aux_barrier*mass>=(p*aux_barrier-aux_charge)*(1-v)>=0):
            raise ValueError('auxiliary adaptive dual control failed')
        aux_controls += 1
    need('auxiliary dual rational controls',aux_controls==49)
    need('auxiliary point-law attainer',
         F(27,37)+9*F(3,74)==F(81,74) and
         min(F(27,37),F(20,3)*F(3,74))+min(F(27,37),18*F(3,74))==1 and
         min(F(27,37),12*F(3,74))+min(F(27,37),18*F(3,74))>=1)

    output = {
      'schema':'adaptive-branch-capacity-exact-v1',
      'scope':['Ordinary conditional theorem; no new Lean or unrestricted Erdos7 claim.',
               'One displayed selected PA source, fixed global phases and distinct numerical labels.',
               '40-family Gamma separation concerns only the specified 580 gate, not all possible spare-phase selectors.',
               'The coefficient separation uses the same generic supplier B; using actual R_Q lets the older fixed-root bound pass.',
               'Fixed-clip separation concerns the uniform no-loss bound, not every older method or actual-law impossibility.'],
      'sources':provenance,'B':ex(B),'alpha':ex(alpha),'target':ex(target),
      'actual_source':{'prefix_atoms':len(prefix),'root11_2':ex(root11_2),'all_roots2_mass':ex(all2),
        'A_count_law':{str(k):ex(p) for k,p in sorted(dist.items())},
        'head_query_projections':source_projections,'exact_RQ':ex(actual_RQ),
        'successful_fixed_root_bound_using_actual_RQ':ex(actual_fixed_bound)},
      'capacities':capacities,'fixed_no_loss_clip_controls':fixed,'fixtures':fixtures,
      'analytic_optimizer_controls':optimizer_cases,
      'capacity_equivalence_control_count':capacity_controls,
      'auxiliary_integer_moment_obstruction':{'actual_arithmetic_realization':False,
        'event_probability':ex(p),'YA_on_event':ex(F(16,3)),
        'active_layers':{'A4':6,'A5':6},'raw_coefficient_barrier':ex(F(81,74)),
        'query_certificate_barrier':ex(aux_barrier),
        'margin_above_target':ex(aux_barrier-target),'rational_controls':aux_controls},
      'same_source_580_gate':{'rho_A':ex(rho),'rho_star':ex(rho_star),'rho_margin':ex(rho-rho_star),'Gamma_star':ex(gamma_star),'dominant_K_corner':dominant,'endpoints':gamma_rows},
      'check_count':len(checks),'checks':checks,
    }
    args.output.write_text(json.dumps(output,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'checks':len(checks),'output':str(args.output),'query_old':capacities['M3_5_lambda1_20']['query_upper'],'query_new':capacities['M13_20_lambda1_21']['query_upper'],'families':[40]},sort_keys=True))


if __name__ == '__main__':
    main()
