#!/usr/bin/env python3
"""Exact controls for joint damaged ternary reserves with all original heights.

The proof retains one actual selected PA source and every alternative query
layout. Finite arithmetic controls do not establish these universal quantifiers.
No new Lean verification or unrestricted Erdos7 conclusion is claimed.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path
import json

SOURCE_NAME = 'pa_complete_suffix_debits.json'
SOURCE_SHA256 = 'b1b204f8728c64ed9265e91d78d3072a2e77f64f6efca57512f3e58f0bdf3ccc'
ENVELOPE_NAME = 'height_three_clipping_envelope.json'
ENVELOPE_SHA256 = '276d7e266a86ed8e5a1c9da2982b219725c2738bc4ad19da1243bf8575543685'
Q = (5, 7, 11, 13, 17, 19)


def ex(value):
    value = F(value)
    return {'exact': str(value), 'decimal': float(value)}


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = []

    def need(name, condition):
        if not condition:
            raise ValueError('FAILED: ' + name)
        checks.append(name)

    raw = (args.source_dir / SOURCE_NAME).read_bytes()
    need('source SHA256 ' + SOURCE_NAME, sha256(raw).hexdigest() == SOURCE_SHA256)
    source = json.loads(raw)
    envelope_raw = (args.source_dir / ENVELOPE_NAME).read_bytes()
    need('source SHA256 ' + ENVELOPE_NAME,
         sha256(envelope_raw).hexdigest() == ENVELOPE_SHA256)
    envelope = json.loads(envelope_raw)
    B = F(source['joint_bound'])
    alpha = min(F(c['alpha']) for c in source['corners'])
    target = F(566, 49)
    K2 = B - 2
    K3 = max(F(c['K_integer'][3]) for c in envelope['corners'])
    K7 = max(F(c['K_integer'][7]) for c in envelope['corners'])
    need('same old-method envelope supplier', F(envelope['B']) == B)
    need('same full query supplier',
         B == F(432040125182653876501, 86355045355449035400))
    need('same density denominator',
         alpha == F(7575003978548161, 73724315753088000))
    need('second hinge is supplier proof coefficient',
         K2 == F(259330034471755805701, 86355045355449035400))
    zeta0 = F(source['suffixes'][0]['zeta'])
    need('second hinge exceeds full leading suffix', K2 >= zeta0)
    corner_data = []
    for corner in source['corners']:
        name = '(' + corner['x'] + ',' + corner['y'] + ')'
        a = F(corner['alpha'])
        phi = F(corner['Phi'])
        debit = F(corner['deletion'])
        joint = F(corner['J'])
        need('positive mass at ' + name, a > 0)
        need('joint cap sum at ' + name,
             joint == sum((F(s['J']) for s in corner['stages']), F(0)))
        quotient = 2 + (phi - debit - joint) / a
        need('unchanged SD10 quotient at ' + name,
             quotient == F(corner['joint_bound']))
        margin = K2 * a - phi + debit + joint
        need('SD10 full hinge corner nonnegative ' + name, margin >= 0)
        corner_data.append({'x': corner['x'], 'y': corner['y'],
                            'hinge_margin': ex(margin),
                            'query_quotient': ex(quotient)})
    for index, row in enumerate(source['coefficients']):
        suffix = F(row['zeta'])
        eta = F(row['eta'])
        cap = F(row['cap'])
        previous = F(source['suffixes'][index]['zeta'])
        need('suffix-cap identity at ' + str(row['q']),
             previous == suffix + cap * eta)
        need('SD9 convex penalty slope at ' + str(row['q']),
             K2 - suffix >= cap * eta)
    need('unit shifts third hinge to nonunit second hinge',
         all(max((n + 1) - 3, 0) == max(n - 2, 0)
             for n in range(12)))

    for height in (2, 3, 6, 12):
        need('full deep query geometric tail ' + str(height),
             sum((F(9, 4 * 3**e) for e in range(2, height + 1)), F(0))
             + F(9, 8 * 3**height) == F(3, 8))
        need('full original incidence geometric tail ' + str(height),
             sum((F(54, 3**e) for e in range(4, height + 4)), F(0))
             + F(1, 3**height) == 1)
    need('disjoint roots have the same deep coefficient',
         F(1, 2) * F(9, 2) == F(3, 4) * 3 == F(9, 4))
    need('root and complete deep coefficients', F(1, 2) + F(3, 8) == F(7, 8))
    need('joint-load coefficients match reserve condition',
         F(2, 12) == F(3, 18) == F(1, 6))
    # Boundary controls for the actual joint capacity domain. The proof covers
    # all real reserves; these rational cases check limiting and interior use.
    for ca in (F(1, 2), F(5, 9), F(2, 3), F(3, 4), F(1)):
        cbmin = (4 - 2 * ca) / 3
        for cb in (cbmin, (cbmin + 1) / 2, F(1)):
            aa = ca / 2
            ab = 1 - aa
            key = str(ca) + ',' + str(cb)
            need('normalized fibre mass ' + key,
                 (aa / ca) * ca + (ab / cb) * cb == 1)
            need('joint capacity deep B cap ' + key, ab / cb <= F(3, 4))
            need('root B weighted identity ' + key, ab == F(1, 2) + (1-ca)/2)

    u = F(16, 3)
    h = u / 24
    mean = B / 24
    base = B + F(7, 8) * (1 + B)
    R = base + h * K2 + 3 * mean
    need('load cap yields five-ninths reserve', 1-u/12 == F(5, 9))
    need('weight cap is two ninths', h == F(2, 9))
    need('all-height budget identity', R == 2*B + F(7, 8) + u*K2/24)
    need('exact all-height joint budget',
         R == F(1795085660881088508439, 155439081639808263720))
    need('strict nine-prime continuation gate', R < target)
    density = F(81, 4) / alpha
    haar = alpha * (566 - 49*R) / 12474
    need('unchanged density from disjoint roots', density == F(9, 4)*9/alpha)
    need('same-law complete 23 and 29 continuation',
         haar == ((566-49*R)/567)/(density*F(22, 21)*F(28, 27)))
    need('exact positive Haar lower',
         haar == F(19322824958140352009, 18870953593726484490240000))
    need('Haar lower exceeds one millionth', haar > F(1, 1000000))
    ustar = 24*(target-2*B-F(7, 8))/K2
    need('exact load threshold',
         ustar == F(68029220008060721916648, 12707171689116034479349))
    need('simple all-height domain lies below exact threshold', u < ustar < 6)
    need('threshold is the exact zero-margin boundary',
         2*B+F(7, 8)+ustar*K2/24 == target)
    raw_coefficient = 1+(9-F(20, 3))/24
    raw_bound = B+raw_coefficient*(1+B)
    need('H5 raw uniform-cap coefficient', raw_coefficient == F(79, 72))
    need('H5 raw supplier-budget comparison', raw_bound > target > R)

    out = {
        'schema': 'joint-weighted-query-reserve-v1',
        'scope': 'Conditional same-source theorem with arbitrary finite original heights and complete query heights. Fixed pure3 geometry, shallow two-phase selection, and actual joint reserves remain assumptions. No new Lean or unrestricted Erdos7 claim.',
        'sources': [{'path': SOURCE_NAME, 'sha256': SOURCE_SHA256},
                    {'path': ENVELOPE_NAME, 'sha256': ENVELOPE_SHA256}],
        'B': ex(B), 'alpha': ex(alpha), 'target': ex(target),
        'second_hinge': {
            'K2': ex(K2), 'SD10_corners': corner_data,
            'contract': 'Every finite partial nonunit one-phase layout under the SAME actual PA source; derived from SD10 full hinge, not R_Q<=B alone.',
            'unit_accounting': 'Complete query N contains unit once; N>=1+L implies (L-2)+<=(N-3)+.',
        },
        'joint_reserve_consumer': {
            'actual_condition': '2cA+3cB>=4 and cA>=5/9 almost everywhere under the SAME nu.',
            'law': 'chi[(aA/cA)uA+(aB/cB)uB]nu; aA=cA/2,aB=1-cA/2.',
            'load_sufficient_condition': 'YA<=16/3 and YA+YB<=6; Yj sums54*3^(-e)Lje over ALL e>=4.',
            'all_height_mean_bound': ex(mean), 'weight_cap': ex(h),
            'query_upper': ex(R), 'query_margin': ex(target-R),
            'density_upper': ex(density), 'Haar_survivor_lower': ex(haar),
            'general_load_formula': 'For YA<=u,YA+YB<=6 and0<=u<6: R<=2B+7/8+(u/24)(B-2).',
            'strict_u_threshold': ex(ustar),
            'relation_to584': 'cB=1,cA>=5/9 implies the joint capacity; the second hinge closes the previously stated arbitrary-original-height mean gap.',
        },
        'raw_supplier_budget_comparison': {
            'H5_capacity_minima': {'a': '20/3', 'b': '52/3', 'r': '20/3', 'beta': '24'},
            'coefficient': ex(raw_coefficient), 'query_upper': ex(raw_bound),
            'scope': 'Comparison using the same conservative supplier B at H5; does not imply any lower bound on actual query cost or failure of older instance-specific certificates.',
        },
    }
    out['actual_family'] = actual_family(B, K3, K7, need)
    out['check_count'] = len(checks)
    out['checks'] = checks
    args.output.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'checks': len(checks), 'query_upper': float(R),
                      'gate': float(target), 'Haar_lower': float(haar),
                      'output': str(args.output)}))


def actual_family(B, K3, K7, need):
    """Exact actual source/original controls; B is the retained supplier bound."""
    from fractions import Fraction as F
    from itertools import product
    from math import gcd, prod
    Q = (5, 7, 11, 13, 17, 19)
    A4 = (0, 6, 9, 15, 18, 24)
    A5 = (27, 33, 36, 42, 45, 51)
    def ex(x):
        x = F(x)
        return {'exact':str(x), 'decimal':float(x)}
    def crt(t, power3, r, d):
        if gcd(power3,d) != 1:
            raise ValueError('noncoprime original CRT inputs')
        return (t+power3*(((r-t)*pow(power3,-1,d))%d))%(power3*d)
    def family(H):
        if H < 5:
            raise ValueError('original height must be at least five')
        out = [{'modulus':3,'phase':1,'d':1,'e':1,'t':1,'r':0},
               {'modulus':9,'phase':3,'d':1,'e':2,'t':3,'r':0}]
        for j,q in enumerate(Q):
            for e,t,r in ((0,0,0),(1,2,1),(4,A4[j] if q!=19 else 2,2),(H if q==19 else 5,A5[j],2)):
                out.append({'modulus':3**e*q,'phase':r if e==0 else crt(t,3**e,r,q),'d':q,'e':e,'t':t,'r':r})
        for e,t,r in ((0,0,0),(1,2,1),(4,24,2)):
            out.append({'modulus':3**e*25,'phase':r if e==0 else crt(t,3**e,r,25),'d':25,'e':e,'t':t,'r':r})
        return out
    rows = []
    for q in Q:
        need('29 source row normalized '+str(q),sum((F(1,q-2) for _ in range(2,q)),F(0))==1)
        caps={11:F(5,3),13:F(3,2),17:F(2),19:F(9,5)}
        if q in caps:
            need('29 source actual PA cap inactive '+str(q),F(q,q-2)<caps[q])
        rows.append({'prime':q,'allowed_roots':list(range(2,q)),'root_mass':ex(F(1,q-2)),'row_density':ex(F(q,q-2))})
    need('29 selected25 phases already excluded at root5',all(r%5 in (0,1) for r in (0,1)))
    RQ = prod((1+F(q,(q-1)*(q-2)) for q in Q),start=F(1))-1
    need('29 exact complete actual source query norm',RQ==F(214267985,147806208))
    all_active = F(1,15)*prod((F(1,q-2) for q in Q[1:]),start=F(1))
    need('29 two branches damaged on one positive event',all_active==F(1,1893375))
    controls = []
    for H in (5,11):
        originals = family(H)
        need('29 distinct odd original moduli H='+str(H),len(originals)==29 and len({o['modulus'] for o in originals})==29 and all(o['modulus']>1 and o['modulus']%2 for o in originals))
        need('29 actual fixed CRT residues H='+str(H),all(o['phase']%o['d']==o['r']%o['d'] and o['phase']%(3**o['e'])==o['t']%(3**o['e']) for o in originals))
        need('29 shallow phases covered H='+str(H),all(o['r'] in (0,1) for o in originals if o['d']>1 and o['e']<=3))
        for e in (0,1):
            child=next(o for o in originals if o['d']==25 and o['e']==e)
            parent=next(o for o in originals if o['d']==5 and o['e']==e)
            need('29 shallow25 redundancy H='+str(H)+' e='+str(e),child['modulus']%parent['modulus']==0 and child['phase']%parent['modulus']==parent['phase'])
        deepA=[o for o in originals if o['e']>=4 and o['t']%9 in (0,6)]
        need('29 actual A ternary cylinders disjoint H='+str(H),all((u['t']-v['t'])%(3**min(u['e'],v['e'])) != 0 for i,u in enumerate(deepA) for v in deepA[i+1:]))
        need('29 actual deep branches H='+str(H),all(o['t']%9 in (0,6) for o in deepA))
        count=0
        worst_cA=F(1);worst_cB=F(1);worst_joint=F(5)
        for i5,i25 in ((0,0),(1,0),(1,1)):
            for rest in product((0,1),repeat=5):
                hits=(i5,)+rest
                YA=F(2,3)*(sum(hits[:5])+i25)+F(2,9)*sum(hits[:5])+F(54,3**H)*hits[5]
                YB=F(2,3)*hits[5]
                cA=1-YA/12;cB=1-YB/18
                aA=cA/2;aB=1-aA
                if not (0<=YA<=F(16,3) and YA+YB<=6 and cA>=F(5,9) and 2*cA+3*cB>=4 and aA<=cA/2 and aB<=F(3,4)*cB):
                    raise ValueError('29 actual fibre capacity failed')
                worst_cA=min(worst_cA,cA);worst_cB=min(worst_cB,cB);worst_joint=min(worst_joint,2*cA+3*cB)
                count+=1
        expected_YA=F(46,9)+F(54,3**H)
        expected_cA=1-expected_YA/12
        expected_cB=F(26,27)
        need('29 all incidence patterns H='+str(H),count==96)
        need('29 jointly attained actual minima H='+str(H),worst_cA==expected_cA and worst_cB==expected_cB and worst_joint==2*expected_cA+3*expected_cB)
        r=12*worst_cA;beta=12*worst_cA+18*worst_cB
        raw_coeff=1+(9-r)/beta
        raw_generic=B+raw_coeff*(1+B)
        controls.append({'H':H,'originals':originals,'incidence_patterns':count,'YA_max':ex(expected_YA),'YB_max':ex(F(2,3)),'cA_min':ex(worst_cA),'cB_min':ex(worst_cB),'joint_2cA_3cB_min':ex(worst_joint),'raw_capacity_coefficient':ex(raw_coeff),'raw_query_bound_using_generic_B':ex(raw_generic)})
    need('29 H5 coupled reserve equality',controls[0]['cA_min']['exact']=='5/9' and controls[0]['cB_min']['exact']=='26/27' and controls[0]['joint_2cA_3cB_min']['exact']=='4')
    need('29 H5 raw supplier certificate misses gate',controls[0]['raw_capacity_coefficient']['exact']=='79/72' and F(controls[0]['raw_query_bound_using_generic_B']['exact'])>F(566,49))
    # This checks the stated extension; it does not claim every larger H
    # continues separating the raw supplier certificate.
    need('29 arbitrary-height load decreases from H5',F(46,9)+F(54,3**5)==F(16,3) and F(54,3**11)<F(54,3**5))
    K2=B-2
    weighted=2*B+F(7,8)+F(2,9)*K2
    need('29 sharp weighted supplier bound passes',weighted==F(1795085660881088508439,155439081639808263720) and weighted<F(566,49))
    # Existing580 constants are included solely for an honest old-method control.
    rho=sum((F(1,q-2) for q in Q[:-1]),F(0))+F(1,15)
    mass=1-rho/33-K3/66-K7/22
    old_generic=(B+F(10,11)*(1+B))/mass
    old_actual=(RQ+F(10,11)*(1+RQ))/mass
    need('29 actual fourth-layer A mean',rho==F(86,99))
    need('29 existing580 generic first-moment gate fails',mass>0 and old_generic>F(566,49))
    need('29 existing580 also passes with actual source norm',old_actual<F(566,49))
    return {'family':'29 originals with one ternary original height H>=5',
            'actual_source_rows':rows,'selected_phases':{str(d):[0,1] for d in Q+(25,)},
            'actual_source_RQ':ex(RQ),'source_density':ex(prod((F(q,q-2) for q in Q),start=F(1))),
            'two_branch_bad_event_mass':ex(all_active),'checked_heights':controls,
            'all_height_identity':'YA_max(H)=46/9+54*3^(-H); cA_min=1-YA_max/12; cB_min=26/27; H>=5. Only q19 exponent5 is replaced by exponentH, preserving its ternary phase51 and Q phase2.',
            'arbitrary_height_scope':'The source and all Q labels are fixed for every H>=5. The residual original height is unbounded; every query height is retained. Raw-budget separation is asserted only at H5.',
            'sharp_weighted_query_upper':ex(weighted),'rho_A4':ex(rho),
            'old580_generic_first_moment_query_upper':ex(old_generic),'old580_actual_query_upper':ex(old_actual),
            'scope':'Both branches are damaged simultaneously under one actual PA source. Two shallow25 originals are redundant. The generic580 first-moment gate fails; no claim is made about its whole Gamma test. Existing580 with the actual source norm passes, so no new noncoverage class is claimed for this control.'}

if __name__ == '__main__':
    main()
