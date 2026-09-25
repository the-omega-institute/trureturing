#!/usr/bin/env python3
"""Exact controls for a same-source clipped two-branch query certificate.

The general result has arbitrary finite original heights and complete query
heights. Finite rational controls below audit formulas, not these quantifiers.
No Lean claim or unrestricted odd-covering conclusion is made.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path
import json

PINS = {
    'pa_complete_suffix_debits.json': 'b1b204f8728c64ed9265e91d78d3072a2e77f64f6efca57512f3e58f0bdf3ccc',
    'height_three_clipping_envelope.json': '276d7e266a86ed8e5a1c9da2982b219725c2738bc4ad19da1243bf8575543685',
}
Q = (5, 7, 11, 13, 17, 19)


def ex(value):
    value = F(value)
    return {'exact': str(value), 'decimal': float(value)}


def positive(value):
    return max(F(0), value)


def clipped(ca, cb, z):
    D = 30-z
    r = 12/D
    X, V = 12*(1-ca), 18*(1-cb)
    W = X+V
    T = positive(W-z)
    U = min(X, positive(z-V))
    aa = r*ca
    ab = min(1-aa, F(3, 2)*r*cb)
    return D, r, X, V, W, T, U, aa, ab


def actual_47(z, B, alpha, K2, K3, gate, tau_star, need):
    residues = [t for t in range(81) if t % 3 != 1 and t % 9 != 3]
    A = {t for t in residues if t % 9 in (0, 6)}
    Bbranch = {t for t in residues if t % 3 == 2}
    need('47 fixed pure survivor has 18 A and 27 B cylinders',
         len(residues) == 45 and len(A) == 18 and len(Bbranch) == 27
         and A.isdisjoint(Bbranch) and A | Bbranch == set(residues))
    originals = [{'modulus': 3, 'phase': 1}, {'modulus': 9, 'phase': 3}]
    for j, t in enumerate(residues, 1):
        d = 5**j
        a = d*((t*pow(d, -1, 81)) % 81)
        originals.append({'modulus': 81*d, 'phase': a, 'ternary_phase': t,
                          'cofactor': d, 'cofactor_phase': 0, 'j': j})
    need('47 actual CRT phases', all(row['phase'] % 81 == row['ternary_phase']
         and row['phase'] % row['cofactor'] == 0 for row in originals[2:]))
    mods = [row['modulus'] for row in originals]
    need('47 distinct odd numerical originals', len(mods) == len(set(mods)) == 47
         and all(m > 1 and m % 2 for m in mods))
    need('47 shallow mixed selector empty', all(row['modulus'] % 81 == 0
         for row in originals[2:]))
    # N=min(v_5(x),45). Its 46 disjoint events include the terminal zero fibre.
    probabilities = [F(4, 5**(n+1)) for n in range(45)] + [F(1, 5**45)]
    need('47 valuation atoms normalized', sum(probabilities, F(0)) == 1)
    cases = []
    expected_T = F(0)
    expected_beta = F(0)
    expected_W = F(0)
    expected_U = F(0)
    expected_Uhinge = F(0)
    ternary_mass = []
    for n, pn in enumerate(probabilities):
        removed = set(residues[:n])
        ca = F(len(A-removed), 18)
        cb = F(len(Bbranch-removed), 27)
        D, r, X, V, W, T, U, aa, ab = clipped(ca, cb, z)
        beta = aa+ab
        ratioA = aa/ca if ca else F(0)
        ratioB = ab/cb if cb else F(0)
        densities = [F(0)]*81
        for t in A-removed:
            densities[t] = F(9, 2)*ratioA
        for t in Bbranch-removed:
            densities[t] = 3*ratioB
        if W != F(2*n, 3) or sum(densities, F(0))/81 != beta:
            raise ValueError('47 actual mask/transport mismatch at n='+str(n))
        if any(densities[t] != 0 for t in removed):
            raise ValueError('47 unsupported transported mass')
        ternary_mass.append([[sum((densities[t] for t in range(a, 81, 3**e)), F(0))/81
                              for a in range(3**e)] for e in range(5)])
        expected_T += pn*T
        expected_beta += pn*beta
        expected_W += pn*W
        expected_U += pn*U
        expected_Uhinge += pn*positive(U-2)
        cases.append({'n': n, 'mass': pn, 'cA': ca, 'cB': cb, 'W': W, 'beta': beta})
    need('47 all valuation atoms match actual full masks', len(cases) == 46)
    tau = (1-F(1, 5**37))/(6*5**8)
    need('47 exact excess tail from actual mask', expected_T == tau)
    need('47 excess tail equals survival-function sum',
         tau == F(2, 3)*sum((F(1, 5**j) for j in range(9, 46)), F(0)))
    need('47 actual mean loss', expected_W == (1-F(1, 5**45))/6)
    need('47 terminal event has both reserves zero', cases[-1]['cA'] == 0
         and cases[-1]['cB'] == 0 and cases[-1]['beta'] == 0
         and probabilities[-1] > 0)
    D = 30-z
    s = 1-tau/D
    need('47 retained mass identity', expected_beta == s and 0 < s < 1)
    need('47 positive excess tail passes strict gate', 0 < tau < tau_star)
    need('47 actual coupled means satisfy same-source estimates',
         expected_U+tau <= expected_W <= B and expected_Uhinge+tau <= K2)
    N2 = 1+2*B+(z*K2-3)/D
    Nsplit = 1+2*B+(3*B-9+(z-2)*K3)/D
    Qeta = min(N2-3*tau/D, Nsplit-4*tau/D)
    density = 486/(D*alpha*s)
    haar_tail = F(185, 149688)*alpha*(tau_star-tau)
    haar_best = alpha*D*(566*s-49*Qeta)/299376
    need('47 normalized supplier gate passes', Qeta/s < gate)
    need('47 tail and best Haar bounds positive', 0 < haar_tail <= haar_best)
    need('47 tail Haar identity', haar_tail == alpha*D*
         (566*s-49*(Nsplit-4*tau/D))/299376)
    # Exact complete queries for this actual mask, using its finite constant
    # cells plus geometric tails in both coordinates. Other Q coordinates Haar.
    # At 5-depth j, the zero phase contains n>=j. Nonzero phases have n<j
    # fixed, with cylinder Haar mass 5^-j; optimize over those n and 3-prefix.
    qtable = [[F(0)]*46 for _ in range(5)]
    for e in range(5):
        suffix = [F(0)]*(3**e)
        zero_phase_max = [F(0)]*46
        for j in range(45, -1, -1):
            suffix = [v+probabilities[j]*ternary_mass[j][e][a]
                      for a, v in enumerate(suffix)]
            zero_phase_max[j] = max(suffix)
        prior_max = F(0)
        for j in range(46):
            qtable[e][j] = max(zero_phase_max[j], prior_max/F(5**j))
            prior_max = max(prior_max, max(ternary_mass[j][e]))
    need('47 exact unit query equals retained mass', qtable[0][0] == s)
    # This example has no mass on the all-zero 5^45 cylinder, hence its 5-tail
    # maxima are among nonzero phases; the same geometric tail identity holds.
    finite = sum((sum(row, F(0)) for row in qtable), F(0))
    ternary_tail = sum(qtable[4], F(0))/2
    five_tail = sum((row[45] for row in qtable), F(0))/4
    double_tail = qtable[4][45]/8
    zeta_other = prod((F(q, q-1) for q in Q if q != 5), start=F(1))
    actual_raw_query = zeta_other*(finite+ternary_tail+five_tail+double_tail)-s
    source_query = prod((F(q, q-1) for q in Q), start=F(1))-1
    need('47 exact actual query lies below supplier certificate',
         actual_raw_query <= Qeta and actual_raw_query/s < gate)
    need('47 Haar source full query norm below B', source_query < B)
    encoded = json.dumps(originals, sort_keys=True, separators=(',', ':')).encode()
    return {
        'scope': '47 fixed originals under the actual empty-selection PA source nu=Q-Haar; both complete reserves vanish on positive source mass. This exceeds the pointwise reserve domains of 585, but is not a new bare noncoverage class.',
        'original_count': 47,
        'original_definition': 'Pure (3,1),(9,3); enumerate t_j in increasing order from {0<=t<81: t%3!=1 and t%9!=3}; j=1..45, m_j=81*5^j, a_j=5^j*((t_j*(5^j)^(-1)) mod81).',
        'originals_sha256': sha256(encoded).hexdigest(),
        'mixed_ternary_height': 4,
        'selected_Q_phases': [],
        'source': 'Q-Haar; every shallow two-phase selection is empty.',
        'source_RQ': ex(source_query),
        'valuation_atom_count': len(cases),
        'joint_zero_fibre_source_mass': ex(probabilities[-1]),
        'actual_damage': 'W=(2/3)*min(v5(x5),45); each mixed ternary cylinder is disjoint.',
        'EW': ex(expected_W), 'EU': ex(expected_U),
        'EU_hinge2': ex(expected_Uhinge), 'tau': ex(tau),
        'retained_mass': ex(s), 'normalized_supplier_query_upper': ex(Qeta/s),
        'normalized_density_upper': ex(density),
        'Haar_survivor_lower_tail_certificate': ex(haar_tail),
        'Haar_survivor_lower_best_two_certificates': ex(haar_best),
        'actual_RP_eta': ex(actual_raw_query),
        'actual_RP_mu': ex(actual_raw_query/s),
        'actual_query_tail_rule': 'For e>4, q_(3^e5^j)=3^(4-e)q_(3^4 5^j); for j>45, q_(3^e5^j)=5^(45-j)q_(3^e5^45). Q primes other than5 are Haar. Unit omitted once.',
    }


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = []
    def need(name, condition):
        if not condition:
            raise ValueError('FAILED: '+name)
        checks.append(name)
    sources = {}
    for name, pin in PINS.items():
        raw = (args.source_dir/name).read_bytes()
        need('source SHA256 '+name, sha256(raw).hexdigest() == pin)
        sources[name] = json.loads(raw)
    supplier = sources['pa_complete_suffix_debits.json']
    envelope = sources['height_three_clipping_envelope.json']
    B = F(supplier['joint_bound'])
    alpha = min(F(row['alpha']) for row in supplier['corners'])
    K2 = B-2
    K3 = max(F(row['K_integer'][3]) for row in envelope['corners'])
    K7 = max(F(row['K_integer'][7]) for row in envelope['corners'])
    gate = F(566, 49)
    need('same-source B pin', B == F(432040125182653876501, 86355045355449035400)
         and F(envelope['B']) == B)
    need('same-source alpha pin', alpha == F(7575003978548161, 73724315753088000))
    need('same-source K3 pin', K3 == F(12019840537595758779003, 5715264751774801992890))
    for corner in supplier['corners']:
        margin = K2*F(corner['alpha'])-F(corner['Phi'])+F(corner['deletion'])+F(corner['J'])
        need('SD10 second hinge corner '+corner['x']+','+corner['y'], margin >= 0)
    z = F(16, 3)
    D = 30-z
    N2 = 1+2*B+(z*K2-3)/D
    Nsplit = 1+2*B+(3*B-9+(z-2)*K3)/D
    tau_star = D*(gate-Nsplit)/(gate-4)
    need('exact N2 at16/3', N2 == (164*B+33)/74)
    need('exact split bound at16/3', Nsplit == (157*B+47+10*K3)/74)
    need('both pointwise bounds pass', N2 < Nsplit < gate)
    need('exact tau threshold', tau_star == (39581-7693*B-490*K3)/1110
         == F(21218460281840396929028797,380636632468201812726474000))
    need('split normalized bound exactly touches gate',
         (Nsplit-4*tau_star/D)/(1-tau_star/D) == gate)
    # Exact corners, interior rationals and the W=z switching surface.
    reserves = [F(0), F(1,100), F(1,3), F(1,2), F(5,9), F(2,3), F(3,4), F(1)]
    controls = []
    for zz in (F(2), F(3), F(4), F(5), F(16,3), F(6)):
        pairs = {(ca,cb) for ca in reserves for cb in reserves}
        for ca in reserves:
            cb = (30-zz-12*ca)/18
            if 0 <= cb <= 1:
                pairs.add((ca,cb))
        for ca,cb in sorted(pairs):
            dd,r,X,V,W,T,U,aa,ab = clipped(ca,cb,zz)
            beta = aa+ab
            ratioA = aa/ca if ca else F(0)
            ratioB = ab/cb if cb else F(0)
            predicates = (
                beta == 1-T/dd, positive(ab-(1-r)) == U/dd,
                0 <= aa <= r <= 1-r, 0 <= ab, 0 <= beta <= 1,
                0 <= U <= zz, U <= W, U+T <= W,
                positive(U-2)+T <= positive(W-2),
                ratioA <= r, ratioB <= F(3,2)*r,
                F(9,2)*ratioA <= 54/dd, 3*ratioB <= 54/dd,
                aa == ca*ratioA, ab == cb*ratioB,
                max(aa,ab) <= 1-r+U/dd,
            )
            if not all(predicates):
                raise ValueError('clipped rational control failed '+str((zz,ca,cb)))
            controls.append((zz,ca,cb))
    need('all rational clipping and coupled-loss controls', len(controls) >= 384)
    need('zero fibre discards mass with no division',
         all(clipped(F(0),F(0),zz)[5] == 30-zz
             and clipped(F(0),F(0),zz)[7:] == (F(0),F(0))
             for zz in (F(2),F(16,3),F(6))))
    need('full deep geometric coefficient', F(3,4)*12/D == 9/D
         and 1-12/D+9/D == 1-3/D)
    for tt in (F(0),tau_star/2,tau_star):
        direct = B+(1-3/D)*(1+B)+(z*K2+3*B-3*tt)/D
        split = B+(1-3/D)*(1+B)+(3*B+3*K2+(z-2)*K3-4*tt)/D
        need('same-source numerator algebra at tau='+str(tt),
             direct == N2-3*tt/D and split == Nsplit-4*tt/D)
    haar = alpha*D*(566-49*N2)/299376
    need('23 and29 same-law continuation density identity',
         haar == ((566-49*N2)/567)/((486/(D*alpha))*F(22,21)*F(28,27)))
    generic_tail = (5*K3+7*K7)/12
    need('generic interpolated tail does not force new gate', generic_tail > tau_star)
    actual = actual_47(z,B,alpha,K2,K3,gate,tau_star,need)
    out = {
        'schema': 'joint-clipped-query-reserve-v1',
        'scope': 'Conditional same-source ordinary-mathematics certificate. Fixed pure3 geometry and shallow two-phase selection are retained; all original heights and query heights are allowed. Finite controls do not prove universal quantifiers. No new Lean and no unrestricted Erdos7 conclusion.',
        'sources': [{'path':name,'sha256':pin} for name,pin in PINS.items()],
        'B':ex(B),'alpha':ex(alpha),'K2':ex(K2),'K3':ex(K3),'K7':ex(K7),'target':ex(gate),
        'formula_contract': {
            'range': '2<=z<=6; D=30-z; r=12/D; actual complete reserves0<=cA,cB<=1 under one actual PA source nu.',
            'damage': 'X=12(1-cA), V=18(1-cB), W=X+V; T=(W-z)+; U=min(X,(z-V)+).',
            'allocation': 'aA=r*cA, aB=min(1-r*cA,(3/2)*r*cB); beta=aA+aB=1-T/D.',
            'zero_convention': 'a_j/c_j=0 when c_j=0; then a_j=0. The ratio aA/cA<=r, with equality required only on cA>0.',
            'same_source_inputs': 'E W<=B, E(W-2)+<=K2, RQ(nu)<=B and every-layout hinges K2,K3. E(U)+tau<=B and E(U-2)++tau<=K2 use the SAME law.',
            'N2': '1+2B+(z*K2-3)/D',
            'Nsplit': '1+2B+(3B-9+(z-2)*K3)/D',
            'normalized_bound': 'RP(mu)<=min(N2-3tau/D,Nsplit-4tau/D)/(1-tau/D), tau=E T<D.',
            'density': 'mu<=486/(D*alpha*(1-tau/D))*Haar_P.',
            'same_label_rule': 'Both roots share one numerical-label inventory: use sum_d max(q_d(v nu),q_d(w nu)); do not sum independent branch inventories.',
            'credit_rule': 'K2=B-2 comes from SD10 full hinge; J credits are already in B and are not subtracted again.',
        },
        'pointwise': {'z':ex(z),'D':ex(D),'r':ex(12/D),
            'N2':ex(N2),'Nsplit':ex(Nsplit),'query_margin':ex(gate-N2),
            'Haar_survivor_lower':ex(haar)},
        'clipped': {'tau_star':ex(tau_star),
            'strict_condition':'E(W-16/3)+<tau_star.',
            'Haar_lower_formula':'(185*alpha/149688)*(tau_star-tau)',
            'generic_interpolated_tail_upper':ex(generic_tail),
            'remaining_gap':'The supplied generic upper estimate exceeds tau_star. This is certificate insufficiency, not actual-law impossibility.'},
        'actual_47_zero_fibre_control':actual,
        'rational_control_count':len(controls),
        'check_count':len(checks),'checks':checks,
    }
    args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'output':str(args.output),'checks':len(checks),
                      'rational_controls':len(controls),
                      'tau_star':str(tau_star),'actual47_tau':actual['tau']['exact']}))


if __name__ == '__main__':
    main()
