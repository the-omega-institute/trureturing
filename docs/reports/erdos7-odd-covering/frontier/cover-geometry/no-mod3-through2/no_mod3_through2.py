#!/usr/bin/env python3
"""Exact controls for the missing-modulus-3, through-exponent-2 slice.

The ordinary clipping proof supplies the arbitrary original/query heights
and all-layout quantifiers. These finite controls verify source constants,
the numerical continuation, and an actual 27-original zero-fibre example.
No new Lean verification or unrestricted odd-covering result is claimed.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path
import json


PINS = {
    'pa_complete_suffix_debits.json':
        'b1b204f8728c64ed9265e91d78d3072a2e77f64f6efca57512f3e58f0bdf3ccc',
    'height_three_clipping_envelope.json':
        '276d7e266a86ed8e5a1c9da2982b219725c2738bc4ad19da1243bf8575543685',
}
Q = (5, 7, 11, 13, 17, 19)


def ex(value):
    value = F(value)
    return {'exact': str(value), 'decimal': float(value)}


def crt(ternary_modulus, ternary_phase, cofactor, cofactor_phase):
    """The canonical integer phase for two coprime prime-power coordinates."""
    return (cofactor_phase + cofactor * (
        (ternary_phase-cofactor_phase) * pow(cofactor, -1, ternary_modulus)
        % ternary_modulus)) % (ternary_modulus*cofactor)


def actual_family(B, K3, s_min, need):
    ternary = [t for t in range(27) if t % 9 != 1]
    need('actual pure survivor consists of 24 depth-three cells',
         len(ternary) == 24)
    originals = []

    def add_original(e, t, d, a):
        modulus = 3**e*d
        phase = crt(3**e, t, d, a)
        need('actual CRT phase at modulus '+str(modulus),
             0 <= phase < modulus and phase % 3**e == t
             and phase % d == a)
        originals.append({'modulus': modulus, 'phase': phase,
                          'ternary_exponent': e, 'ternary_phase': t,
                          'cofactor': d, 'cofactor_phase': a})

    add_original(2, 1, 1, 0)
    add_original(0, 0, 5, 0)
    add_original(1, 0, 5, 1)
    for j, t in enumerate(ternary, 1):
        add_original(3, t, 5**j, 2)
    labels = [row['modulus'] for row in originals]
    need('actual 27 numerical original labels are distinct',
         len(labels) == len(set(labels)) == 27)
    need('actual original labels are odd nonunits',
         all(m > 1 and m % 2 == 1 for m in labels))
    need('actual modulus three is absent and modulus nine is present',
         3 not in labels and 9 in labels)

    selected = {}
    through_three = {}
    for row in originals:
        d = row['cofactor']
        if d == 1:
            continue
        if row['ternary_exponent'] <= 2:
            selected.setdefault(d, set()).add(row['cofactor_phase'])
        if row['ternary_exponent'] <= 3:
            through_three.setdefault(d, set()).add(row['cofactor_phase'])
    need('actual through-two selector has exactly the two five phases',
         selected == {5: {0, 1}})
    need('actual through-three selector fails at cofactor five',
         through_three[5] == {0, 1, 2})
    need('actual other through-two projected phase sets are empty',
         all(row['ternary_exponent'] > 2 for row in originals
             if row['cofactor'] > 5))

    period = 27*5**24

    def bad_originals(t, x5):
        n = crt(27, t, 5**24, x5)
        return [row['modulus'] for row in originals
                if n % row['modulus'] == row['phase']]

    witness_coordinates = [(1, 3), (2, 0), (0, 1)]
    witness_coordinates += [
        (t, 2+5**j if j < 24 else 2)
        for j, t in enumerate(ternary, 1)
    ]
    for row, (t, x5) in zip(originals, witness_coordinates):
        witness = crt(27, t, 5**24, x5)
        need('actual private witness at modulus '+str(row['modulus']),
             bad_originals(t, x5) == [row['modulus']])
        need('actual private witness CRT coordinates at modulus '+str(row['modulus']),
             0 <= witness < period and witness % 27 == t
             and witness % 5**24 == x5)
        row['private_witness'] = witness

    # N=sum_{j=1}^{24} 1_{[2]_(5^j)} under the actual selected PA source.
    # Its first digit is uniform on {2,3,4}; all higher digits are Haar.
    probabilities = ([F(2, 3)]
                     + [F(4, 3*5**n) for n in range(1, 24)]
                     + [F(1, 3*5**23)])
    need('actual 25 valuation atoms normalize', sum(probabilities, F(0)) == 1)
    expected_beta = F(0)
    expected_hinge = F(0)
    expected_Y = F(0)
    cases = []
    for n, probability in enumerate(probabilities):
        x5 = 3 if n == 0 else 2+5**n if n < 24 else 2
        incident = sum(x5 % 5**j == 2 for j in range(1, 25))
        need('actual incidence count at valuation atom '+str(n), incident == n)
        remaining = sum(not bad_originals(t, x5) for t in ternary)
        c = F(remaining, 24)
        need('actual complete survivor mask at valuation atom '+str(n),
             c == 1-F(n, 24))
        Y = F(2*n, 3)
        need('actual complete height-mixture loss at valuation atom '+str(n),
             1-c <= Y/15)
        beta = c/max(c, F(4, 5))
        need('actual clipped mass defect at valuation atom '+str(n),
             1-beta <= max(Y-3, F(0))/12)
        need('actual clipped weight finite at valuation atom '+str(n),
             0 <= beta <= 1 and max(c, F(4, 5)) > 0)
        if n >= 1:
            need('actual valuation tail probability from atom '+str(n),
                 sum(probabilities[n:], F(0)) == F(1, 3*5**(n-1)))
        expected_beta += probability*beta
        expected_hinge += probability*max(Y-3, F(0))
        expected_Y += probability*Y
        cases.append({'n': n, 'source_mass': ex(probability),
                      'survivor_fraction': ex(c), 'Y': ex(Y),
                      'clipped_fraction': ex(beta)})
    need('actual zero fibre has positive source mass', probabilities[-1] > 0)
    need('actual terminal fibre is entirely discarded',
         cases[-1]['survivor_fraction']['exact'] == '0'
         and cases[-1]['clipped_fraction']['exact'] == '0')
    need('actual third hinge satisfies uniform source bound', expected_hinge < K3)
    need('actual clipped mass exceeds uniform lower bound', expected_beta >= s_min)
    need('actual mean height load includes complete finite inventory',
         expected_Y == F(2, 3)*sum(
             (F(1, 3*5**(j-1)) for j in range(1, 25)), F(0)))
    source_RQ = (1+F(5, 12))*prod(
        (F(q, q-1) for q in Q if q != 5), start=F(1))-1
    need('actual selected PA source complete query cost below B', source_RQ < B)

    return {
        'scope': 'An actual 27-original family; its role is third projected phase and positive-mass zero-fibre behavior. Its bare noncoverage is not claimed new.',
        'original_count': len(originals),
        'originals': originals,
        'common_period': period,
        'original_definition': 'Pure 1 mod9; 0 mod5; (t=0 mod3,x5=1 mod5); for the increasing 24 residues t_j mod27 with t_j mod9!=1, add (t=t_j mod27,x5=2 mod5^j) at numerical modulus27*5^j.',
        'selected_Q_phases': [{'modulus': 5, 'phases': [0, 1]}],
        'source': 'Uniform first five roots {2,3,4}, Haar higher five digits, independent Haar at the other Q coordinates; all later selected PA rows are unchanged.',
        'source_RQ': ex(source_RQ),
        'pure_ternary_survivor_mass': ex(F(8, 9)),
        'valuation_atoms': cases,
        'zero_fibre_source_mass': ex(probabilities[-1]),
        'actual_clipped_mass': ex(expected_beta),
        'actual_height_mixture_mean': ex(expected_Y),
        'actual_height_mixture_third_hinge': ex(expected_hinge),
        'original_height_note': 'This finite control has mixed ternary height3; the ordinary clipping proof supplies arbitrary finite higher original heights.',
    }


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path,
                        default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = []

    def need(name, condition):
        if not condition:
            raise ValueError('FAILED: '+name)
        if name in checks:
            raise ValueError('DUPLICATE CHECK: '+name)
        checks.append(name)

    sources = {}
    for name, pin in PINS.items():
        raw_source = (args.source_dir/name).read_bytes()
        need('source SHA256 '+name, sha256(raw_source).hexdigest() == pin)
        sources[name] = json.loads(raw_source)
    supplier = sources['pa_complete_suffix_debits.json']
    envelope = sources['height_three_clipping_envelope.json']
    B = F(supplier['joint_bound'])
    K3 = max(F(row['K_integer'][3]) for row in envelope['corners'])
    alpha = min(F(row['alpha']) for row in supplier['corners'])
    gate = F(566, 49)
    need('same source query budget in both inputs', F(envelope['B']) == B)
    need('exact source query constant',
         B == F(432040125182653876501, 86355045355449035400))
    need('exact all-layout third hinge constant',
         K3 == F(12019840537595758779003, 5715264751774801992890))
    need('exact source density denominator',
         alpha == F(7575003978548161, 73724315753088000))

    s_min = 1-K3/12
    raw_query = (7*B+3)/4
    normalized_query = raw_query/s_min
    raw_density = F(27, 2)/alpha
    haar_lower = alpha*(566*s_min-49*raw_query)/8316
    need('positive uniform retained mass', s_min > 0)
    need('normalized query formula',
         normalized_query == (21*B+9)/(12-K3))
    need('strict nine-prime query gate', normalized_query < gate)
    need('Haar continuation exceeds one eighty-thousandth', haar_lower > F(1, 80000))
    need('complete pure query geometric sum', F(6, 5)*F(1, 2) == F(3, 5))
    need('complete residual height-mixture coefficients sum to one',
         18*F(1, 27)/(1-F(1, 3)) == 1)
    need('complete residual height cap', F(6, 5)*F(1, 18) == F(1, 15))
    need('raw density after clipping', F(6, 5)*9/F(4, 5) == F(27, 2))
    need('complete outside-prime density denominator', F(27, 2)*616 == 8316)
    need('missing modulus-three complete pure loss budget',
         F(1, 9)/(1-F(1, 3)) == F(1, 6))
    need('clipped complete positive-ternary query coefficient',
         F(3, 5)/F(4, 5) == F(3, 4))
    need('raw query retains the Q-unit at every positive ternary height',
         raw_query == B+F(3, 4)*(1+B))
    need('same-law outside-prime continuation and density identity',
         haar_lower == ((566*s_min-49*raw_query)/567)
         /(raw_density*F(22, 21)*F(28, 27)))
    need('exact retained mass constant',
         s_min == F(18854445494567288378559, 22861059007099207971560))
    need('exact complete normalized query constant',
         normalized_query == F(13038167015021694163818497,
                               1131266729674037302713540))
    need('exact nine-prime Haar lower constant',
         haar_lower == F(1426785259442099308757287,
                         111017121067685733201100800000))

    actual = actual_family(B, K3, s_min, need)
    out = {
        'schema': 'no-mod3-through2-v1',
        'scope': 'Ordinary corollary of the same-source clipping proof. No actual modulus3 original; arbitrary pure3^e originals for e>=2; at most two selected Q phases through ternary exponent2. All higher original phases/heights and complete query heights are retained. No residual-load or positive-fibre assumption. No new Lean or unrestricted odd-covering conclusion.',
        'sources': [{'path': name, 'sha256': pin} for name, pin in PINS.items()],
        'B': ex(B), 'K3': ex(K3), 'alpha': ex(alpha), 'target': ex(gate),
        'formula_contract': {
            'source': 'ONE actual selected PA law nu throughout; the third hinge holds for every finite partial nonunit one-phase Q query layout, not just actual layers.',
            'pure_source': 'u is Haar conditioned on the complete actual pure3 survivor; its Haar mass is at least5/6, u<=6H3/5, and R3(u)<=3/5.',
            'height_mixture': 'Y=sum_(e>=3)18*3^(-e)L_e; each L_e uses its actual fixed original phases and numerical labels; E(Y-3)+<=K3 and1-c<=Y/15.',
            'law': 'eta=chi*u*nu/max(c,4/5), c=integral chi du; Q marginal beta*nu with beta=c/max(c,4/5). Normalize once by s=eta(1).',
            'mass': 's>=1-K3/12; zero fibres are discarded with no division by zero.',
            'raw_query': 'R_P(eta)<=B+(3/4)(1+B)=(7B+3)/4; all positive ternary heights include the Q-unit once.',
            'normalized_query': 'R_P(mu)<=(21B+9)/(12-K3).',
            'density': 'eta<=27/(2*alpha)*H_P; mu<=27/(2*alpha*s)*H_P.',
            'nine_prime_continuation': 'Arbitrary additional distinct originals touching23 or29 within P union{23,29}; H>=alpha*(566s-49R_P(eta))/8316.',
            'marginal_scope': 'The final Q marginal can change; this is not lossless compression of the supplied marginal.',
            'reuse': 'Report574 complete-layout hinge and clipped conditional construction; Report578 PT12 with A=3/5,theta=1/15,t=3.',
        },
        'uniform_certificate': {
            'retained_mass_lower': ex(s_min),
            'raw_query_upper': ex(raw_query),
            'normalized_query_upper': ex(normalized_query),
            'normalized_query_margin': ex(gate-normalized_query),
            'raw_density_upper': ex(raw_density),
            'normalized_density_upper': ex(raw_density/s_min),
            'nine_prime_Haar_lower': ex(haar_lower),
        },
        'actual_27_zero_fibre_control': actual,
        'check_count': len(checks), 'checks': checks,
    }
    args.output.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'output': str(args.output), 'checks': len(checks),
                      'normalized_query_upper': float(normalized_query),
                      'nine_prime_Haar_lower': float(haar_lower)}))


if __name__ == '__main__':
    main()
