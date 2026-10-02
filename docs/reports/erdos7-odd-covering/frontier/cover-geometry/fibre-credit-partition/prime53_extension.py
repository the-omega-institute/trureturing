"""One fixed half-clipped 53 step and existing tail/gate consumers.

The reviewed joint-prime JSON is a pinned input, not a re-executed producer.
All arithmetic is exact. Infinite auxiliary moments remain complete.
Only the explicitly requested output file is written.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import factorial, prod
from pathlib import Path

PIN = 'd185684ac07516e26b9359539abacccfbfcf0680010d6f689477d73213c44862'
LIMIT = 96
CHECKS = 0


def check(b, reason):
    global CHECKS
    CHECKS += 1
    if not b:
        raise ArithmeticError(reason)


def read_atoms(snapshot):
    a = [F(0) for _ in range(LIMIT + 1)]
    for z, v in snapshot['low_atoms'].items():
        a[int(z)] = F(v)
    check(all(x >= 0 for x in a), 'nonnegative pinned low atoms')
    return a


def fourth_factor(p, cap):
    t = F(1, p - 1)
    return 1 + cap * (15*t + 50*t*t + 60*t**3 + 24*t**4)


def trim_fourth(before, after):
    b, a = read_atoms(before), read_atoms(after)
    check(all(x >= y for x, y in zip(b, a)), 'prior trim only removes low mass')
    return sum((z**4 * (b[z] - a[z]) for z in range(1, LIMIT + 1)), F(0))


def snapshot(m, w, g, k4, a):
    low = [sum((z**r*a[z] for z in range(1, LIMIT + 1)), F(0))
           for r in (0, 1, 2, 4)]
    tail = [v - u for v, u in zip((m, w, g, k4), low)]
    check(all(x >= 0 for x in tail), 'all complete tail moments nonnegative')
    check(tail[1] >= (LIMIT+1)*tail[0], 'tail first moment has correct support')
    check(tail[2] >= (LIMIT+1)*tail[1], 'tail second moment has correct support')
    check(tail[3] >= (LIMIT+1)**2*tail[2], 'tail fourth moment has correct support')
    return {'mass': str(m), 'first': str(w), 'second': str(g), 'fourth': str(k4),
            'mean': str(w/m), 'normalized_second': str(g/m),
            'normalized_fourth': str(k4/m),
            'tail_mass': str(tail[0]), 'tail_first': str(tail[1]),
            'tail_second': str(tail[2]), 'tail_fourth': str(tail[3]),
            'low_atoms': {str(z): str(a[z]) for z in range(1, LIMIT + 1) if a[z]}}


def tau7(b, ell):
    check(b >= 286 and ell >= 4 and 3**ell <= b, 'SH tail domain')
    poly = sum((F(factorial(7), factorial(7-j)*ell**j) for j in range(8)), F(0))
    c = F(2*ell*ell+1, 2*ell*ell-1)
    return c**7/b * F(b, b-3)**2 * poly


def quartic_tail(b, ell):
    check(b >= 286 and ell >= 4 and 3**ell <= b and 4*ell >= 25,
          'HM15 fixed quartic tail domain')
    poly = sum((F(factorial(25), factorial(25-j)*(3*ell)**j)
                for j in range(26)), F(0))
    c = F(2*ell*ell+1, 2*ell*ell-1)
    return F(5625, 6144)*c**25 * F(b, (b-1)**4) * poly


def main(source, output):
    raw = source.read_bytes()
    check(sha256(raw).hexdigest() == PIN, 'reviewed joint-prime input hash')
    base = json.loads(raw)
    check(base['atom_limit'] == LIMIT, 'retained low atom domain')
    check([s['prime'] for s in base['stages']] == [43, 47], 'reviewed fixed predecessor')
    k4 = prod(F(p**4+11*p**3+11*p*p+p, (p-1)**4) for p in base['primes'])
    initial_full_fourth = k4
    k4 -= trim_fourth(base['complete_Haar_comparison'], base['initial'])
    fourth_chain = [{'stage': 'initial trim', 'fourth': str(k4)}]
    for stage in base['stages']:
        check(stage['conditional_cap'] == '2', 'reviewed predecessor cap')
        k4 *= fourth_factor(stage['prime'], F(2))
        k4 -= trim_fourth(stage['appended'], stage['after'])
        fourth_chain.append({'stage': stage['prime'], 'fourth': str(k4)})
    s = base['stages'][-1]['after']
    m, w, g = map(F, (s['mass'], s['first'], s['second']))
    atoms = read_atoms(s)
    before = snapshot(m, w, g, k4, atoms)

    q, threshold = 53, F(26)
    hinge = w-threshold*m + sum(((threshold-z)*atoms[z]
                                for z in range(1, 26)), F(0))
    charge = hinge/threshold
    target = m-charge
    check(hinge >= 0 and target > 0, 'fixed 53 step has positive certified mass')
    appended_atoms = [F(0) for _ in range(LIMIT+1)]
    for z in range(1, LIMIT+1):
        for value in range(1, LIMIT//z+1):
            prob = 1-F(2,q) if value == 1 else F(2*(q-1),q**value)
            appended_atoms[z*value] += atoms[z]*prob
    aw = w*(1+F(2,q-1))
    ag = g*(1+F(2*(3*q-1),(q-1)**2))
    ak = k4*fourth_factor(q,F(2))
    appended = snapshot(m, aw, ag, ak, appended_atoms)
    atoms = appended_atoms[:]
    left = charge
    removed = {r:F(0) for r in (1,2,4)}
    cutoff = 0
    for z in range(1,LIMIT+1):
        take = min(left,atoms[z])
        atoms[z] -= take
        left -= take
        for r in removed:
            removed[r] += z**r*take
        if left == 0:
            cutoff = z
            break
    check(left == 0 and cutoff == 36, '53 upper-mass trim resolved at 36')
    m,w,g,k4 = target,aw-removed[1],ag-removed[2],ak-removed[4]
    after = snapshot(m,w,g,k4,atoms)
    check(m > F(1,300), 'same physical source mass exceeds 1/300')
    check(g < F(173,10), 'same physical source second moment below 173/10')
    check(k4 < 2130000, 'same physical source fourth moment below 2130000')
    check(F(123,2)*m < w < 62*m, 'mean bracket excludes next 59 for all constant clips')
    check(w-58*m > F(7,2)*m, 'strict next59 mean-gate deficit')
    check(F(8)/m < 2400 and m/8 > F(1,2400), 'full Haar density and survival reserve')

    sh10=tau7(10000,8)
    sh20=tau7(20000,9)
    check(m-g*sh10 < 0, 'same SH second-moment certificate fails at 10000')
    sh20coarse=F(1,300)-F(173,10)*sh20
    check(sh20coarse > F(7,10000), 'SH sufficient reserve at existing cutoff20000')
    check(m-g*sh20 > sh20coarse, 'exact SH reserve dominates its rational summary')

    tq=quartic_tail(10000,8)
    qcoarse=F(1,300)-2130000*tq
    check(qcoarse > F(33,10000), 'quartic tail keeps cutoff10000 with positive reserve')
    check(m-k4*tq > qcoarse, 'exact quartic reserve dominates rational summary')
    # Fixed HM13 coefficient certificate for delta=2/5, r=25.
    from math import comb
    for j,coefficient in enumerate((F(1),F(25),F(250,3),F(100),F(40))):
        check(coefficient <= comb(25,j), 'fixed quartic coefficient majorization')

    result = {'input':source.name,'input_sha256':PIN,
              'evidence':'exact single-step application of reviewed common-source comparison; no Lean claim',
              'atom_limit':LIMIT,'initial_Haar_fourth':str(initial_full_fourth),
              'reconstructed_fourth_chain':fourth_chain,
              'prime':53,'delta':'1/2','threshold':'26','before':before,
              'stop_loss':str(hinge),'charge':str(charge),'appended':appended,
              'trim':{'cutoff':36,'removed_mass':str(charge),
                      'removed_first':str(removed[1]),'removed_second':str(removed[2]),
                      'removed_fourth':str(removed[4])},'after':after,
              'physical_full_Haar_density_cap':'8',
              'normalized_density_cap':str(8/m),'Haar_survivor_lower':str(m/8),
              'next59':{'mean_minus58':str(w/m-58),'absolute_gate_deficit':str(w-58*m),
                        'scope':'all legal constant clips fail this comparator ledger only'},
              'SH_second_moment':{
                  'B10000_ell8_allowance':str(sh10),'B10000_reserve':str(m-g*sh10),
                  'B20000_ell9_allowance':str(sh20),'B20000_reserve':str(m-g*sh20),
                  'B20000_coarse_reserve':str(sh20coarse)},
              'quartic_same_source':{
                  'B':10000,'ell':8,'tail_delta':'2/5','growth_exponent':25,
                  'allowance':str(tq),'exact_reserve':str(m-k4*tq),
                  'coarse_reserve':str(qcoarse),'mass_lower':'1/300',
                  'fourth_upper':'2130000','inherited_analytic_premise':'SH11/HM14'},
              'exact_checks':CHECKS}
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'checks':CHECKS,'output':str(output),'m53':float(m),'G53':float(g),
                      'K4_53':float(k4),'mean53':float(w/m),'trim_cutoff':36,
                      'quartic_coarse_reserve':float(qcoarse)}))


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--source',type=Path,default=Path(__file__).with_name('joint43_47.json'))
    parser.add_argument('--output',type=Path,required=True)
    a=parser.parse_args()
    main(a.source,a.output)
