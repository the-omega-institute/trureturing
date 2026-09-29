"""Finite-prefix tail budgets for the fixed missing23 source chart.

Reads one adjacent pinned result and checks rational infinite-tail formulas
and a legal concrete prefix. The all-height proof is in the companion report.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import gcd
from pathlib import Path
import argparse
import json


def need(ok, message):
    if not ok:
        raise ValueError(message)


def prefix(p, height):
    if p == 3:
        return [(3, 0), (9, 1), (27, 4)] + [
            (3 ** n, 13 + 27 * 3 ** (n - 4)) for n in range(4, height + 1)]
    return [(5, 0), (25, 1)] + [
        (5 ** n, 11 + 25 * 5 ** (n - 3)) for n in range(3, height + 1)]


def verify(root):
    raw = (root / 'tube.json').read_bytes()
    need(sha256(raw).hexdigest() == '10cc4fb16f5c4db94fbdb227c9a6a524ca7bc34e52ba3881d6f9dcfda30a0b64',
         'pinned common-functional tube result')
    tube = json.loads(raw)
    reserve, bound = F(tube['reserve_lower']), F(tube['common_G_upper'])
    cases = []
    for h3, h5 in ((13, 8), (13, 9), (14, 8)):
        alpha = F(3) ** (3 - h3)
        beta = F(5) ** (2 - h5)
        need(alpha == 2 * 27 * F(3) ** (-h3 - 1) / (1 - F(1, 3)), 'ternary tail series')
        need(beta == 20 * 5 * F(5) ** (-h5 - 1) / (1 - F(1, 5)), 'quinary tail series')
        rho = max((1 + F(3, 5) * alpha) * (1 + beta / 11), 1 + beta / 7)
        slack = 14 * reserve - rho * bound
        need((slack > 0) == ((h3, h5) != (13, 8)), 'positive screen and negative screen control')
        cases.append(dict(height3=h3, height5=h5, additional_pure_phase_conditions=h3+h5-5,
                          bad3_upper=str(alpha), bad5_upper=str(beta),
                          weight_multiplier_upper=str(rho), slack_lower=str(slack),
                          screen_certifies=slack > 0))
    p3, p5 = prefix(3, 14), prefix(5, 9)
    for sequence in (p3, p5):
        for i, (m, a) in enumerate(sequence):
            need(0 <= a < m, 'canonical pure phase')
            for n, b in sequence[:i]:
                need((a-b) % gcd(m, n) != 0, 'same-prime cylinders disjoint')
    anchors = [(15, 2), (45, 8), (75, 56)]
    all_classes = p3 + p5 + anchors
    need(len({m for m,a in all_classes}) == len(all_classes), 'distinct numerical labels')
    for m, a in anchors:
        for n, b in all_classes:
            if n < m and m % n == 0:
                need((a-b) % n != 0, 'selected anchor avoids every selected proper divisor')
    need(all(a % 27 in (13,22) for m,a in p3[3:]), 'good ternary prefix')
    need(all(a % 5 == 1 and a % 25 != 56 % 25 for m,a in p5[2:]), 'good quinary prefix, zero75 overlap')
    need(max(F(1,59049),F(1,78125)) < F(tube['tube_radius_in_raw_parameter_interpolation']),
         '13/9 prefix also lies in the uniform tube')

    # Exact raw-mixture construction at an interior boundary of the uniform tube.
    tau = F(1,50000)
    for u in (F(0), F(2,7), F(1)):
        for a,b in ((F(0),F(0)), (tau,tau), (F(1,59049),F(1,78125))):
            z = {13: (1-a)*u/2, 22: (1-a)*(1-u)/2, 7: a/2}
            s = z[13]+z[22]
            edge = {13:z[13]/(2*s),22:z[22]/(2*s),7:F(0)}
            vz = {h:(z[h]-(1-tau)*edge[h])/tau for h in z}
            # Split the quinary bad budget between an outside column and75 overlap.
            t2,e = b/40,b/40
            t1 = F(1,20)-t2
            vt1,vt2,ve = (t1-(1-tau)/20)/tau,t2/tau,e/tau
            need(all(v >= 0 for v in vz.values()) and sum(vz.values()) == F(1,2), 'mixture ternary simplex')
            need(vt1 >= 0 and vt2 >= 0 and vt1+vt2 == F(1,20) and 0 <= ve <= vt1, 'mixture quinary simplex and overlap')
    return {
        'scope':'Fixed source chart and unchanged complete-query schedule. Conditions are on one completed source, not a reduction of every odd cover to this prefix.',
        'tube_result_sha256':sha256(raw).hexdigest(),
        'cases':cases,
        'prefix3_example':p3, 'prefix5_example':p5, 'selected_anchors_example':anchors,
        'general_tail_identity':'bad3<=3^(3-H3); bad5<=5^(2-H5), with outside-column and75-overlap events disjoint',
        'raw_mixture_criterion':'For 0<tau<1: theta in (1-tau)*edge+tau*legal_domain iff max(1-2*(z13+z22),1-20*(t1-e))<=tau',
        'negative_control_boundary':'The13/8 lower screen fails; this is not infeasibility, a query counterexample, or a lower bound on the required prefix length.',
        'verification':'Exact rational tails and finite prefix legality. General arbitrary-height statements follow from geometric series and same-source disjointness, not finite sampling. No geometry or Lean verification.',
    }


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--package',type=Path,default=Path(__file__).resolve().parent)
    args=parser.parse_args()
    print(json.dumps(verify(args.package),sort_keys=True,indent=2))
