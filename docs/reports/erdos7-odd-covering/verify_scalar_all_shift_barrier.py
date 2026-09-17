#!/usr/bin/env python3
"""Exact scalar countermodel for all square shifts at fixed17/T8,19/T8.

The independent two-point source satisfies 21 published scalar observations.
Full geometric auxiliary tails and a three-piece affine calculation certify
that the specified common-N functional stays positive for every square shift.
No actual congruence realization, other-schedule barrier, or Lean claim follows.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PINS = {
    'certificates/shared_square_continuation_certificate.json':
        '5368499e7747e43960ee05073ef7563bfa2a0cfc90a1c32a749ab388cc946099',
    'certificates/shared_cell_square_certificate.json':
        'df746d03d242d44a1cfe85d6ee6d283b3495af155320e970140f69912479fe0d',
}


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def source_observations(sources, law):
    continuation = sources['certificates/shared_square_continuation_certificate.json']
    square = sources['certificates/shared_cell_square_certificate.json']
    require(continuation['schema'] == 'erdos7-shared-square-continuation-v1',
            'continuation source schema')
    require(square['schema'] == 'erdos7-shared-cell-square-v1',
            'square source schema')
    require(continuation['source_sha256']['certificates/shared_cell_square_certificate.json']
            == PINS['certificates/shared_cell_square_certificate.json'], 'same SQ source')
    source = continuation['source']
    targets = {r['tau']: r for r in square['targets']}
    require(set(targets) == {16, 81} and len(square['targets']) == 2,
            'exact two SQ targets')
    require(F(source['Gamma13']) == F(targets[16]['shift_square']),
            'same Gamma13 observation')
    require(F(source['T81']) == F(targets[81]['supported_hinge']),
            'same T81 observation')
    require(F(targets[16]['shift_square'])
            == 16 + F(targets[16]['supported_hinge']), 'SQ16 shift identity')
    require(set(source['hinges']) == {str(h) for h in range(1, 18)},
            'all and only H1 through H17')
    observations = []

    def check(name, value, upper):
        upper = F(upper)
        require(value <= upper, 'scalar observation: ' + name)
        observations.append(dict(name=name, value=value, upper=upper,
                                 slack=upper-value))

    check('mean', sum(w*x for x, w in law.items()), source['mean'])
    check('square', sum(w*x*x for x, w in law.items()), source['Gamma13'])
    for h in range(1, 18):
        check('H'+str(h), sum(w*max(x-h, 0) for x, w in law.items()),
              source['hinges'][str(h)])
    for tau in (16, 81):
        check('T'+str(tau), sum(w*max(x*x-tau, 0) for x, w in law.items()),
              targets[tau]['supported_hinge'])
    require(len(observations) == 21, 'clause-complete scalar observation count')
    return observations


def parameters(p):
    require(p in (17, 19), 'fixed schedule primes')
    return dict(p=p, threshold=8, a=F(3*p-1, (p-1)**2),
                c=F(p-1, p-9), charge_denominator=p-9,
                minimum_kappa_denominator=p-9)


def diagonal_coefficients(p, t):
    """H_direct(p,W;t,t) = W*b + s, exactly."""
    require(t >= 1, 'positive diagonal source')
    par = parameters(p)
    kappa = F(p-1, p-1-min(t, 8))
    return max(F(t)-8, F(0))/F(p-9), par['a']*kappa*t*t


def n_mass(n):
    require(n >= 1, 'positive auxiliary value')
    return F(15, 17) if n == 1 else F(32, 17**n)


def auxiliary_moments():
    r = F(1, 17)
    # Sum r^n, n*r^n, n^2*r^n for n >= 0, then remove n=0,1
    # and insert the separately specified atom P(N=1)=15/17.
    geometric = [1/(1-r), r/(1-r)**2, r*(1+r)/(1-r)**3]
    moments = {j: F(15, 17)+32*(geometric[j]-(1 if j == 0 else 0)-r)
               for j in range(3)}
    require(moments == {0: F(1), 1: F(9, 8), 2: F(89, 64)},
            'complete auxiliary probability, mean and square')
    return moments


def full_tail(cut, moments):
    require(cut >= 8, 'all-high auxiliary tail')
    finite = {j: sum(n_mass(n)*n**j for n in range(1, cut))
              for j in range(3)}
    tail = {j: moments[j]-finite[j] for j in range(3)}
    r = F(1, 17)
    # Independent shifted geometric formulas, with n=cut+k.
    direct = {
        0: 32*r**cut/(1-r),
        1: 32*r**cut*(F(cut)/(1-r)+r/(1-r)**2),
        2: 32*r**cut*(F(cut*cut)/(1-r)+2*cut*r/(1-r)**2
                      +r*(1+r)/(1-r)**3),
    }
    require(tail == direct and all(v > 0 for v in tail.values()),
            'independent complete geometric tail moments')
    return dict(cut=cut, finite=finite, tail=tail)


def step19(x, tail_record, moments):
    cut = tail_record['cut']
    tail = tail_record['tail']
    finite_b = sum(n_mass(n)*diagonal_coefficients(19, n*x)[0]
                   for n in range(1, cut))
    finite_s = sum(n_mass(n)*diagonal_coefficients(19, n*x)[1]
                   for n in range(1, cut))
    # n >= cut >= 8 and x >= 1 force kappa_19=9/5.
    tail_b = (x*tail[1]-8*tail[0])/10
    tail_s = F(14, 45)*x*x*tail[2]
    require(tail_b >= 0 and tail_s > 0, 'complete tail contributions')
    b, s = finite_b+tail_b, finite_s+tail_s
    if x == 11:
        require(b == (11*moments[1]-8)/10, 'all-high charge formula')
        require(s == F(14, 45)*121*moments[2], 'all-high square formula')
    return dict(x=x, finite_b=finite_b, tail_b=tail_b, b=b,
                finite_s=finite_s, tail_s=tail_s, s=s)


def compute(sources):
    law = {1: F(7, 100), 11: F(93, 100)}
    require(sum(law.values()) == 1 and all(w > 0 for w in law.values()),
            'abstract positive probability')
    observations = source_observations(sources, law)
    mean = sum(w*x for x, w in law.items())
    square = sum(w*x*x for x, w in law.items())
    require(mean == F(103, 10) and square == F(563, 5), 'source moments')
    moments = auxiliary_moments()
    tails = [full_tail(cut, moments) for cut in (8, 16)]
    steps = []
    for record in tails:
        rows = [step19(x, record, moments) for x in law]
        steps.append(dict(cut=record['cut'], given_x=rows,
                          b=sum(law[r['x']]*r['b'] for r in rows),
                          s=sum(law[r['x']]*r['s'] for r in rows)))
    require(steps[0]['b'] == steps[1]['b']
            and steps[0]['s'] == steps[1]['s'], 'two full-tail decompositions')
    for i in range(2):
        require(steps[0]['given_x'][i]['b'] == steps[1]['given_x'][i]['b']
                and steps[0]['given_x'][i]['s'] == steps[1]['given_x'][i]['s'],
                'two decompositions for each source atom')
    b17 = sum(w*diagonal_coefficients(17, x)[0] for x, w in law.items())
    s17 = sum(w*diagonal_coefficients(17, x)[1] for x, w in law.items())
    b19, s19 = steps[0]['b'], steps[0]['s']
    B, S = b17+b19, s17+s19
    require(B == F(620124319573, 820677346000), 'total charge coefficient')
    require(S == F(313229334820050587, 3379877581766400), 'direct square term')
    require(F(7, 100) < B < 1, 'three affine-piece slope signs')

    def defect(tau):
        return sum(w*max(F(x*x)-tau, F(0)) for x, w in law.items()) \
            + S-(484-tau)*(1-B)

    # The complete two-atom square hinge yields these exact affine pieces.
    # No load-domain cutoff, optimizer, or sampling supplies this identity.
    intervals = [(0, 1, square+S-484*(1-B), -B),
                 (1, 121, F(93, 100)*121+S-484*(1-B), F(7, 100)-B),
                 (121, 484, S-484*(1-B), 1-B)]
    piece_records = []
    for lo, hi, intercept, slope in intervals:
        require(intercept+slope*lo == defect(F(lo))
                and intercept+slope*hi == defect(F(hi)),
                'affine pieces agree at both boundary points')
        piece_records.append(dict(interval=[lo, hi], intercept=intercept,
                                  slope=slope, left_value=defect(F(lo)),
                                  right_value=defect(F(hi))))
    minimum = defect(F(121))
    require(minimum == S-363*(1-B)
            == F(67033659073176343, 16899387908832000), 'exact minimum')
    require(minimum > 0, 'strict positive all-shift barrier')
    require(piece_records[0]['slope'] < 0 and piece_records[1]['slope'] < 0
            and piece_records[2]['slope'] > 0, 'minimum occurs at121')
    for p in (17, 19):
        par = parameters(p)
        require(par['a'] > 0 and par['c'] > 0
                and par['minimum_kappa_denominator'] > 0,
                'pointwise clip-majorization coefficient domain')
    return encode(dict(
        schema='erdos7-scalar-all-shift-barrier-v1', source_sha256=PINS,
        abstract_source=dict(law=law, mean=mean, square=square,
                             independent_auxiliary=True),
        observations=observations, observation_count=len(observations),
        parameters=[parameters(p) for p in (17, 19)],
        auxiliary=dict(atom_one=F(15, 17), tail_mass_coefficient=32,
                       geometric_base=17, full_moments=moments,
                       complete_tail_decompositions=tails),
        step17=dict(b=b17, s=s17), step19=steps,
        direct_functional=dict(B=B, S=S, square_shift_interval=[0, 484],
                               affine_pieces=piece_records, minimum_shift=121,
                               minimum_defect=minimum),
        clip_majorization=dict(
            domain='p in {17,19}, z>=0, y>=0, K>=0',
            identity='H_K-H_direct=a_p*(c_p-kappa_p(z))*(y^2-min(y^2,K))',
            sign_reason='min(z,8)<=8 implies 0<kappa_p(z)<=c_p; both remaining factors are nonnegative'),
        scope='Abstract scalar countermodel to closing the fixed17/T8,19/T8 common-N functional for any real0<=tau<=484 or any pointwise-majorizing clip. Exactly21 published upper observations are checked. No congruence realization, actual AP13 law, all-schedule barrier, killed-frontier lower bound, or Lean endpoint is asserted.',
        open_mathematical_obligations='Actual labelled test and bad-mask geometry, and the finite killed frontier, remain outside these scalar observations. Unrestricted Erdos7 remains unresolved.'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--certificate', type=Path,
                        default=HERE/'certificates/scalar_all_shift_barrier_certificate.json')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    sources = {}
    for name, digest in PINS.items():
        raw = read_artifact_bytes(args.source_directory/name)
        require(sha256(raw).hexdigest() == digest, 'source SHA-256: '+name)
        sources[name] = json.loads(raw, object_pairs_hook=unique)
    result = compute(sources)
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2)+'\n')
    else:
        saved = json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique)
        require(saved == result, 'entire certificate equality')
    value = F(result['direct_functional']['minimum_defect'])
    print('PASS21 scalar observations; complete N tails at8 and16; '
          'all-shift minimum '+str(value)+' = '+str(float(value))+
          '; ordinary clip-majorization proof applies for every K>=0')


if __name__ == '__main__':
    main()
