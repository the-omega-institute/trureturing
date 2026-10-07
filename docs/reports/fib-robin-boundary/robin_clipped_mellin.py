"""Directed Mellin responses of clipped profiles, consuming existing FIB399 data."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

import flint
from flint import acb, arb, ctx, fmpq

from robin_kernel_diagonal import enclosure
from robin_kernel_ratio import load_ball


def profile(u, a, d, c):
    return a*u**2/2 + (d-a)*u + c


def closed_transform(z, low, high, a, d, c):
    if z == 1:
        def primitive(u):
            return a*u**3/6 + (d-a)*u**2/2 + c*u
        return acb(primitive(high) - primitive(low))
    w = z - 1

    def primitive(u):
        return (w*u).exp() * (profile(u, a, d, c)/w
                               - (a*u+d-a)/w**2 + a/w**3)
    return (primitive(high) - primitive(low))/z


def integrated_transform(z, low, high, a, d, c):
    # The callback is entire in u; no branch cut is ignored by the analytic flag.
    return acb.integral(
        lambda u, _: profile(u, a, d, c) * ((z-1)*u).exp()/z,
        low, high, rel_tol=arb(2)**(-ctx.prec+32),
        abs_tol=arb(2)**(-ctx.prec+32))


def complex_enclosure(value):
    return {'real': enclosure(value.real), 'imag': enclosure(value.imag)}


def produce(source, precision):
    if precision < 128:
        raise ValueError('At least 128 bits required')
    ctx.prec = precision
    raw = source.read_bytes()
    data = json.loads(raw)
    if data['profile'] != 'p(u)=A*u^2/2+(D-A)*u+c_diag':
        raise ValueError('The declared FIB399 profile source is required')
    a, d, c = [load_ball(data[key]) for key in ['A', 'D', 'c_diag']]
    if not (a > 0 and d > a and c < 0):
        raise ValueError('Actual source parameter range is required')
    if not (load_ball(data['negative_profile']) < 0
            < load_ball(data['positive_profile'])):
        raise ValueError('Existing source sign brackets are required')
    ell0 = int(data['common_log_threshold_strict_integer'])
    margins = {
        'negative': -load_ball(data['negative_profile'])
                    - load_ball(data['negative_allowance'])/ell0,
        'positive': load_ball(data['positive_profile'])
                    - load_ball(data['positive_allowance'])/ell0}
    if not (ell0 > load_ball(data['monotonic_log_threshold_upper'])
            and all(value > 0 for value in margins.values())):
        raise ValueError('Existing scale must pay both actual density sign margins')

    windows = [('negative', fmpq(0), fmpq(1, 100), -1),
               ('positive', fmpq(3, 100), fmpq(4, 100), 1)]
    rows = []
    for name, low_q, high_q, sign in windows:
        low, high = arb(low_q), arb(high_q)
        if not (sign*profile(low, a, d, c) > 0
                and sign*profile(high, a, d, c) > 0):
            raise ValueError('This window must retain its claimed profile sign')
        width, center = high-low, (high+low)/2
        mass = sign*(arb(fmpq(1, 2))*closed_transform(
            acb(fmpq(1, 2)), low, high, a, d, c)).real
        if not mass > 0:
            raise ValueError('Positive sector mass required')
        for tau in [0, 14, 100, 300]:
            z = acb(fmpq(1, 2), tau)
            closed = closed_transform(z, low, high, a, d, c)
            integral = integrated_transform(z, low, high, a, d, c)
            if not (closed.is_finite() and integral.is_finite()
                    and closed.overlaps(integral)):
                raise ValueError('Independent directed forms disagree')
            cosine = (abs(tau)*width/2).cos()
            if not (abs(tau)*width < arb.pi() and cosine > 0):
                raise ValueError('Strict sector condition required')
            projection = (sign*z*acb(0, -tau*center).exp()*closed).real
            lower_bound = cosine*mass/abs(z)
            # FIB402.5, conditional on the manuscript exact-kernel bridge.
            unweighted_mass = 2*((-low/2).exp()-(-high/2).exp())
            actual_lower = cosine*margins[name]*unweighted_mass/abs(z)
            if not (projection > 0 and lower_bound > 0
                    and actual_lower > 0
                    and not closed.contains(0) and not integral.contains(0)):
                raise ValueError('Directed sector and nonzero checks required')
            rows.append({'window': name, 'u0': str(low_q), 'u1': str(high_q),
                         'sigma': '1/2', 'tau': tau,
                         'closed_transform': complex_enclosure(closed),
                         'integrated_transform': complex_enclosure(integral),
                         'signed_centered_projection': enclosure(projection),
                         'sector_absolute_lower_bound': enclosure(lower_bound),
                         'conditional_actual_ellT_lower_bound': enclosure(actual_lower)})
        closed = closed_transform(acb(1), low, high, a, d, c)
        integral = integrated_transform(acb(1), low, high, a, d, c)
        if not (closed.is_finite() and integral.is_finite()
                and closed.overlaps(integral) and sign*closed.real > 0):
            raise ValueError('Removable z=1 value must agree with direct integration')
        rows.append({'window': name, 'u0': str(low_q), 'u1': str(high_q),
                     'sigma': '1', 'tau': 0,
                     'closed_transform': complex_enclosure(closed),
                     'integrated_transform': complex_enclosure(integral),
                     'removable_value': True})

    return {'scope': 'FIB401 continuous clipped-window templates and FIB402 conditional actual-kernel allowances, not integer-window realizations or signed H sums. Existing FIB399 scalar data are consumed; old Binet, inverse-kernel, PNT, and zero enumeration calculations are not rerun. Analytic applications not Lean verified.',
            'runtime': {'python': sys.version.split()[0],
                        'python_flint': flint.__version__, 'precision_bits': precision},
            'source_name': source.name,
            'source_sha256': hashlib.sha256(raw).hexdigest(),
            'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'transform': 'T(z)=(1/z)*integral_[u0,u1] p(u)*exp((z-1)*u) du',
            'sector_condition': 'Re(z)>0, p has strict fixed sign, abs(Im(z))*(u1-u0)<pi',
            'actual_log_scale': ell0,
            'actual_density_margins': {key: enclosure(value)
                                       for key, value in margins.items()},
            'actual_bound_condition': 'FIB399 exact kernel bridge and global monotonicity; ell>=actual_log_scale; reported actual bound is for abs(ell*T_actual), not abs(T_actual)',
            'rows': rows,
            'not_claimed': ['a zeta zero position at tau=14',
                            'an arithmetic sign for any actual H-weighted window',
                            'a contour-shift or infinite residue expansion',
                            'a Lean proof', 'Robin or RH']}


def render(data):
    lines = ['# Clipped-profile Mellin responses', '', data['scope'], '',
             'Both windows have logarithmic width 1/100. The manuscript sector bound',
             'applies throughout abs(Im(z)) < 100*pi when Re(z)>0; the sampled',
             'frequencies below are integer parameters, not asserted zeta zero positions.',
             '', 'The final column is conditional on the manuscript exact-kernel bridge',
             'and uses ell={}; it bounds abs(ell*T_actual).'.format(data['actual_log_scale']),
             '', '| Window | sigma | tau | Sector lower bound for abs(T) | Conditional lower bound for abs(ell*T_actual) |',
             '| --- | --- | --- | --- | --- |']
    for row in data['rows']:
        if 'sector_absolute_lower_bound' in row:
            lines.append('| {} | {} | {} | {} | {} |'.format(
                row['window'], row['sigma'], row['tau'],
                row['sector_absolute_lower_bound']['display'],
                row['conditional_actual_ellT_lower_bound']['display']))
    lines.extend(['', 'Closed endpoint formulas and independent Arb integrals overlap',
                  'for all ten responses, including the removable z=1 value in both windows.',
                  'The JSON stores their exact outward dyadic endpoints.', '',
                  'Source: [existing ratio data](robin-kernel-ratio.json).',
                  'Data: [directed responses](robin-clipped-mellin.json).',
                  'Producer: [robin_clipped_mellin.py](robin_clipped_mellin.py).', '',
                  'Reproduce with Python 3.13 and python-flint 0.9.0:', '', '```sh',
                  'uv run --python 3.13 --with python-flint==0.9.0 python docs/reports/fib-robin-boundary/robin_clipped_mellin.py --source docs/reports/fib-robin-boundary/robin-kernel-ratio.json --output /tmp/robin-clipped-mellin.json --report /tmp/robin-clipped-mellin.md',
                  '```', '', 'No actual arithmetic cancellation or full Robin/RH conclusion follows.'])
    return '\n'.join(lines)+'\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--report', required=True, type=Path)
    parser.add_argument('--precision', default=192, type=int)
    args = parser.parse_args()
    result = produce(args.source, args.precision)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    args.report.write_text(render(result))
    print(json.dumps({'responses': len(result['rows']),
                      'source_name': result['source_name'],
                      'precision_bits': args.precision}))


if __name__ == '__main__':
    main()
