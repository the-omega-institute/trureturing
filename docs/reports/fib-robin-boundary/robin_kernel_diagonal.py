"""Directed scalar input for the actual centered Robin kernel diagonal."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

import flint
from flint import acb, arb, arb_series, ctx, fmpq


def enclosure(value):
    if not value.is_finite():
        raise ValueError('A finite directed enclosure is required')
    return {'display': str(value),
            'lower_dyadic': [str(x) for x in value.lower().man_exp()],
            'upper_dyadic': [str(x) for x in value.upper().man_exp()]}


def produce(terms=64, precision=192):
    if terms < 16 or precision < 128:
        raise ValueError('At least 16 Binet terms and 128 bits are required')
    ctx.prec = precision
    q = (3-arb(5).sqrt())/2
    if not 0 < q < 1:
        raise ValueError('The actual golden parameter must lie in (0,1)')
    beta = [arb(0)] + [(-(-q)**n).log1p() for n in range(1, terms+1)]
    logs = [arb(0)] + [arb(n).log() for n in range(1, terms+1)]
    b0_head = sum((beta[n]/n for n in range(1, terms+1)), arb(0))
    b1_head = -sum((beta[n]*logs[n]/n for n in range(1, terms+1)), arb(0))
    b2_head = sum((beta[n]*logs[n]**2/n for n in range(1, terms+1)), arb(0))
    # |beta_n| <= q^n/(1-q); log(n)<=n for n>=1.
    tail0 = (q**(terms+1)/((terms+1)*(1-q)**2)).upper()
    tail1 = (q**(terms+1)/(1-q)**2).upper()
    tail2 = (q**(terms+1)*((terms+1)-terms*q)/(1-q)**3).upper()
    b0 = b0_head + arb(0, tail0)
    b1 = b1_head + arb(0, tail1)
    b2 = b2_head + arb(0, tail2)
    if not b0 > 0:
        raise ValueError('The complete actual B(1) must be strictly positive')
    gamma_complex = acb.stieltjes(1)
    if not gamma_complex.imag.is_zero():
        raise ValueError('The real Stieltjes input must have zero imaginary part')
    gamma1 = gamma_complex.real
    # ζ(1+z)-1/z = γ - γ1*z + O(z^2): check the Laurent sign.
    gamma1_jet = -arb_series([1, 1]).zeta(deflate=True)[1]
    if not (gamma1-gamma1_jet).contains(0):
        raise ValueError('The independent Laurent convention comparison failed')
    diagonal = b1**2/b0**3-b2/(2*b0**2)+gamma1/b0
    lower = arb(fmpq(-13, 1000))
    upper = arb(fmpq(-12, 1000))
    if not lower < diagonal < upper:
        raise ValueError('The declared actual negative scalar interval was not verified')
    a = 1/b0
    d = a+b1/b0**2
    moment = d+diagonal
    return {
        'scope': 'Complete directed scalar enclosure for the actual diagonal coefficient. The Mellin moment and kernel-limit application are paper deductions, not Lean-certified conclusions. No full signed H-weighted Robin bound or RH proof.',
        'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__,
                    'precision_bits': precision},
        'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'parameter': 'q=(3-sqrt(5))/2=phi^(-2)',
        'retained_beta_terms': terms,
        'beta_tail_majorant': '|beta_n|<=q^n/(1-q)',
        'moment_tail_majorants': {
            'B(1)': 'q^(N+1)/((N+1)*(1-q)^2)',
            'Bprime(1)': 'q^(N+1)/(1-q)^2',
            'Bsecond(1)': 'q^(N+1)*((N+1)-N*q)/(1-q)^3'},
        'q': enclosure(q), 'B': enclosure(b0), 'Bprime': enclosure(b1),
        'Bsecond': enclosure(b2), 'gamma1': enclosure(gamma1),
        'gamma1_from_deflated_jet': enclosure(gamma1_jet),
        'tails': {'B': enclosure(tail0), 'Bprime': enclosure(tail1),
                  'Bsecond': enclosure(tail2)},
        'A': enclosure(a), 'D': enclosure(d), 'high_residual_moment': enclosure(moment),
        'diagonal_coefficient': enclosure(diagonal),
        'declared_interval': '-13/1000 < c_diag < -12/1000',
        'laurent_convention': 'zeta(1+z)=1/z+gamma-gamma1*z+O(z^2)',
        'references': {
            'actual_source': 'FIBONACCI_ATOMIC_RELATION_GENERATION.md sections385-387,398',
            'stieltjes': 'FLINT acb.stieltjes(1), real ball',
            'jet': 'FLINT arb_series.zeta(deflate=True), coefficient1'},
        'not_claimed': ['an explicit diagonal sign-change threshold',
                        'a uniform-in-x fixed-threshold kernel asymptotic',
                        'a numerical C_H bound', 'a Lean proof', 'full Robin or RH']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--terms', type=int, default=64)
    parser.add_argument('--precision', type=int, default=192)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = produce(args.terms, args.precision)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in
                      ['runtime', 'retained_beta_terms', 'diagonal_coefficient',
                       'declared_interval']}, indent=2))


if __name__ == '__main__':
    main()
