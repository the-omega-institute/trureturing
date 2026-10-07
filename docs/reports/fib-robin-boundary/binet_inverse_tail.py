"""Directed quarter-moment budget for the actual Binet Dirichlet inverse."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

import flint
from flint import arb, ctx, fmpq


def endpoints(value):
    if not value.is_finite():
        raise ValueError('Finite directed enclosure required')
    return {'display': str(value),
            'lower_dyadic': [str(x) for x in value.lower().man_exp()],
            'upper_dyadic': [str(x) for x in value.upper().man_exp()]}


def fibonacci_cuts(limit):
    left, right, index = 0, 1, 0
    result = []
    while left <= limit:
        if index >= 3 and index % 3 == 0:
            result.append((index, left))
        left, right, index = right, left+right, index+1
    return result


def produce(terms=64, inverse_cutoff=2584, precision=192):
    if precision < 128 or terms < 16 or inverse_cutoff < 2:
        raise ValueError('At least 128 bits, 16 head terms and inverse cutoff 2 required')
    ctx.prec = precision
    q = (3-arb(5).sqrt())/2
    if not 0 < q < 1:
        raise ValueError('Actual golden parameter inside (0,1) required')

    def beta(index):
        return (-(-q)**index).log1p()

    head = beta(1)
    weighted_head = sum((abs(beta(d))*arb(d).root(4)
                         for d in range(2, terms+1)), arb(0))
    # d^(1/4)<=d and |log(1-(-q)^d)|<=q^d/(1-q).
    omitted = (q**(terms+1)*((terms+1)-terms*q)/(1-q)**3).upper()
    # Pay the exported endpoint budgets before forming the point gap.
    gap_lower = (head.lower()-weighted_head.upper()-omitted).lower()
    if not gap_lower > arb(fmpq(7, 500)):
        raise ValueError('Complete quarter-moment gap >7/500 required')
    inverse_norm_upper = (1/gap_lower).upper()
    if not inverse_norm_upper < arb(fmpq(500, 7)):
        raise ValueError('Complete weighted inverse allowance <500/7 required')

    coefficients = [arb(0)] + [beta(d) for d in range(1, inverse_cutoff+1)]
    divisors = [[] for _ in range(inverse_cutoff+1)]
    for d in range(2, inverse_cutoff+1):
        for multiple in range(d, inverse_cutoff+1, d):
            divisors[multiple].append(d)
    inverse = [arb(0), 1/head]
    rows = [{'index': 1, 'inverse_coefficient': endpoints(inverse[1])}]
    prefix_moment = abs(inverse[1])
    cuts = dict(fibonacci_cuts(inverse_cutoff))
    by_cut = {value: index for index, value in cuts.items()}
    resolutions = []
    for n in range(2, inverse_cutoff+1):
        value = -sum((coefficients[d]*inverse[n//d] for d in divisors[n]), arb(0))/head
        if not value.is_finite():
            raise ValueError('Finite actual inverse coefficient required')
        inverse.append(value)
        convolution = head*value+sum((coefficients[d]*inverse[n//d] for d in divisors[n]), arb(0))
        if not convolution.contains(0):
            raise ValueError('Finite Dirichlet inverse identity enclosure required')
        prefix_moment += abs(value)*arb(n).root(4)
        rows.append({'index': n, 'inverse_coefficient': endpoints(value)})
        if n in by_cut:
            root = arb(n+1).root(4)
            remaining = (inverse_norm_upper-prefix_moment.lower()).upper()
            if not remaining > 0:
                raise ValueError('Positive remaining complete moment allowance required')
            # Pay the computed visible prefix with its lower endpoint.
            resolutions.append({'fibonacci_index': by_cut[n], 'kernel_cutoff': n,
                                'inverse_prefix_quarter_moment': endpoints(prefix_moment),
                                'remaining_quarter_moment_upper': endpoints(remaining),
                                'Xhalf_global_cap_reference': endpoints((arb(fmpq(500, 7))/root**3).upper()),
                                'X0_tail_allowance': endpoints((remaining/root).upper()),
                                'Xhalf_tail_allowance': endpoints((remaining/root**3).upper()),
                                'X1_tail_allowance': endpoints((remaining/root**5).upper())})
    if not prefix_moment.upper() < inverse_norm_upper:
        raise ValueError('Inverse-prefix quarter moment must fit complete allowance')
    # Independent prime and prime-square coefficient identities within the prefix.
    prime = -coefficients[2]/head**2
    square = coefficients[2]**2/head**3-coefficients[4]/head**2 if inverse_cutoff >= 4 else None
    if not (inverse[2]-prime).contains(0):
        raise ValueError('Prime inverse coefficient comparison required')
    if square is not None and not (inverse[4]-square).contains(0):
        raise ValueError('Prime-square inverse coefficient comparison required')

    return {'scope': 'Conditional directed actual Binet quarter-moment and inverse-resolution allowance; weighted inversion and existing actual summatory reconstruction are reused. No new Lean, actual square-root cancellation, Robin sign, RH or originality certificate.',
            'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__, 'precision_bits': precision},
            'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'parameter': 'q=(3-sqrt(5))/2=phi^(-2)', 'moment_exponent_exact': '1/4',
            'retained_beta_terms': terms, 'inverse_cutoff': inverse_cutoff,
            'q': endpoints(q), 'head': endpoints(head),
            'weighted_tail_retained': endpoints(weighted_head),
            'weighted_tail_omitted_upper': endpoints(omitted),
            'complete_gap_lower': endpoints(gap_lower),
            'complete_inverse_quarter_moment_upper': endpoints(inverse_norm_upper),
            'inverse_prefix_quarter_moment': endpoints(prefix_moment),
            'inverse_coefficients': rows, 'fibonacci_resolutions': resolutions,
            'references': {'weighted_algebra': 'Gloeckner-Lucht arXiv:1112.0749v2 Proposition 1, pp.4-5',
                           'small_norm_inverse': 'same source Theorem 2(a), p.4; geometric Neumann norm bound',
                           'actual_reconstruction': 'FIBONACCI_ATOMIC_RELATION_GENERATION.md sections384-387'},
            'not_used': ['Theorem 1 admissible-weight spectral criterion for the exponential log-index weight',
                         'old theta or arithmetic grid producers', 'unknown global H square-root bound']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--terms', type=int, default=64)
    parser.add_argument('--inverse-cutoff', type=int, default=2584)
    parser.add_argument('--precision', type=int, default=192)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = produce(args.terms, args.inverse_cutoff, args.precision)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ['complete_gap_lower', 'complete_inverse_quarter_moment_upper',
                                                 'inverse_prefix_quarter_moment', 'fibonacci_resolutions']}, indent=2))


if __name__ == '__main__':
    main()
