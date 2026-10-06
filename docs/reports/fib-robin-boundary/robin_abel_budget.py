"""Exact rational Abel budget from existing FIB scalar enclosures.

Python 3.9+ standard library; inputs and output are explicit paths.
This consumes scalar data and literature constants, without recomputing
Binet coefficients, inverse kernels, Mertens sums or zeta zeros.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path


def dyadic(pair):
    mantissa, exponent = map(int, pair)
    return F(mantissa * 2**max(exponent, 0), 2**max(-exponent, 0))


def bounds(row):
    lower, upper = (dyadic(row[k]) for k in ['lower_dyadic', 'upper_dyadic'])
    if lower > upper:
        raise ValueError('Ordered scalar endpoints required')
    return lower, upper


def produce(ratio_source, diagonal_source):
    ratio_raw, diagonal_raw = ratio_source.read_bytes(), diagonal_source.read_bytes()
    ratio, diagonal = json.loads(ratio_raw), json.loads(diagonal_raw)
    diagonal_hash = hashlib.sha256(diagonal_raw).hexdigest()
    if ratio['source_sha256'] != diagonal_hash:
        raise ValueError('The ratio and diagonal must have the same actual source')
    if diagonal['parameter'] != 'q=(3-sqrt(5))/2=phi^(-2)':
        raise ValueError('The declared actual golden source is required')
    q_low, q_high = bounds(diagonal['q'])
    if not 0 < q_low <= q_high < F(2, 5):
        raise ValueError('Actual q must be strictly between zero and 2/5')
    caps = {'mu0_upper': 62, 'A': 4, 'D': 5}
    for key, cap in caps.items():
        lower, upper = bounds(ratio[key])
        if not 0 < lower <= upper < cap:
            raise ValueError('Positive actual scalar below declared cap required: '+key)
    for key in ['A', 'D']:
        low_r, high_r = bounds(ratio[key])
        low_d, high_d = bounds(diagonal[key])
        if max(low_r, low_d) > min(high_r, high_d):
            raise ValueError('Scalar source enclosures must agree: '+key)

    threshold = F('4589.20')
    mertens_low_constant, mertens_high_constant = F('2.91890'), F('33.56')
    zero_free_constant = F('5.56')
    cm = mertens_low_constant * threshold**4
    # L^7 exp(-sqrt(L/5.56)) decreases once L >=196*5.56.
    if not threshold > 196 * zero_free_constant:
        raise ValueError('Literature threshold must lie in decreasing range')
    # sqrt(4589.20/5.56)>28; exp(28) exceeds its positive Taylor prefix.
    exp_lower = sum((F(28)**n / factorial(n) for n in range(101)), F(0))
    high_at_threshold_cap = mertens_high_constant * threshold**7 / exp_lower
    if not (threshold > 28**2 * zero_free_constant
            and high_at_threshold_cap < cm < F(13 * 10**14)):
        raise ValueError('Two literature regimes must join under global Mertens cap')

    c6_cap = F(10**17)
    beta_harmonic_cap = F(10, 9)  # q/(1-q)^2 <10/9.
    h_main_cap = 64 * beta_harmonic_cap * cm
    h_tail_cap = 64 * F(25, 9) * 10**5
    if not h_main_cap + h_tail_cap < c6_cap:
        raise ValueError('The full actual H budget must fit C6')

    # log(2)>2/3 and log(2)<1, with the consumed scalar caps.
    log2_lower = F(2, 3)
    a2, a1, a0 = F(66), F(212), F(248)
    h1_cap = F(2, 5)  # log(1+q)<=q<2/5.
    # Integral comparison for S_p=sum_{k>=2}1/(k log^p k).
    sp = {p: 1/(2*log2_lower**p)
          + 1/((p-1)*log2_lower**(p-1)) for p in range(3, 7)}
    # For k>=2, t in [k,k+1], (t/k)^p <=(3/2)^p <=9/4.
    # Thus U_r(p)<=9/4*r!/(p-1)^(r+1); r=0 uses decreasing comparison.
    ordinary_q_sum_cap = a2*F(9, 2) + a1*F(9, 4) + a0
    half_q_sum_cap = a2*36 + a1*9 + a0*2
    h_log_component = c6_cap * (a2*sp[3] + a1*sp[4] + a0*sp[5])
    h1_component = h1_cap * ordinary_q_sum_cap
    inner_low_component = c6_cap / log2_lower**6 * half_q_sum_cap
    inner_high_component = 64*c6_cap*(a2*sp[4] + a1*sp[5] + a0*sp[6])
    cstar_bound = h_log_component + h1_component + inner_low_component + inner_high_component
    cstar_cap = F(3*10**22)
    if not cstar_bound < cstar_cap:
        raise ValueError('Every full Abel budget component must fit Cstar cap')

    def exact(value):
        return {'numerator': str(value.numerator), 'denominator': str(value.denominator)}

    return {
        'scope': 'Exact rational consumer for the full FIB Robin Abel budget, using existing actual scalar enclosures and original explicit Mertens bounds. Analytic transport is paper-only, not Lean verified. No remaining-frequency signed estimate or RH proof.',
        'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'sources': {
            'ratio': {'name': ratio_source.name, 'sha256': hashlib.sha256(ratio_raw).hexdigest()},
            'diagonal': {'name': diagonal_source.name, 'sha256': diagonal_hash},
            'mertens_low': {
                'url': 'https://arxiv.org/html/2408.04143v3#Sx2.Thmtheorem1',
                'identifier': 'arXiv:2408.04143v3, Theorem A.1, (A.5)',
                'publication_doi': '10.1080/10586458.2025.2483942',
                'domain': 'all real x>1', 'constant': '2.91890', 'log_power': 2},
            'mertens_high': {
                'url': 'https://arxiv.org/html/2208.06141v5#S1.Thmtheorem1',
                'identifier': 'arXiv:2208.06141v5, Theorem 1.1, (10)',
                'version_date': '2026-09-09', 'publication_status': 'preprint version',
                'domain': 'all real x>=exp(4589.20)',
                'constant': '33.56', 'sqrt_denominator': '5.56'}},
        'actual_scalar_caps': {**caps, 'q_upper': '2/5'},
        'qk_coefficient_caps': {'a2': '66', 'a1': '212', 'a0': '248'},
        'mertens_constant': exact(cm),
        'exp28_taylor_terms': 101,
        'high_at_threshold_upper': exact(high_at_threshold_cap),
        'H_main_upper': exact(h_main_cap), 'H_tail_upper': exact(h_tail_cap),
        'C6_upper': exact(c6_cap),
        'Sp_upper': {str(p): exact(v) for p,v in sp.items()},
        'Cstar_components_upper': {
            'Hk_logk': exact(h_log_component), 'H1': exact(h1_component),
            'inner_low': exact(inner_low_component), 'inner_high': exact(inner_high_component)},
        'Cstar_bound_upper': exact(cstar_bound), 'Cstar_upper': exact(cstar_cap),
        'epsilon_coefficient': exact(1/(2*cstar_cap)),
        'schedule': 'epsilon_x=epsilon_coefficient/(sqrt(x)*log(x)), x>=exp(1)',
        'error_bound': '|I_epsilon(x)-I_psi(x)|<=1/(sqrt(x)*log(x)^2)',
        'not_claimed': ['a sharp numerical constant', 'a published-only source chain',
                        'a Lean verification', 'a signed bound on I_epsilon',
                        'the missing full-frequency critical budget', 'Robin or RH']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ratio-source', type=Path, required=True)
    parser.add_argument('--diagonal-source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = produce(args.ratio_source, args.diagonal_source)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['C6_upper','Cstar_upper','epsilon_coefficient']},indent=2))


if __name__ == '__main__':
    main()
