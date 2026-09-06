"""Directed certificate for the retained prime correction after prolate evenization.

The earlier complete prolate verifier is replayed, including its infinite
Legendre tail. No finite-prolate eigenpair is accepted from a black box. The
new calculation integrates the actual piecewise exponential models in closed
form, retaining all mixed terms. It certifies the true prolate model's odd
mass, its actual prime energy, and the error made by discarding the odd-model
correction in the proved prime/Mellin identity.

The mathematical operator/domain and spectral realization arguments are those
in the existing RH theory volume. This program is not a Lean kernel replay.
"""
from __future__ import annotations
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import sys
from mpmath import iv

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not use -O.')
ROOT = Path(__file__).resolve().parent
PINS = {
    'certify_prime3_prolate_model.py': '42dceb5c81f9aabdc12b51a99d29f0929d81e712f815b49b13bbf9bb5ec56039',
    'prime3_prolate_proposal.json': '242c9897bbd247ef0485039e6dcde819a351c5900ceac52fecc420934c1896db',
    'certify_prime3_refined.py': '8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0',
}

def load_reviewed():
    for filename, expected in PINS.items():
        actual = hashlib.sha256((ROOT/filename).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f'Unreviewed dependency: {filename}')
    spec = importlib.util.spec_from_file_location('reviewed_prolate', ROOT/'certify_prime3_prolate_model.py')
    if spec is None or spec.loader is None:
        raise ImportError('Could not load the pinned prolate verifier.')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def rat(x: Fraction | int):
    f = Fraction(x)
    return iv.mpf(f.numerator)/f.denominator

def exp_integral(t: Fraction, left, right):
    return right-left if t == 0 else (iv.exp(rat(t)*right)-iv.exp(rat(t)*left))/rat(t)

def x_exp_integral(t: Fraction, left, right):
    if t == 0:
        return (right**2-left**2)/2
    s = rat(t)
    return (iv.exp(s*right)*(s*right-1)-iv.exp(s*left)*(s*left-1))/s**2

def convolution(first: dict, second: dict) -> dict:
    result = {}
    for t, a in first.items():
        for s, b in second.items():
            result[t+s] = result.get(t+s, rat(0))+a*b
    return result

def integrate_terms(terms: dict, left, right, linear: bool = False):
    f = x_exp_integral if linear else exp_integral
    return sum((v*f(t, left, right) for t, v in terms.items()), rat(0))

def run(digits: int = 110) -> dict:
    if digits < 100:
        raise ValueError('At least 100 decimal interval digits are required.')
    old = load_reviewed()
    previous = old.run(digits)  # Actual replay, not a read of the historical result JSON.
    iv.dps = digits
    data = json.loads((ROOT/'prime3_prolate_proposal.json').read_bytes())
    K, bits = data['dimension'], data['dyadic_bits']
    assert (data['scale_c'], K, bits) == (3, 32, 250)
    c, lam = rat(3), iv.sqrt(3)
    a = iv.ln(3)/2
    shift = iv.ln(2)
    b = a-shift
    assert bool(-a < b) and bool(b < -b) and bool(-b < a)
    v = []
    for proposal in data['proposals']:
        nums = list(map(int, proposal['vector_numerators']))
        norm_sq = sum((Fraction(n*n, 2**(2*bits)) for n in nums), Fraction(0))
        assert norm_sq > 0
        norm = iv.sqrt(rat(norm_sq))
        v.append([rat(Fraction(n, 2**bits))/norm for n in nums])
    eps = Fraction(1, 10**25)  # Independently checked for both modes by old.run above.
    ratio = v[1][0]/v[0][0]
    assert bool(v[0][0] > rat(eps))
    ratio_error = rat(eps)*(1+abs(ratio))/(v[0][0]-rat(eps))
    H_error = rat(eps)+(abs(ratio)+ratio_error)*rat(eps)+ratio_error
    H = [v[1][j]-ratio*v[0][j] for j in range(K)]
    H[0] = rat(0)  # Exact zero from the chosen ratio, not discarded interval uncertainty.
    A = [rat(0) for _ in range(K)]
    for j in range(1, K):
        poly = old.legendre_coefficients(2*j)
        factor = H[j]*iv.sqrt(rat(Fraction(4*j+1, 2)))
        for r in range(j+1):
            A[r] += factor*rat(poly[2*r])/c**r

    def parity_terms(positive: tuple, negative: tuple, sign: int) -> dict:
        out = {}
        for j in range(K):
            t = Fraction(4*j+1, 2)
            out[t] = 2*A[j]*sum(m**(2*j) for m in positive)
            out[-t] = sign*2*A[j]*sum(m**(2*j) for m in negative)
        return out

    intervals = [(-a, b, (1, 2), (1,)), (b, -b, (1,), (1,)), (-b, a, (1,), (1, 2))]
    norm_even_sq, norm_odd_sq, log_pair = rat(0), rat(0), rat(0)
    for left, right, positive, negative in intervals:
        even = parity_terms(positive, negative, 1)
        odd = parity_terms(positive, negative, -1)
        norm_even_sq += integrate_terms(convolution(even, even), left, right)
        norm_odd_sq += integrate_terms(convolution(odd, odd), left, right)
        q0, q1 = {}, {}
        for j in range(K):
            t = Fraction(4*j+1, 2)
            q0[t] = 4*A[j]*sum((m**(2*j)*iv.ln(m) for m in positive), rat(0))
            q1[t] = 4*A[j]*sum(m**(2*j) for m in positive)
        log_pair += integrate_terms(convolution(even, q0), left, right)
        log_pair += integrate_terms(convolution(even, q1), left, right, linear=True)
    assert bool(norm_even_sq > 0) and bool(norm_odd_sq > 0)
    ne, no = iv.sqrt(norm_even_sq), iv.sqrt(norm_odd_sq)

    # Independently integrate the original actual prime-2 translation of the even model.
    # On [-a,b], x+log(2) lies in [-b,a], so these are the exact two expressions.
    left_terms = parity_terms((1, 2), (1,), 1)
    right_terms = {t: value*iv.exp(rat(t)*shift)
                   for t, value in parity_terms((1,), (1, 2), 1).items()}
    V = iv.ln(2)/iv.sqrt(2)
    prime_energy = -2*V*integrate_terms(convolution(left_terms, right_terms), -a, b)
    unit_prime = prime_energy/norm_even_sq
    unit_log_only = -2*log_pair/norm_even_sq
    unit_parity_correction = (prime_energy+2*log_pair)/norm_even_sq

    # Transport the certified prolate L2 error to BOTH p and E(log(t)h).
    # Every actually used seed argument is in [lambda^-1,lambda], so |log(t)|<=a.
    C = 4*iv.sqrt(lam)*sum((1/iv.sqrt(m) for m in range(1,4)), rat(0))
    err = C*H_error
    assert bool(ne > err) and bool(no > err)
    normalized_error = 2*err/ne
    Q = a*C*(1+abs(ratio))  # Rigorous bound for the polynomial log-seed synthesis norm.
    z_error = 2*V*(2*ne+err)*err + 2*(a*ne+Q+a*err)*err
    z_absolute = 2*V*ne**2+2*ne*Q
    ratio_budget = z_error/(ne-err)**2 + z_absolute*(2*ne+err)*err/(ne**2*(ne-err)**2)
    prime_budget = 4*V*normalized_error
    odd_ratio_lower = (no-err)/(ne+err)
    odd_ratio_upper = (no+err)/(ne-err)
    assert bool(odd_ratio_lower > rat(Fraction(76, 10**6)))
    assert bool(odd_ratio_upper < rat(Fraction(77, 10**6)))
    assert bool(unit_parity_correction-ratio_budget > -rat(Fraction(44, 10**8)))
    assert bool(unit_parity_correction+ratio_budget < -rat(Fraction(43, 10**8)))
    assert bool(unit_prime-prime_budget > -rat(Fraction(18173952, 10**9)))
    assert bool(unit_prime+prime_budget < -rat(Fraction(18173950, 10**9)))
    operator_budget = 2*(a+V)*odd_ratio_upper
    assert bool(operator_budget < rat(Fraction(159, 10**6)))
    U = Fraction(560909, 10**13)
    assert Fraction(43, 10**8) > 7*U
    return {
        'scale': 'lambda=sqrt(3), a=log(3)/2; the actual zero-integral prolate line',
        'interval_decimal_digits': digits,
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'dependency_sha256': PINS,
        'prolate_replay': previous['new_checks'],
        'even_norm_sq': str(norm_even_sq),
        'odd_norm_sq': str(norm_odd_sq),
        'polynomial_unit_prime_energy': str(unit_prime),
        'polynomial_unit_log_only_energy': str(unit_log_only),
        'polynomial_unit_parity_correction': str(unit_parity_correction),
        'true_vs_polynomial_parity_correction_budget': str(ratio_budget),
        'true_odd_to_even_norm_ratio_interval_rational': ['76/1000000', '77/1000000'],
        'true_unit_prime_energy_interval_rational': ['-18173952/1000000000', '-18173950/1000000000'],
        'true_unit_parity_energy_correction_interval_rational': ['-44/100000000', '-43/100000000'],
        'true_unit_prime_action_correction_norm_upper': '159/1000000',
        'comparison_to_previous_ground_energy': 'The omitted parity energy has magnitude >7*U, U=560909/10000000000000. This is not a new eigenvalue enclosure.',
        'status': 'Pinned infinite-prolate verifier replay and all new directed interval guards passed.',
        'scope': 'Actual model parity and prime block only. No Gamma/pole cancellation, full Weil Rayleigh value, all-scale ground approximation, RH or Lean kernel verification is claimed.',
        'python': platform.python_version(),
    }

if __name__ == '__main__':
    digits = int(sys.argv[1]) if len(sys.argv) > 1 else 110
    result = run(digits)
    suffix = '' if digits == 110 else f'_{digits}'
    output = ROOT/f'prime3_mellin_parity_certificate{suffix}.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2), flush=True)
