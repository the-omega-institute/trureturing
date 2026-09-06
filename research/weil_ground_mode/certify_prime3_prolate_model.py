"""Certify the genuine zero-mean prolate line against a fixed Weil candidate.

Proposal eigenpairs are untrusted dyadic data. This verifier uses no eigensolver,
quadrature, spheroidal black box, zeta values or fitted spectral gaps. It checks
Sturm counts using two Schur comparisons with the entire Legendre complement,
and residuals including the single infinite-tail coupling. Polynomial arithmetic
Mellin windows are integrated in closed form, including all mixed norm terms.

The identification of the Jacobi operator with the regular prolate realization,
the residual spectral-projection argument and the L2 transport are paper bridges
in RH_RESEARCH_LANE_THEORY.md. This is not an end-to-end Lean certificate.
"""
from __future__ import annotations
import ast
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
from mpmath import iv

if not __debug__:
    raise RuntimeError('Assertions are part of the verifier; do not use -O.')
ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'certify_prime3_refined.py'
BASE_SHA = '8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0'
PROPOSAL = ROOT / 'prime3_prolate_proposal.json'

def rat(x: Fraction | int):
    x = Fraction(x)
    return iv.mpf(x.numerator) / x.denominator

def sq(x):
    return x ** 2

def integral_exp(t, left, right):
    """t is an exact integer/Fraction; endpoint integrals are directed intervals."""
    t = Fraction(t)
    return right - left if t == 0 else (iv.exp(rat(t)*right)-iv.exp(rat(t)*left))/rat(t)

def legendre_coefficients(n: int) -> list[Fraction]:
    # Rodrigues formula, exact rational arithmetic in monomial coordinates.
    from math import factorial
    coeff = [Fraction(0) for _ in range(n+1)]
    for k in range(n//2+1):
        coeff[n-2*k] = Fraction((-1)**k*factorial(2*n-2*k),
            2**n*factorial(k)*factorial(n-k)*factorial(n-2*k))
    return coeff

def run(digits: int = 110) -> dict:
    if digits < 90:
        raise ValueError('At least 90 decimal digits are required for this monomial certificate.')
    iv.dps = digits
    base_bytes = BASE.read_bytes()
    assert hashlib.sha256(base_bytes).hexdigest() == BASE_SHA
    tree = ast.parse(base_bytes)
    assignments = [n for n in tree.body if isinstance(n, ast.Assign)
                   and any(isinstance(t, ast.Name) and t.id == 'CANDIDATE' for t in n.targets)]
    assert len(assignments) == 1
    old = ast.literal_eval(assignments[0].value)
    assert len(old) == 129 and old == tuple(reversed(old))
    data = json.loads(PROPOSAL.read_bytes())
    c, K, bits = data['scale_c'], data['dimension'], data['dyadic_bits']
    assert (c, K, bits) == (3, 32, 250)
    assert [p['even_index'] for p in data['proposals']] == [0, 2]
    pi, lam = iv.pi, iv.sqrt(c)
    a, L = iv.ln(c)/2, iv.ln(c)
    q2 = (2*pi*c)**2
    def alpha(j):
        return rat(j+1)/iv.sqrt((2*j+1)*(2*j+3)) if j >= 0 else rat(0)
    diagonal = [rat(2*r*(2*r+1))+q2*(alpha(2*r)**2+alpha(2*r-1)**2) for r in range(K)]
    off = [q2*alpha(2*r)*alpha(2*r+1) for r in range(K)]
    high_floor = (2*K)*(2*K+1)
    def count(shift, subtract_tail):
        # LDL signs, not approximate eigenvalues. Entire tail is positive here.
        assert bool(shift < high_floor)
        correction = off[-1]**2/(high_floor-shift) if subtract_tail else rat(0)
        pivot = diagonal[0]-shift
        signs = []
        for r in range(K):
            if r:
                pivot = diagonal[r]-shift-off[r-1]**2/pivot
            if r == K-1:
                pivot -= correction
            assert bool(pivot > 0) or bool(pivot < 0), ('uncertain pivot', r, str(pivot))
            signs.append(-1 if bool(pivot < 0) else 1)
        return signs.count(-1)
    vectors, residuals, count_checks = [], [], []
    eps = Fraction(1, 10**25)
    for proposal in data['proposals']:
        nums = list(map(int, proposal['vector_numerators']))
        assert len(nums) == K
        raw = [rat(Fraction(n, 2**bits)) for n in nums]
        exact_norm_sq = sum(Fraction(n*n, 2**(2*bits)) for n in nums)
        assert exact_norm_sq > 0
        norm = iv.sqrt(rat(exact_norm_sq))
        v = [x/norm for x in raw]
        assert bool(v[0] > 0)
        mu = rat(Fraction(int(proposal['center_numerator']), 2**bits))
        j = proposal['even_index']
        counts = [count(mu-1, False), count(mu-1, True),
                  count(mu+1, False), count(mu+1, True)]
        assert counts == [j, j, j+1, j+1]
        residual = []
        for r in range(K):
            value = (diagonal[r]-mu)*v[r]
            if r: value += off[r-1]*v[r-1]
            if r+1 < K: value += off[r]*v[r+1]
            residual.append(value)
        residual_sq = sum((sq(x) for x in residual), rat(0)) + sq(off[-1]*v[-1])
        # Rest of spectrum has distance >=1 from mu; sqrt(2)*r bounds unit-mode error.
        assert bool(2*residual_sq < rat(eps)**2)
        vectors.append(v)
        residuals.append(str(residual_sq))
        count_checks.append({'index': j, 'center': str(mu), 'counts': counts})
    v0, v4 = vectors
    ratio = v4[0]/v0[0]
    # Exact L2 error for the true zero-integral prolate line, in t=x/lambda.
    assert bool(v0[0] > rat(eps))
    dr = rat(eps)*(1+abs(ratio))/(v0[0]-rat(eps))
    combo_error = rat(eps)+(abs(ratio)+dr)*rat(eps)+dr
    # h(x)=sum H_r*sqrt((4r+1)/2)*P_{2r}(x/lambda).
    # The overall nonzero normalization is immaterial for the normalized line.
    H = [v4[r]-ratio*v0[r] for r in range(K)]
    H[0] = rat(0)  # exact from the definition of ratio, not an approximation
    A = [rat(0) for _ in range(K)]
    for j in range(1, K):
        poly = legendre_coefficients(2*j)
        factor = H[j]*iv.sqrt(rat(Fraction(4*j+1, 2)))
        for r in range(j+1):
            A[r] += factor*rat(poly[2*r])/c**r
    # Piecewise evenized Mellin window. m=3 contributes only at one endpoint.
    b = a-iv.ln(2)
    assert bool(-a < b) and bool(b < -b) and bool(-b < a)
    intervals = [(-a, b, (1, 2), (1,)),
                 (b, -b, (1,), (1,)),
                 (-b, a, (1,), (1, 2))]
    model_norm_sq = rat(0)
    for left, right, positive, negative in intervals:
        terms = {}
        for r in range(K):
            t = Fraction(4*r+1, 2)
            terms[t] = 2*A[r]*sum(m**(2*r) for m in positive)
            terms[-t] = 2*A[r]*sum(m**(2*r) for m in negative)
        combined = {}
        for t, ar in terms.items():
            for s, bs in terms.items():
                combined[t+s] = combined.get(t+s, rat(0))+ar*bs
        model_norm_sq += sum((value*integral_exp(exponent, left, right)
                              for exponent, value in combined.items()), rat(0))
    assert bool(model_norm_sq > 0)
    model_norm = iv.sqrt(model_norm_sq)
    def ft(z):
        # Direct finite sum of endpoint integrals, including the half-power Jacobian.
        out = iv.mpc(0)
        for r in range(K):
            t = rat(Fraction(4*r+1, 2)) + iv.j*z
            assert bool(t.real > 0)
            for m in (1, 2):
                right = a-iv.ln(m)
                out += 4*A[r]*m**(2*r)*(iv.exp(t*right)-iv.exp(-t*a))/t
        return out
    # Real cosine coefficients of p^+, exactly the real part of p's Fourier transform.
    cosine = [(1 if n == 0 else iv.sqrt(2))*(-1)**n/iv.sqrt(L)*ft(2*pi*n/L).real
              for n in range(65)]
    old_norm_sq = sum(Fraction(n*n, 2**80) for n in old)
    old_norm = iv.sqrt(rat(old_norm_sq))
    old_even = [rat(Fraction(old[64], 2**40))/old_norm] + [
        iv.sqrt(2)*rat(Fraction(old[64+n], 2**40))/old_norm for n in range(1,65)]
    overlap = sum((cosine[n]*old_even[n] for n in range(65)), rat(0))/model_norm
    assert bool(overlap > 0) or bool(overlap < 0)
    distance_sq = 2-2*abs(overlap)
    assert bool(distance_sq > 0)
    polynomial_distance_bound = Fraction(112, 100000)  # 0.00112
    assert bool(distance_sq < rat(polynomial_distance_bound)**2)
    # Actual arithmetic transport: each summand has L2 norm <=m^-1/2 ||delta h||.
    mellin_error = 4*sum((1/iv.sqrt(m) for m in range(1,c+1)), rat(0))*iv.sqrt(lam)*combo_error
    assert bool(mellin_error < model_norm)
    normalized_model_error = 2*mellin_error/model_norm
    final_bound = Fraction(113, 100000)  # 0.00113
    assert bool(rat(polynomial_distance_bound)+normalized_model_error < rat(final_bound))
    report = {
        'scale': 'lambda=sqrt(3), a=log(3)/2',
        'prolate_operator': '-d/dt((1-t^2)d/dt)+(6*pi)^2*t^2 on [-1,1], even regular realization',
        'dimension': K, 'dyadic_bits': bits, 'interval_decimal_digits': digits,
        'proposal_sha256': hashlib.sha256(PROPOSAL.read_bytes()).hexdigest(),
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'weil_candidate_source_sha256': BASE_SHA,
        'sturm_schur_counts': count_checks,
        'full_residual_squared_intervals': residuals,
        'unit_prolate_mode_error_upper': str(eps),
        'zero_integral_ratio_interval': str(ratio),
        'unnormalized_mellin_model_norm_interval': str(model_norm),
        'polynomial_model_candidate_overlap': str(overlap),
        'polynomial_model_candidate_distance_squared': str(distance_sq),
        'normalized_true_vs_polynomial_model_error': str(normalized_model_error),
        'true_normalized_prolate_model_to_fixed_weil_candidate_bound': str(final_bound),
        'combined_with_existing_ground_certificate': 'Projective true Weil ground to aligned unit true prolate model < 1113/100000, assuming the already-documented full Weil certificate with projective error <1/100.',
        'new_checks': 'All directed interval comparisons passed. No quadrature or eigensolver used by verifier.',
        'scope': 'Fixed-window prolate-model identification with explicit spectral tail and arithmetic Mellin transport; analytic operator/core and spectral projection bridges are paper proofs, not Lean kernel results.',
        'not_established': 'No unbounded-scale Weil/prolate comparison rate, no all-scale simple-even ground theorem, no Xi/RH conclusion.'}
    return report

if __name__ == '__main__':
    digits = int(sys.argv[1]) if len(sys.argv) > 1 else 110
    result = run(digits)
    output = ROOT / ('prime3_prolate_model_certificate.json' if digits == 110 else f'prime3_prolate_model_certificate_{digits}.json')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2), flush=True)
