# Signed Reciprocal Quadrature

## Abstract

Signed Reciprocal Quadrature

The natural tail is indexed by m=N+j+1 for every natural j, so the entire infinite tail m>N is present. For real N>0 put w(x)=h(N/x)/x^2. Its derivative is -2*h(N/x)/x^3-N*h'(N/x)/x^4, and V(h,h') is the integral on [0,1] of 2*t*abs(h(t))+t^2*abs(h'(t)).

Continuous h and h' with HasDerivAt h (h'(t)) t for every t in [0,1] suffice. No derivative of abs(h) and no monotonicity of h is assumed. Reciprocal substitution gives the integral of w on (N,infinity) as the integral of h on [0,1] divided by N. The integral of abs(w') is at most V/N^2.

For positive natural N, the samples w(N+j+1) are absolutely summable. The absolute difference of their sum from integral(h)/N is at most V/N^2. The proof compares each right endpoint with its cell integral and passes to the improper integral.

If a real sequence x has every signed prefix sum bounded in absolute value by a nonnegative D, then sum_j x(j)*w(N+j+1) is absolutely summable and its absolute value is at most D*V/N^2. Finite Abel summation keeps the signed prefix bound; its boundary vanishes at infinity. This is not a bound obtained by replacing each x(j) with its absolute value.

**Definition 1.1 (weight).**

Lean statement: `D5/S3/Analytic/SignedReciprocalQuadrature.weight`

*Formalization.* `D5/S3/Analytic/SignedReciprocalQuadrature.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def weight (N : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ := h (N / x) / x ^ 2.

**Definition 1.2 (weightDeriv).**

Lean statement: `D5/S3/Analytic/SignedReciprocalQuadrature.weightDeriv`

*Formalization.* `D5/S3/Analytic/SignedReciprocalQuadrature.weightDeriv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def weightDeriv (N : ℝ) (h h' : ℝ → ℝ) (x : ℝ) : ℝ := -(2 * h (N / x) / x ^ 3) - N * h' (N / x) / x ^ 4.

**Definition 1.3 (variationDensity).**

Lean statement: `D5/S3/Analytic/SignedReciprocalQuadrature.variationDensity`

*Formalization.* `D5/S3/Analytic/SignedReciprocalQuadrature.variationDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def variationDensity (h h' : ℝ → ℝ) (t : ℝ) : ℝ := 2 * t * |h t| + t ^ 2 * |h' t|.

**Definition 1.4 (variation).**

Lean statement: `D5/S3/Analytic/SignedReciprocalQuadrature.variation`

*Formalization.* `D5/S3/Analytic/SignedReciprocalQuadrature.variation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def variation (h h' : ℝ → ℝ) : ℝ := ∫ t in (0 : ℝ)..1, variationDensity h h' t.

**Theorem 1.5 (derivative integral bound).**

Lean statement: `D5/S3/Analytic/SignedReciprocalQuadrature.derivative_integral_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SignedReciprocalQuadrature.derivative_integral_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem derivative_integral_bound {N : ℝ} (hN : 0 < N) {h h' : ℝ → ℝ} (hh : Continuous h) (hh' : Continuous h') : IntegrableOn (weightDeriv N h h') (Ioi N) ∧ (∫ x in Ioi N, |weightDeriv N h h' x|) ≤ variation h h' / N ^ 2.

**Theorem 1.6 (sample summable).**

Lean statement: `D5/S3/Analytic/SignedReciprocalQuadrature.sample_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SignedReciprocalQuadrature.sample_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma sample_summable {N : ℕ} (hN : 0 < N) {h : ℝ → ℝ} (hh : Continuous h) : Summable (fun j : ℕ => weight N h (N + j + 1 : ℕ)).

**Theorem 1.7 (right endpoint quadrature).**

Lean statement: `D5/S3/Analytic/SignedReciprocalQuadrature.right_endpoint_quadrature`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SignedReciprocalQuadrature.right_endpoint_quadrature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem right_endpoint_quadrature {N : ℕ} (hN : 0 < N) {h h' : ℝ → ℝ} (hh : Continuous h) (hh' : Continuous h') (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt h (h' t) t) : Summable (fun j : ℕ => weight N h (N+j+1 : ℕ)) ∧ |(∑' j : ℕ, weight N h (N+j+1 : ℕ)) - (∫ t in (0 : ℝ)..1, h t) / N| ≤ variation h h' / (N : ℝ)^2.

**Theorem 1.8 (signed weighted reciprocal).**

Lean statement: `D5/S3/Analytic/SignedReciprocalQuadrature.signed_weighted_reciprocal`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SignedReciprocalQuadrature.signed_weighted_reciprocal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem signed_weighted_reciprocal {N : ℕ} (hN : 0 < N) {h h' : ℝ → ℝ} (hh : Continuous h) (hh' : Continuous h') (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt h (h' t) t) {x : ℕ → ℝ} {D : ℝ} (hD : 0 ≤ D) (hb : ∀ k, |∑ j ∈ Finset.range k, x j| ≤ D) : Summable (fun j : ℕ => x j * weight N h (N+j+1 : ℕ)) ∧ |∑' j : ℕ, x j * weight N h (N+j+1 : ℕ)| ≤ D * variation h h' / (N:ℝ)^2.

## References

- Truth anchor: `D5/S3/Analytic/SignedReciprocalQuadrature.derivative_integral_bound`
- Truth anchor: `D5/S3/Analytic/SignedReciprocalQuadrature.right_endpoint_quadrature`
- Truth anchor: `D5/S3/Analytic/SignedReciprocalQuadrature.sample_summable`
- Truth anchor: `D5/S3/Analytic/SignedReciprocalQuadrature.signed_weighted_reciprocal`
- Truth anchor: `D5/S3/Analytic/SignedReciprocalQuadrature.variation`
- Truth anchor: `D5/S3/Analytic/SignedReciprocalQuadrature.variationDensity`
- Truth anchor: `D5/S3/Analytic/SignedReciprocalQuadrature.weight`
- Truth anchor: `D5/S3/Analytic/SignedReciprocalQuadrature.weightDeriv`
