# Polynomial Reciprocal Bounds

## Abstract

Polynomial Reciprocal Bounds

For arbitrary complex polynomials F and G, value(F,t)=F(t), E(F)=integral_[0,1] norm(F(t))^2, and ltwo(F)=sqrt(E(F)). The mixed readout is the real part of F(t)*conj(G(t)); mixedDeriv is its actual derivative. Complex conjugation is retained throughout.

For natural d>=1 and natDegree(F),natDegree(G)<d, the mixed variation is at most 4*d^2*ltwo(F)*ltwo(G). The proof uses integral Cauchy-Schwarz and the existing PolynomialL2Derivative.complex_polynomial_derivative_l2, whose derivative energy bound is d^4*E(F). No coefficient norm conversion or new moment assumption is used.

For positive natural N, define tailEnergy as sum over all j>=0 of norm(F(N/(N+j+1)))^2/(N+j+1)^2. It is summable and abs(N*tailEnergy-E(F))<=4*d^2*E(F)/N.

For every real sequence with signed prefix sums bounded by D>=0, the corresponding mixed reciprocal sum is summable and abs(N*sum)<=4*d^2*D*ltwo(F)*ltwo(G)/N. Zero and near-cancelling polynomials remain in scope; no energy division occurs.

**Definition 1.1 (value).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.value`

*Formalization.* `D5/S3/Analytic/PolynomialReciprocalBounds.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def value (F : ℂ[X]) (t : ℝ) : ℂ := F.eval (t : ℂ).

**Definition 1.2 (energy).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.energy`

*Formalization.* `D5/S3/Analytic/PolynomialReciprocalBounds.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def energy (F : ℂ[X]) : ℝ := ∫ t in (0:ℝ)..1, ‖value F t‖^2.

**Definition 1.3 (ltwo).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.ltwo`

*Formalization.* `D5/S3/Analytic/PolynomialReciprocalBounds.ltwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def ltwo (F : ℂ[X]) : ℝ := Real.sqrt (energy F).

**Definition 1.4 (mixed).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.mixed`

*Formalization.* `D5/S3/Analytic/PolynomialReciprocalBounds.mixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def mixed (F G : ℂ[X]) (t : ℝ) : ℝ := (value F t * conj (value G t)).re.

**Definition 1.5 (mixedDeriv).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.mixedDeriv`

*Formalization.* `D5/S3/Analytic/PolynomialReciprocalBounds.mixedDeriv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def mixedDeriv (F G : ℂ[X]) (t : ℝ) : ℝ := (value F.derivative t * conj (value G t) + value F t * conj (value G.derivative t)).re.

**Theorem 1.6 (value continuous).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.value_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.value_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: @[fun_prop] lemma value_continuous (F : ℂ[X]) : Continuous (value F) := F.continuous.comp Complex.continuous_ofReal lemma energy_nonneg (F : ℂ[X]) : 0 ≤ energy F := intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => sq_nonneg _) lemma ltwo_nonneg (F : ℂ[X]) : 0 ≤ ltwo F := Real.sqrt_nonneg _ lemma ltwo_sq (F : ℂ[X]) : ltwo F ^ 2 = energy F := Real.sq_sqrt (energy_nonneg F) lemma mixed_self (F : ℂ[X]) (t : ℝ) : mixed F F t = ‖value F t‖^2.

**Theorem 1.7 (energy nonneg).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.energy_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.energy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma energy_nonneg (F : ℂ[X]) : 0 ≤ energy F := intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => sq_nonneg _) lemma ltwo_nonneg (F : ℂ[X]) : 0 ≤ ltwo F := Real.sqrt_nonneg _ lemma ltwo_sq (F : ℂ[X]) : ltwo F ^ 2 = energy F := Real.sq_sqrt (energy_nonneg F) lemma mixed_self (F : ℂ[X]) (t : ℝ) : mixed F F t = ‖value F t‖^2.

**Theorem 1.8 (ltwo nonneg).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.ltwo_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.ltwo_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma ltwo_nonneg (F : ℂ[X]) : 0 ≤ ltwo F := Real.sqrt_nonneg _ lemma ltwo_sq (F : ℂ[X]) : ltwo F ^ 2 = energy F := Real.sq_sqrt (energy_nonneg F) lemma mixed_self (F : ℂ[X]) (t : ℝ) : mixed F F t = ‖value F t‖^2.

**Theorem 1.9 (ltwo sq).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.ltwo_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.ltwo_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma ltwo_sq (F : ℂ[X]) : ltwo F ^ 2 = energy F := Real.sq_sqrt (energy_nonneg F) lemma mixed_self (F : ℂ[X]) (t : ℝ) : mixed F F t = ‖value F t‖^2.

**Theorem 1.10 (mixed self).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.mixed_self`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.mixed_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma mixed_self (F : ℂ[X]) (t : ℝ) : mixed F F t = ‖value F t‖^2.

**Theorem 1.11 (mixed continuous).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.mixed_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.mixed_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: @[fun_prop] lemma mixed_continuous (F G : ℂ[X]) : Continuous (mixed F G).

**Theorem 1.12 (mixedDeriv continuous).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.mixedDeriv_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.mixedDeriv_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: @[fun_prop] lemma mixedDeriv_continuous (F G : ℂ[X]) : Continuous (mixedDeriv F G).

**Theorem 1.13 (mixed variation le).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.mixed_variation_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.mixed_variation_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem mixed_variation_le {d : ℕ} (hd : 1 ≤ d) (F G : ℂ[X]) (hF : F.natDegree < d) (hG : G.natDegree < d) : variation (mixed F G) (mixedDeriv F G) ≤ 4*(d:ℝ)^2*(ltwo F*ltwo G).

**Definition 1.14 (tailEnergy).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.tailEnergy`

*Formalization.* `D5/S3/Analytic/PolynomialReciprocalBounds.tailEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def tailEnergy (N : ℕ) (F : ℂ[X]) : ℝ := ∑' j : ℕ, ‖value F ((N:ℝ)/(N+j+1 : ℕ))‖^2 / ((N+j+1 : ℕ):ℝ)^2.

**Theorem 1.15 (square sample summable).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.square_sample_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.square_sample_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma square_sample_summable {N : ℕ} (hN : 0 < N) (F : ℂ[X]) : Summable (fun j : ℕ => ‖value F ((N:ℝ)/(N+j+1 : ℕ))‖^2 / ((N+j+1 : ℕ):ℝ)^2).

**Theorem 1.16 (polynomial quadrature).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.polynomial_quadrature`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.polynomial_quadrature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem polynomial_quadrature {d N : ℕ} (hd : 1 ≤ d) (hN : 0 < N) (F : ℂ[X]) (hF : F.natDegree < d) : |(N:ℝ)*tailEnergy N F-energy F| ≤ 4*(d:ℝ)^2/(N:ℝ)*energy F.

**Theorem 1.17 (polynomial signed weighted).**

Lean statement: `D5/S3/Analytic/PolynomialReciprocalBounds.polynomial_signed_weighted`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReciprocalBounds.polynomial_signed_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem polynomial_signed_weighted {d N : ℕ} (hd : 1 ≤ d) (hN : 0 < N) (F G : ℂ[X]) (hF : F.natDegree < d) (hG : G.natDegree < d) {x : ℕ → ℝ} {D : ℝ} (hD : 0 ≤ D) (hb : ∀ k, |∑ j ∈ Finset.range k, x j| ≤ D) : Summable (fun j : ℕ => x j * weight N (mixed F G) (N+j+1 : ℕ)) ∧ |(N:ℝ)*(∑' j : ℕ, x j * weight N (mixed F G) (N+j+1 : ℕ))| ≤ 4*(d:ℝ)^2*D/(N:ℝ)*(ltwo F*ltwo G).

## References

- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.energy`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.energy_nonneg`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.ltwo`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.ltwo_nonneg`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.ltwo_sq`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.mixed`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.mixedDeriv`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.mixedDeriv_continuous`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.mixed_continuous`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.mixed_self`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.mixed_variation_le`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.polynomial_quadrature`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.polynomial_signed_weighted`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.square_sample_summable`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.tailEnergy`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.value`
- Truth anchor: `D5/S3/Analytic/PolynomialReciprocalBounds.value_continuous`
- Dependency: [D5/S3/Analytic/PolynomialL2Derivative](PolynomialL2Derivative.md)
- Dependency: [D5/S3/Analytic/SignedReciprocalQuadrature](SignedReciprocalQuadrature.md)
