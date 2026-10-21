# Actual three-node FiniteEnergy

## Abstract

Actual three-node FiniteEnergy

The signed integer nodes are the sealed owner's literal set {-n,0,n}; n is any nonzero integer. The same owner supplies the normalized source heads and sourceHead. No new Hilbert-space bridge, summability theorem or positivity definition is introduced here.

Nodal expansion derives D=X(X^2-n^2), Q=(v(-n)+v(0)+v(n))X^2+n(v(n)-v(-n))X-n^2 v(0), and P=a(v(n)-v(-n))X^2+an(v(n)+v(-n))X from the actual arithmetic symbol and its oddness.

For raw coordinates v=p(1,1,1)+q(-1,0,1)+s(1,-2,1), reciprocal evaluation gives A(t)=2aq+2ar(p+s)t and B(t)=3p+2rq t+r^2(-p+2s)t^2. Both exterior signs are kept before integration. All p,q,s are complex and may vanish or cancel.

The paired energy integral is U|p|^2+2O|q|^2+C|s|^2+2T Re(conj(p)s). Substituting p=x(0)/sqrt(3), q=x(1)/sqrt(2), s=x(2)/sqrt(6) gives the Hermitian matrix [[U/3,0,T/sqrt(18)],[0,O,0],[T/sqrt(18),0,C/6]].

The sealed sourceHead_original_norm theorem identifies the original retained coefficient mass with the Euclidean mass of x. The realized matrix therefore uses that original metric; it is derived from actual P,Q and pairedEnergy, rather than selected as an unrelated Hermitian matrix.

**Theorem 1.1 (nodes distinct).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodes_distinct`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodes_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma nodes_distinct {n : ℤ} (hn : n ≠ 0) :     -n ≠ 0 ∧ -n ≠ n ∧ (0 : ℤ) ≠ n

**Theorem 1.2 (threeNodes card).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_card`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma threeNodes_card {n : ℤ} (hn : n ≠ 0) : (threeNodes n).card = 3

**Theorem 1.3 (actual symbol zero).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_symbol_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_symbol_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_symbol_zero (c : ℕ) : arithmeticBoundarySymbol c 0 = 0

**Theorem 1.4 (actual three nodal).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_three_nodal`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_three_nodal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_three_nodal {n : ℤ} (hn : n ≠ 0) (c : ℕ) (v : ℤ → ℂ) :     D (threeNodes n) = X * (X ^ 2 - C ((n : ℂ) ^ 2)) ∧     Q (threeNodes n) v =       C (v (-n) + v 0 + v n) * X ^ 2 +         C ((n : ℂ) * (v n - v (-n))) * X - C ((n : ℂ) ^ 2 * v 0) ∧     P c (threeNodes n) v =       C ((arithmeticBoundarySymbol c n : ℂ) * (v n - v (-n))) * X ^ 2 +         C ((arithmeticBoundarySymbol c n : ℂ) * (n : ℂ) * (v n + v (-n))) * X

**Definition 1.5 (rawHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def rawHead (n : ℤ) (p q s : ℂ) : ℤ → ℂ :=   p • (singletonHead (-n) + singletonHead 0 + singletonHead n) +   q • (-singletonHead (-n) + singletonHead n) +   s • (singletonHead (-n) - 2 • singletonHead 0 + singletonHead n)

**Theorem 1.6 (rawHead nodes).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead_nodes`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead_nodes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma rawHead_nodes {n : ℤ} (hn : n ≠ 0) (p q s : ℂ) :     rawHead n p q s (-n) = p - q + s ∧     rawHead n p q s 0 = p - 2 * s ∧     rawHead n p q s n = p + q + s

**Theorem 1.7 (sourceHead eq rawHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_eq_rawHead`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_eq_rawHead` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma sourceHead_eq_rawHead (n : ℤ) (x : Fin 3 → ℂ) :     sourceHead n x = rawHead n (x 0 / (Real.sqrt 3 : ℂ))       (x 1 / (Real.sqrt 2 : ℂ)) (x 2 / (Real.sqrt 6 : ℂ))

**Definition 1.8 (rawA).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawA`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def rawA (a r : ℝ) (p q s : ℂ) : ℂ[X] :=   C (2 * (a : ℂ) * q) + C (2 * (a : ℂ) * (r : ℂ) * (p + s)) * X

**Definition 1.9 (rawB).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawB`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def rawB (r : ℝ) (p q s : ℂ) : ℂ[X] :=   C (3 * p) + C (2 * (r : ℂ) * q) * X +     C ((r : ℂ) ^ 2 * (-p + 2 * s)) * X ^ 2

**Theorem 1.10 (reciprocal three).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.reciprocal_three`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.reciprocal_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma reciprocal_three (N : ℕ) (b0 b1 b2 : ℂ) :     reciprocalPolynomial 3 N (C b0 + C b1 * X + C b2 * X ^ 2) =       C b2 + C (b1 / (N : ℂ)) * X + C (b0 / (N : ℂ) ^ 2) * X ^ 2

**Theorem 1.11 (actual raw reciprocals).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_raw_reciprocals`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_raw_reciprocals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_raw_reciprocals {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)     (p q s : ℂ) :     reciprocalPolynomial 3 N (P c (threeNodes n) (rawHead n p q s)) =       rawA (arithmeticBoundarySymbol c n) ((n : ℝ) / N) p q s ∧     reciprocalPolynomial 3 N (Q (threeNodes n) (rawHead n p q s)) =       rawB ((n : ℝ) / N) p q s

**Definition 1.12 (mixed).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def mixed (p s : ℂ) : ℝ := (conj p * s).re

**Definition 1.13 (rawIntegrand).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def rawIntegrand (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) : ℝ :=   ‖value (rawA a r p q s) t + (g : ℂ) * value (rawB r p q s) t‖ ^ 2 +   ‖value (rawA a r p q s) (-t) - (g : ℂ) * value (rawB r p q s) (-t)‖ ^ 2 +   mu * (‖value (rawB r p q s) t‖ ^ 2 + ‖value (rawB r p q s) (-t)‖ ^ 2)

**Definition 1.14 (quarticCoeffs).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.quarticCoeffs`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.quarticCoeffs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def quarticCoeffs (g mu a r : ℝ) (p q s : ℂ) : Fin 5 → ℝ :=   ![18 * (g ^ 2 + mu) * ‖p‖ ^ 2 + 8 * a ^ 2 * ‖q‖ ^ 2,     24 * g * a * r * (‖p‖ ^ 2 + mixed p s) + 16 * a * g * r * ‖q‖ ^ 2,     (8 * a ^ 2 - 12 * (g ^ 2 + mu)) * r ^ 2 * ‖p‖ ^ 2 +       8 * (g ^ 2 + mu) * r ^ 2 * ‖q‖ ^ 2 + 8 * a ^ 2 * r ^ 2 * ‖s‖ ^ 2 +       (16 * a ^ 2 + 24 * (g ^ 2 + mu)) * r ^ 2 * mixed p s,     8 * a * g * r ^ 3 * (-‖p‖ ^ 2 + 2 * ‖s‖ ^ 2 + mixed p s),     2 * (g ^ 2 + mu) * r ^ 4 * (‖p‖ ^ 2 + 4 * ‖s‖ ^ 2 - 4 * mixed p s)]

**Theorem 1.15 (rawIntegrand parity pair).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_parity_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_parity_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma rawIntegrand_parity_pair (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) :     rawIntegrand g mu a r p q s t =       2 * ‖value (rawA a r p 0 s) t + (g : ℂ) * value (rawB r p 0 s) t‖ ^ 2 +       2 * ‖value (rawA a r 0 q 0) t + (g : ℂ) * value (rawB r 0 q 0) t‖ ^ 2 +       2 * mu * (‖value (rawB r p 0 s) t‖ ^ 2 + ‖value (rawB r 0 q 0) t‖ ^ 2)

**Theorem 1.16 (rawIntegrand quartic).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_quartic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_quartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma rawIntegrand_quartic (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) :     rawIntegrand g mu a r p q s t =       ∑ i : Fin 5, quarticCoeffs g mu a r p q s i * t ^ (i : ℕ)

**Theorem 1.17 (integral fin5 monomials).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.integral_fin5_monomials`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.integral_fin5_monomials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma integral_fin5_monomials (b : Fin 5 → ℝ) :     (∫ t in (0 : ℝ)..1, ∑ i : Fin 5, b i * t ^ (i : ℕ)) =       ∑ i : Fin 5, b i / (((i : ℕ) : ℝ) + 1)

**Theorem 1.18 (raw pairedEnergy).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.raw_pairedEnergy`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.raw_pairedEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma raw_pairedEnergy (c : ℕ) (a r : ℝ) (p q s : ℂ) :     pairedEnergy c (rawA a r p q s) (rawB r p q s) =       U₃ (Real.pi / 4) (mean c) a r * ‖p‖ ^ 2 +       2 * O₃ (Real.pi / 4) (mean c) a r * ‖q‖ ^ 2 +       C₃ (Real.pi / 4) (mean c) a r * ‖s‖ ^ 2 +       2 * T₃ (Real.pi / 4) (mean c) a r * mixed p s

**Theorem 1.19 (mixed div real).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed_div_real`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed_div_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma mixed_div_real (p s : ℂ) (u v : ℝ) :     mixed (p / (u : ℂ)) (s / (v : ℂ)) = mixed p s / (u * v)

**Theorem 1.20 (norm div sqrt sq).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.norm_div_sqrt_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.norm_div_sqrt_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma norm_div_sqrt_sq (p : ℂ) {d : ℝ} (hd : 0 ≤ d) :     ‖p / (Real.sqrt d : ℂ)‖ ^ 2 = ‖p‖ ^ 2 / d

**Definition 1.21 (finiteForm).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteForm`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def finiteForm (g mu a r : ℝ) (x : Fin 3 → ℂ) : ℝ :=   U₃ g mu a r / 3 * ‖x 0‖ ^ 2 + O₃ g mu a r * ‖x 1‖ ^ 2 +     C₃ g mu a r / 6 * ‖x 2‖ ^ 2 +     2 * (T₃ g mu a r / Real.sqrt 18) * mixed (x 0) (x 2)

**Definition 1.22 (finiteMatrix).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def finiteMatrix (g mu a r : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=   !![((U₃ g mu a r / 3 : ℝ) : ℂ), 0, ((T₃ g mu a r / Real.sqrt 18 : ℝ) : ℂ);       0, (O₃ g mu a r : ℂ), 0;       ((T₃ g mu a r / Real.sqrt 18 : ℝ) : ℂ), 0, ((C₃ g mu a r / 6 : ℝ) : ℂ)]

**Theorem 1.23 (finiteMatrix form).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_form`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma finiteMatrix_form (g mu a r : ℝ) (x : Fin 3 → ℂ) :     star x ⬝ᵥ (finiteMatrix g mu a r *ᵥ x) = (finiteForm g mu a r x : ℂ)

**Theorem 1.24 (finiteMatrix isHermitian).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma finiteMatrix_isHermitian (g mu a r : ℝ) :     (finiteMatrix g mu a r).IsHermitian

**Theorem 1.25 (actual finite energy form).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_energy_form`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_energy_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_finite_energy_form {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)     (x : Fin 3 → ℂ) :     pairedEnergy c         (reciprocalPolynomial 3 N (P c (threeNodes n) (sourceHead n x)))         (reciprocalPolynomial 3 N (Q (threeNodes n) (sourceHead n x))) =       finiteForm (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x

**Theorem 1.26 (actual finite matrix realization).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_matrix_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_matrix_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_finite_matrix_realization {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)     (x : Fin 3 → ℂ) :     star x ⬝ᵥ (finiteMatrix (Real.pi / 4) (mean c)         (arithmeticBoundarySymbol c n) ((n : ℝ) / N) *ᵥ x) =       (pairedEnergy c         (reciprocalPolynomial 3 N (P c (threeNodes n) (sourceHead n x)))         (reciprocalPolynomial 3 N (Q (threeNodes n) (sourceHead n x))) : ℂ)

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_energy_form`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_matrix_realization`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_raw_reciprocals`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_symbol_zero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_three_nodal`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteForm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_form`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_isHermitian`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.integral_fin5_monomials`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed_div_real`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodes_distinct`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.norm_div_sqrt_sq`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.quarticCoeffs`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawA`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawB`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead_nodes`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_parity_pair`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_quartic`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.raw_pairedEnergy`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.reciprocal_three`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_eq_rawHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_card`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge](ActualThreeNodeSourceHeadBridge.md)
