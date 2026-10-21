# Actual three-node Full336

## Abstract

Actual three-node Full336

K_N is defined to be Matrix.gram Complex (sourceTailFamily hc N n) from the literal source family. It includes every j>=0 and both exterior signs. Its quadratic form is given by actual_source_gram_tsum.

Let delta=9*336*c^2*(1+log(c))^3, l_N=1-delta/N and u_N=(1+delta/N)/(1-(n/N)^2)^2. For c>=3, signed n!=0, N>=9 and |n|<N, the complete actual paired symbol bounds and exact denominator comparison yield l_N H_N <= pi^2 N K_N <= u_N H_N.

The vector form is proved for every complex x, including zero and cancellation, before the Loewner forms. Complete-tail summability holds by actual_tail_summable_all. No vector mass or finite energy is divided out.

The matrices in the two differences are Hermitian by the physical finite-matrix witness and the canonical Gram witness. Their nonnegative quadratic forms give positive semidefiniteness of the two actual differences.

**Definition 1.1 (delta336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.delta336`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.delta336` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def delta336 (c : ℕ) : ℝ := 9 * 336 * (c : ℝ) ^ 2 * (1 + Real.log (c : ℝ)) ^ 3

**Definition 1.2 (lower336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.lower336`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.lower336` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def lower336 (c N : ℕ) : ℝ := 1 - delta336 c / N

**Definition 1.3 (upper336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.upper336`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.upper336` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def upper336 (c N : ℕ) (n : ℤ) : ℝ :=   (1 + delta336 c / N) / (1 - ((n : ℝ) / N) ^ 2) ^ 2

**Definition 1.4 (actualTailGram).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actualTailGram`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actualTailGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def actualTailGram {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=   Matrix.gram ℂ (sourceTailFamily hc N n)

**Theorem 1.5 (actual full336 all vector).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_all_vector`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_all_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_full336_all_vector {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)     (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ)) :     ∀ x : Fin 3 → ℂ,       lower336 c N * finiteForm (Real.pi / 4) (mean c)           (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x ≤         Real.pi ^ 2 * N * (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re ∧       Real.pi ^ 2 * N * (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re ≤         upper336 c N n * finiteForm (Real.pi / 4) (mean c)           (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x

**Theorem 1.6 (actual full336 loewner).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_loewner`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_loewner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_full336_loewner {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)     (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ)) :     let H := finiteMatrix (Real.pi / 4) (mean c)       (arithmeticBoundarySymbol c n) ((n : ℝ) / N)     let K := actualTailGram hc n N     ((((Real.pi ^ 2 * N : ℝ) : ℂ) • K) - ((lower336 c N : ℂ) • H)).PosSemidef ∧       (((upper336 c N n : ℂ) • H) - (((Real.pi ^ 2 * N : ℝ) : ℂ) • K)).PosSemidef

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actualTailGram`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_all_vector`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_loewner`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.delta336`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.lower336`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.upper336`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge](ActualThreeNodeSourceHeadBridge.md)
