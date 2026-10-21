# Actual three-node SymmetricDenominator

## Abstract

Actual three-node SymmetricDenominator

For either nonzero signed exterior node m, the actual nodal model and exact reciprocal evaluation give pi^2(1-(n/m)^2)^2 times the column norm square equal to the corresponding reciprocal numerator norm square divided by m^2.

The negative exterior node is proved to lie outside the literal head using the same radius |n|. After taking norm squares the positive and negative columns share a denominator, and their sum is precisely pairedTerm.

When N>0, |n|<N and m>N, the squared factors satisfy 0<(1-(n/N)^2)^2 <= (1-(n/m)^2)^2 <=1. These bounds depend on the nodes and cutoff, before any coefficient vector.

**Theorem 1.1 (actual single symmetric denominator).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_single_symmetric_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_single_symmetric_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_single_symmetric_denominator {n : ℤ} (hn : n ≠ 0) (c N : ℕ)     (hN : 0 < N) (v : ℤ → ℂ) (m : ℤ) (hm : m ≠ 0) (hmS : m ∉ threeNodes n) :     Real.pi ^ 2 * (1 - ((n : ℝ) / (m : ℝ)) ^ 2) ^ 2 *         ‖couplingColumn c (threeNodes n) v m‖ ^ 2 =       ‖value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -           (arithmeticBoundarySymbol c m : ℂ) *             value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)‖ ^ 2 /         (m : ℝ) ^ 2

**Theorem 1.2 (threeNodes radius).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma threeNodes_radius (n : ℤ) :     ∀ k ∈ threeNodes n, |(k : ℝ)| ≤ |(n : ℝ)|

**Theorem 1.3 (actual pair symmetric denominator).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_pair_symmetric_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_pair_symmetric_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_pair_symmetric_denominator {n : ℤ} (hn : n ≠ 0) (c N : ℕ)     (hN : 0 < N) (hR : |(n : ℝ)| < (N : ℝ)) (v : ℤ → ℂ) (j : ℕ) :     Real.pi ^ 2 * (1 - ((n : ℝ) / (N + j + 1 : ℕ)) ^ 2) ^ 2 *         pairedColumnTerm c N (threeNodes n) v j =       pairedTerm c N         (reciprocalPolynomial 3 N (P c (threeNodes n) v))         (reciprocalPolynomial 3 N (Q (threeNodes n) v)) j

**Theorem 1.4 (symmetric factor bounds).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.symmetric_factor_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.symmetric_factor_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma symmetric_factor_bounds {b N m : ℝ} (hN : 0 < N) (hR : |b| < N) (hNm : N < m) :     0 < (1 - (b / N) ^ 2) ^ 2 ∧       (1 - (b / N) ^ 2) ^ 2 ≤ (1 - (b / m) ^ 2) ^ 2 ∧       (1 - (b / m) ^ 2) ^ 2 ≤ 1

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_pair_symmetric_denominator`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_single_symmetric_denominator`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.symmetric_factor_bounds`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_radius`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge](ActualThreeNodeSourceHeadBridge.md)
