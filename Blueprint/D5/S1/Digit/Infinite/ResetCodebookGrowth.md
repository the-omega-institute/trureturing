# Reset codebook: Growth

## Abstract

Reset codebooks, actual sources and weighted lower-memory graphs.

**Theorem 1.1 (radius smul).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookGrowth.radius_smul`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookGrowth.radius_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (A : Matrix ι ι ℝ) (c : ℝ) (hc : 0 ≤ c) : radius (c • A) = c * radius A

**Theorem 1.2 (row lower radius).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookGrowth.row_lower_radius`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookGrowth.row_lower_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a finite nonempty nonnegative matrix has every row sum at least a nonnegative real r, its spectral radius is at least r. The same lower bound propagates to row sums of all powers before taking the Gelfand limit.

**Theorem 1.3 (radius sq).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookGrowth.radius_sq`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookGrowth.radius_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (A : Matrix ι ι ℝ) : radius (A^2) = radius A ^ 2

**Theorem 1.4 (small powers).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookGrowth.small_powers`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookGrowth.small_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (n : ℕ) : 0 ≤ g^n ∧ g^n ≤ (1/4:ℝ)^n

**Theorem 1.5 (auto positive).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookGrowth.auto_positive`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookGrowth.auto_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: 0 < lambda-rho

**Theorem 1.6 (U cost).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookGrowth.U_cost`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookGrowth.U_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1/4) : wordCost U sixColor (coord false D) ≤ max (lambda-g^2*D) (lambda-rho)

**Theorem 1.7 (V cost).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookGrowth.V_cost`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookGrowth.V_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1/4) : wordCost V sixColor (coord true D) ≤ max (lambda-g^2*D) (lambda-rho)

**Theorem 1.8 (C cost).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookGrowth.C_cost`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookGrowth.C_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (z : ℝ) (hz : |z-c0| ≤ 1/4) : wordCost C twentyColor z ≤ lambda-rho

## References

- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookGrowth.C_cost`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookGrowth.U_cost`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookGrowth.V_cost`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookGrowth.auto_positive`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookGrowth.radius_smul`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookGrowth.radius_sq`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookGrowth.row_lower_radius`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookGrowth.small_powers`
- Dependency: [D5/S1/Digit/Infinite/ResetCodebookOrder](ResetCodebookOrder.md)
