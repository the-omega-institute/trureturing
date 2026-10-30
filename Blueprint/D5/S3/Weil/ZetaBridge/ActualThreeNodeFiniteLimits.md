# Actual three-node FiniteLimits

## Abstract

Actual three-node FiniteLimits

For fixed signed integer n, r=n/N tends to zero. Continuity through the discriminant gives rhoPlus->6h, rhoMinus->0 and O->4a^2 when h>0. The positive limit 6h justifies division by rhoPlus on one eventual set.

The exact determinant identity gives N^2 rhoMinus -> n^2 a^2(g^2+4mu)/(9h). If a!=0, rhoMinus eventually lies below O; sorting yields the first two limits max(6h,4a^2) and min(6h,4a^2), preserving the top tie.

When a=0 and n!=0, N^4 rhoMinus ->16h n^4/135 and N^2 O=4h n^2/3 for N>0. Exact exterior ordering supplies the three sorted limits with powers 0,2,4.

The sequences remain total at N=0. Algebraic cancellations use N>=1 eventually; no sign condition n>0, eigenvector condition, or artificial separation between two vanishing roots is imposed.

**Theorem 1.1 (roots at zero).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.roots_at_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.roots_at_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma roots_at_zero (g mu a : ℝ) (hh : 0 ≤ g ^ 2 + mu) :     rhoPlus g mu a 0 = 6 * (g ^ 2 + mu) ∧ rhoMinus g mu a 0 = 0

**Theorem 1.2 (root limits).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.root_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.root_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma root_limits (g mu a : ℝ) (n : ℤ) (hh : 0 < g ^ 2 + mu) :     Tendsto (fun N : ℕ => rhoPlus g mu a ((n : ℝ) / N)) atTop (𝓝 (6 * (g ^ 2 + mu))) ∧     Tendsto (fun N : ℕ => rhoMinus g mu a ((n : ℝ) / N)) atTop (𝓝 0) ∧     Tendsto (fun N : ℕ => O g mu a ((n : ℝ) / N)) atTop (𝓝 (4 * a ^ 2))

**Definition 1.3 (detReduced).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.detReduced`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.detReduced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def detReduced (g mu a r : ℝ) : ℝ :=   2 * a ^ 2 * (g ^ 2 + 4 * mu) / 3 +   (4 * g * a * (g ^ 2 + mu) / 3) * r +   (2 * a ^ 2 * g ^ 2 - 16 * a ^ 2 * (g ^ 2 + mu) / 9 +     32 * (g ^ 2 + mu) ^ 2 / 45) * r ^ 2 +   (4 * g * a * (g ^ 2 + mu) / 15) * r ^ 3 +   (a ^ 2 * (g ^ 2 + 16 * mu) / 30) * r ^ 4

**Theorem 1.4 (determinant factored).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.determinant_factored`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.determinant_factored` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma determinant_factored (g mu a r : ℝ) :     evenDet g mu a r = r ^ 2 * detReduced g mu a r

**Theorem 1.5 (scaled det two).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_det_two`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_det_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma scaled_det_two (g mu a : ℝ) (n : ℤ) (N : ℕ) (hN : N ≠ 0) :     (N : ℝ) ^ 2 * evenDet g mu a ((n : ℝ) / N) =       (n : ℝ) ^ 2 * detReduced g mu a ((n : ℝ) / N)

**Theorem 1.6 (scaled det four zero).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_det_four_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_det_four_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma scaled_det_four_zero (g mu : ℝ) (n : ℤ) (N : ℕ) (hN : N ≠ 0) :     (N : ℝ) ^ 4 * evenDet g mu 0 ((n : ℝ) / N) =       32 * (g ^ 2 + mu) ^ 2 * (n : ℝ) ^ 4 / 45

**Theorem 1.7 (scaled small root limit).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_small_root_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_small_root_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma scaled_small_root_limit (g mu a : ℝ) (n : ℤ) (hh : 0 < g ^ 2 + mu) :     Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * rhoMinus g mu a ((n : ℝ) / N)) atTop       (𝓝 ((n : ℝ) ^ 2 * a ^ 2 * (g ^ 2 + 4 * mu) / (9 * (g ^ 2 + mu))))

**Theorem 1.8 (scaled small root limit zero).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_small_root_limit_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_small_root_limit_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma scaled_small_root_limit_zero (g mu : ℝ) (n : ℤ) (hh : 0 < g ^ 2 + mu) :     Tendsto (fun N : ℕ => (N : ℝ) ^ 4 * rhoMinus g mu 0 ((n : ℝ) / N)) atTop       (𝓝 (16 * (g ^ 2 + mu) * (n : ℝ) ^ 4 / 135))

**Theorem 1.9 (nonzero eventually sorted).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.nonzero_eventually_sorted`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.nonzero_eventually_sorted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma nonzero_eventually_sorted (g mu a : ℝ) (n : ℤ) (hh : 0 < g ^ 2 + mu) (ha : a ≠ 0) :     ∀ᶠ N : ℕ in atTop,       finiteEigen g mu a ((n : ℝ) / N) =         ![max (rhoPlus g mu a ((n : ℝ) / N)) (O g mu a ((n : ℝ) / N)),           min (rhoPlus g mu a ((n : ℝ) / N)) (O g mu a ((n : ℝ) / N)),           rhoMinus g mu a ((n : ℝ) / N)]

**Theorem 1.10 (finite nonzero limits).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.finite_nonzero_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.finite_nonzero_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem finite_nonzero_limits (g mu a : ℝ) (n : ℤ) (hh : 0 < g ^ 2 + mu) (ha : a ≠ 0) :     Tendsto (fun N : ℕ => finiteEigen g mu a ((n : ℝ) / N) 0) atTop       (𝓝 (max (6 * (g ^ 2 + mu)) (4 * a ^ 2))) ∧     Tendsto (fun N : ℕ => finiteEigen g mu a ((n : ℝ) / N) 1) atTop       (𝓝 (min (6 * (g ^ 2 + mu)) (4 * a ^ 2))) ∧     Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * finiteEigen g mu a ((n : ℝ) / N) 2) atTop       (𝓝 ((n : ℝ) ^ 2 * a ^ 2 * (g ^ 2 + 4 * mu) / (9 * (g ^ 2 + mu))))

**Theorem 1.11 (exterior eventually).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.exterior_eventually`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.exterior_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma exterior_eventually (n : ℤ) :     ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ |(n : ℝ)| < (N : ℝ)

**Theorem 1.12 (zero eventually sorted).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.zero_eventually_sorted`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.zero_eventually_sorted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma zero_eventually_sorted (g mu : ℝ) {n : ℤ} (hn : n ≠ 0) (hh : 0 < g ^ 2 + mu) :     ∀ᶠ N : ℕ in atTop,       finiteEigen g mu 0 ((n : ℝ) / N) =         ![rhoPlus g mu 0 ((n : ℝ) / N), O g mu 0 ((n : ℝ) / N),           rhoMinus g mu 0 ((n : ℝ) / N)]

**Theorem 1.13 (zero scaled odd).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.zero_scaled_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.zero_scaled_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma zero_scaled_odd (g mu : ℝ) (n : ℤ) (N : ℕ) (hN : N ≠ 0) :     (N : ℝ) ^ 2 * O g mu 0 ((n : ℝ) / N) = 4 * (g ^ 2 + mu) * (n : ℝ) ^ 2 / 3

**Theorem 1.14 (finite zero limits).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.finite_zero_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.finite_zero_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem finite_zero_limits (g mu : ℝ) {n : ℤ} (hn : n ≠ 0) (hh : 0 < g ^ 2 + mu) :     Tendsto (fun N : ℕ => finiteEigen g mu 0 ((n : ℝ) / N) 0) atTop       (𝓝 (6 * (g ^ 2 + mu))) ∧     Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * finiteEigen g mu 0 ((n : ℝ) / N) 1) atTop       (𝓝 (4 * (g ^ 2 + mu) * (n : ℝ) ^ 2 / 3)) ∧     Tendsto (fun N : ℕ => (N : ℝ) ^ 4 * finiteEigen g mu 0 ((n : ℝ) / N) 2) atTop       (𝓝 (16 * (g ^ 2 + mu) * (n : ℝ) ^ 4 / 135))

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.detReduced`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.determinant_factored`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.exterior_eventually`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.finite_nonzero_limits`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.finite_zero_limits`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.nonzero_eventually_sorted`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.root_limits`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.roots_at_zero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_det_four_zero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_det_two`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_small_root_limit`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.scaled_small_root_limit_zero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.zero_eventually_sorted`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits.zero_scaled_odd`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum](ActualThreeNodeFiniteSpectrum.md)
