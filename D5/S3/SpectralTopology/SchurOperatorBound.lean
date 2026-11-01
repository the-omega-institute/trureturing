/- GID: D5/S3/SpectralTopology/SchurOperatorBound
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/SchurOperatorBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.Matrix]
   utility: none
   digest: Finite rectangular Schur bound for the Euclidean operator norm. -/

module
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu

Minimal port of LeanPool/LowWeightPauliDynamics/SchurCore.lean at
https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/LowWeightPauliDynamics/SchurCore.lean
Source SHA256: 7327b00d289548d89d1018bda0d38716152a01f2838837251e3bc419c31f426f.
Modifications: repository namespace, private consumed helpers, omitted unused corollaries.
Apache-2.0 license and the applicable LeanPool NOTICE are retained at
  docs/reports/brooks-suppliers/daviskahan-LICENSE.txt
  docs/reports/brooks-suppliers/daviskahan-NOTICE.txt.
Original project: https://github.com/Jue-Xu/Lean4LPD.
Retirement: replace this port when the pinned Mathlib provides the rectangular
RCLike row/column-sum L2 operator bound, including empty index types.
The current consumer is Apollonian.CutoffSpectralBounds.late_adjacency_norm_le.
-/

@[expose] public section
namespace D5.S3.SpectralTopology.SchurOperatorBound
open Finset Matrix WithLp
open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The continuous linear map on `EuclideanSpace` attached to a (possibly rectangular) matrix.
This is the map whose operator norm *is* `‖A‖` for the scoped ℓ² operator norm, by
`Matrix.l2_opNorm_def`; for square matrices it agrees with `Matrix.toEuclideanCLM`. -/
private noncomputable abbrev clm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m :=
  (Matrix.toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans LinearMap.toContinuousLinearMap A

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
/-- Weighted Cauchy–Schwarz for one row: if row `i` of `A` has absolute sum at most `R`, then
`‖(A *ᵥ y) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2`. This is the row step of the Schur test used
in `apd:thm:layer_inflow`. Zero entries and empty sums need no separate case. -/
private theorem schur_row_sq_le (A : Matrix ι κ 𝕜) (y : κ → 𝕜) (i : ι) (R : ℝ)
    (hrow : ∑ j, ‖A i j‖ ≤ R) :
    ‖(A *ᵥ y) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2 := by
  have habs : ‖(A *ᵥ y) i‖ ≤ ∑ j, ‖A i j‖ * ‖y j‖ := by
    simpa only [Matrix.mulVec, dotProduct, norm_mul] using
      (norm_sum_le univ (fun j => A i j * y j))
  have hcs : (∑ j, ‖A i j‖ * ‖y j‖) ^ 2 ≤
      (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul univ
      (f := fun j => ‖A i j‖) (g := fun j => ‖A i j‖ * ‖y j‖ ^ 2)
    · intro j _; exact norm_nonneg _
    · intro j _; positivity
    · intro j _; exact le_of_eq (by ring)
  exact ((pow_le_pow_left₀ (norm_nonneg _) habs 2).trans hcs).trans
    (mul_le_mul_of_nonneg_right hrow (Finset.sum_nonneg fun j _ => by positivity))

/-- Squared form of the finite Schur test used in `apd:thm:layer_inflow`: if every row of `A`
has absolute sum at most `R` and every column at most `C`, then
`∑ i, ‖(A *ᵥ y) i‖ ^ 2 ≤ R * C * ∑ j, ‖y j‖ ^ 2`. -/
private theorem schur_mulVec_sq_le (A : Matrix ι κ 𝕜) (y : κ → 𝕜) {R C : ℝ}
    (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    (∑ i, ‖(A *ᵥ y) i‖ ^ 2) ≤ R * C * ∑ j, ‖y j‖ ^ 2 := by
  have h1 : (∑ i, ‖(A *ᵥ y) i‖ ^ 2) ≤
      ∑ i, R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => schur_row_sq_le A y i R (hrow i)
  have h2 : (∑ i, R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2) =
      R * ∑ j, (∑ i, ‖A i j‖) * ‖y j‖ ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
  calc (∑ i, ‖(A *ᵥ y) i‖ ^ 2)
      ≤ R * ∑ j, (∑ i, ‖A i j‖) * ‖y j‖ ^ 2 := h1.trans_eq h2
    _ ≤ R * ∑ j, C * ‖y j‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)) hR
    _ = R * C * ∑ j, ‖y j‖ ^ 2 := by rw [← Finset.mul_sum, mul_assoc]

variable [DecidableEq κ]

/-- The Schur test as a bound on the action of `clm A`, the continuous linear map of Euclidean
spaces attached to `A` in `BlockNorm`: `‖clm A y‖ ≤ √(R * C) * ‖y‖` (`apd:thm:layer_inflow`). -/
private theorem schur_clm_le (A : Matrix ι κ 𝕜) (y : EuclideanSpace 𝕜 κ) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖clm A y‖ ≤ Real.sqrt (R * C) * ‖y‖ := by
  have hsq : ‖clm A y‖ ^ 2 ≤ (Real.sqrt (R * C) * ‖y‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hR hC)]
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact schur_mulVec_sq_le A y.ofLp hR hrow hcol
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))] at h

/-- **The finite Schur test**, in the form used by `apd:thm:layer_inflow`: row sums at most `R`
and column sums at most `C` give `‖A‖ ≤ √(R * C)`. Here `‖A‖` is the scoped **ℓ² operator norm**
(`Matrix.Norms.L2Operator`), not an entrywise matrix norm. -/
theorem l2_opNorm_le_schur (A : Matrix ι κ 𝕜) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) : ‖A‖ ≤ Real.sqrt (R * C) := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (fun y => schur_clm_le A y hR hC hrow hcol)


end D5.S3.SpectralTopology.SchurOperatorBound
