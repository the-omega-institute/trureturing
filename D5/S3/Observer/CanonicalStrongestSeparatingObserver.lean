/- GID: D5/S3/Observer/CanonicalStrongestSeparatingObserver
   generality: G
   mirror-B: D5/B/S3/Observer/CanonicalStrongestSeparatingObserver
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The normalized orthogonal residual is the canonical strongest separating observer. -/

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/- Library-search audit trail (2026-09-02):
   * Six-way repository, receipt, digest, generalized-body, and in-flight branch searches found
     no existing theorem identifying every maximizer of the residual readout problem.
   * The nearby closed-convex distance-witness theorem is Banach-space general but does not give
     Hilbert representatives or equality cases.
   * Pinned Mathlib's `Submodule.inner_starProjection_left_eq_right`,
     `abs_real_inner_le_norm`, and `eq_of_norm_le_re_inner_eq_norm_sq` are applied directly.
   * The source's claimed uniqueness under an absolute-value objective is false: both signs of
     the normalized residual maximize it.  The theorem below states exactly those two maximizers
     and proves uniqueness after imposing positive alignment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.CanonicalStrongestSeparatingObserver

open Set

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The component of `x` invisible to the closed observation subspace `M`. -/
def residual (M : ClosedSubmodule ℝ H) (x : H) : H :=
  x - M.starProjection x

/-- The canonical unit observer in the residual direction.  Its intended use requires a
nonzero residual, which is explicit in the main theorem. -/
def normalizedResidual (M : ClosedSubmodule ℝ H) (x : H) : H :=
  ‖residual M x‖⁻¹ • residual M x

/-- Absolute readout values achieved by unit-ball observers orthogonal to `M`. -/
def separatingReadoutValues (M : ClosedSubmodule ℝ H) (x : H) : Set ℝ :=
  {value | ∃ g : H, g ∈ Mᗮ ∧ ‖g‖ ≤ 1 ∧ value = abs (inner ℝ g x)}

/-- For a nonzero orthogonal residual `r`, the optimal absolute readout is `‖r‖`.  Its complete
set of maximizers is `{r / ‖r‖, -r / ‖r‖}`; the positively aligned maximizer is uniquely
`r / ‖r‖`. -/
theorem canonical_strongest_separating_observer
    (M : ClosedSubmodule ℝ H) (x : H)
    (residualNeZero : residual M x ≠ 0) :
    sSup (separatingReadoutValues M x) = ‖residual M x‖ ∧
      IsGreatest (separatingReadoutValues M x) ‖residual M x‖ ∧
      (∀ g : H, g ∈ Mᗮ → ‖g‖ ≤ 1 →
        (abs (inner ℝ g x) = ‖residual M x‖ ↔
          g = normalizedResidual M x ∨ g = -normalizedResidual M x)) ∧
      (∀ g : H, g ∈ Mᗮ → ‖g‖ ≤ 1 →
        inner ℝ g x = ‖residual M x‖ → g = normalizedResidual M x) := by
  let r : H := residual M x
  let rhat : H := normalizedResidual M x
  change sSup (separatingReadoutValues M x) = ‖r‖ ∧
    IsGreatest (separatingReadoutValues M x) ‖r‖ ∧
    (∀ g : H, g ∈ Mᗮ → ‖g‖ ≤ 1 →
      (abs (inner ℝ g x) = ‖r‖ ↔ g = rhat ∨ g = -rhat)) ∧
    (∀ g : H, g ∈ Mᗮ → ‖g‖ ≤ 1 →
      inner ℝ g x = ‖r‖ → g = rhat)
  have rNeZero : r ≠ 0 := by simpa [r] using residualNeZero
  have rNormPos : 0 < ‖r‖ := norm_pos_iff.mpr rNeZero
  have rhatEq : rhat = ‖r‖⁻¹ • r := by
    simp [rhat, normalizedResidual, r]
  have rhatNorm : ‖rhat‖ = 1 := by
    rw [rhatEq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr rNormPos)]
    exact inv_mul_cancel₀ rNormPos.ne'
  have rMem : r ∈ Mᗮ := by
    exact Submodule.sub_starProjection_mem_orthogonal _
  have rhatMem : rhat ∈ Mᗮ := by
    rw [rhatEq]
    exact (Mᗮ).smul_mem _ rMem
  have innerResidual (g : H) (gMem : g ∈ Mᗮ) :
      inner ℝ g x = inner ℝ g r := by
    change inner ℝ g x = inner ℝ g (x - M.starProjection x)
    have projectedInner : inner ℝ g (M.starProjection x) = 0 := by
      apply Submodule.inner_left_of_mem_orthogonal (K := M.toSubmodule)
      · exact Submodule.starProjection_apply_mem M.toSubmodule x
      · simpa using gMem
    rw [inner_sub_right, projectedInner, sub_zero]
  have rhatInner : inner ℝ rhat x = ‖r‖ := by
    rw [innerResidual rhat rhatMem, rhatEq, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    field_simp
  have valueUpper (g : H) (gNorm : ‖g‖ ≤ 1) :
      abs (inner ℝ g r) ≤ ‖r‖ := by
    calc
      abs (inner ℝ g r) ≤ ‖g‖ * ‖r‖ := abs_real_inner_le_norm g r
      _ ≤ 1 * ‖r‖ :=
        mul_le_mul_of_nonneg_right gNorm (norm_nonneg r)
      _ = ‖r‖ := one_mul _
  have greatest : IsGreatest (separatingReadoutValues M x) ‖r‖ := by
    constructor
    · refine ⟨rhat, rhatMem, rhatNorm.le, ?_⟩
      rw [rhatInner, abs_of_pos rNormPos]
    · intro value valueMem
      rcases valueMem with ⟨g, gMem, gNorm, rfl⟩
      rw [innerResidual g gMem]
      exact valueUpper g gNorm
  have positiveUnique (g : H) (gNorm : ‖g‖ ≤ 1)
      (gInner : inner ℝ g r = ‖r‖) : g = rhat := by
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ)
    · simpa [rhatNorm] using gNorm
    · rw [rhatNorm, one_pow, rhatEq, real_inner_smul_right,
        RCLike.re_to_real, gInner]
      exact inv_mul_cancel₀ rNormPos.ne'
  have maximizers (g : H) (gMem : g ∈ Mᗮ) (gNorm : ‖g‖ ≤ 1) :
      abs (inner ℝ g x) = ‖r‖ ↔ g = rhat ∨ g = -rhat := by
    rw [innerResidual g gMem]
    constructor
    · intro absoluteEquality
      rcases (abs_eq rNormPos.le).mp absoluteEquality with
          positive | negative
      · exact Or.inl (positiveUnique g gNorm positive)
      · apply Or.inr
        have negNorm : ‖-g‖ ≤ 1 := by simpa using gNorm
        have negInner : inner ℝ (-g) r = ‖r‖ := by
          rw [inner_neg_left, negative, neg_neg]
        have negEq := positiveUnique (-g) negNorm negInner
        simpa only [neg_eq_iff_eq_neg] using negEq
    · rintro (rfl | rfl)
      · rw [← innerResidual rhat rhatMem, rhatInner, abs_of_pos rNormPos]
      · rw [inner_neg_left, ← innerResidual rhat rhatMem, rhatInner,
          abs_neg, abs_of_pos rNormPos]
  have positiveAligned (g : H) (gMem : g ∈ Mᗮ) (gNorm : ‖g‖ ≤ 1)
      (gInner : inner ℝ g x = ‖r‖) : g = rhat := by
    apply positiveUnique g gNorm
    rwa [← innerResidual g gMem]
  exact ⟨greatest.csSup_eq, greatest, maximizers, positiveAligned⟩

#print axioms canonical_strongest_separating_observer

end


end D5.S3.Observer.CanonicalStrongestSeparatingObserver
