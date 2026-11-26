/- GID: D5/S3/Quantum/AURICOmega/NonobtuseFamilyFixedVector
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/NonobtuseFamilyFixedVector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nonobtuse unit family has a nonzero least-norm hull point fixed by its symmetries. -/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# A fixed vector for a nonobtuse family of unit vectors

Let `S` be a nonempty family of unit vectors in a finite-dimensional real inner-product space
whose members have pairwise nonnegative inner products. Every point of the convex hull of `S` is,
by Caratheodory's theorem, a convex combination of at most `finrank + 1` members of `S`, and the
nonnegativity of the cross terms gives the uniform bound `1 / (finrank + 1) ≤ ‖x‖ ^ 2`. Hence
the closed convex hull `K` of `S` avoids the origin, and its least-norm point `m` is nonzero.
The variational inequality of the least-norm point reads `‖m‖ ^ 2 ≤ ⟪x, m⟫` on `K`; it forces
every point of `K` with the norm of `m` to equal `m`. A linear isometry equivalence mapping `S`
into itself maps `K` into itself, so it fixes `m`.
-/

namespace D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector

open scoped InnerProductSpace
open Module

/-- Every point of the convex hull of a family of unit vectors with pairwise nonnegative inner
products has squared norm at least `1 / (finrank + 1)`. -/
private theorem one_div_finrank_succ_le_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hunit : ∀ s ∈ S, ‖s‖ = 1)
    (hpos : ∀ s ∈ S, ∀ t ∈ S, 0 ≤ ⟪s, t⟫_ℝ) {x : E} (hx : x ∈ convexHull ℝ S) :
    1 / ((finrank ℝ E : ℝ) + 1) ≤ ‖x‖ ^ 2 := by
  obtain ⟨ι, _, z, w, hz, hai, hw, hw1, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hzS : ∀ i, z i ∈ S := fun i => hz ⟨i, rfl⟩
  have hcard : (Fintype.card ι : ℝ) ≤ (finrank ℝ E : ℝ) + 1 := by
    exact_mod_cast hai.card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have hcs : 1 ≤ (Fintype.card ι : ℝ) * ∑ i, w i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w)
    rw [hw1, one_pow, Finset.card_univ] at h
    exact h
  have hsq : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (w i)
  have hnorm : ∑ i, w i ^ 2 ≤ ‖∑ i, w i • z i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [inner_sum]
    calc w i ^ 2 = ⟪w i • z i, w i • z i⟫_ℝ := by
          rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
            hunit _ (hzS i)]
          ring
      _ ≤ ∑ j, ⟪w i • z i, w j • z j⟫_ℝ := by
          refine Finset.single_le_sum (f := fun j => ⟪w i • z i, w j • z j⟫_ℝ)
            (fun j _ => ?_) (Finset.mem_univ i)
          rw [real_inner_smul_left, real_inner_smul_right]
          exact mul_nonneg (hw i).le (mul_nonneg (hw j).le (hpos _ (hzS i) _ (hzS j)))
  rw [div_le_iff₀ (by positivity)]
  calc (1 : ℝ) ≤ (Fintype.card ι : ℝ) * ∑ i, w i ^ 2 := hcs
    _ ≤ ((finrank ℝ E : ℝ) + 1) * ∑ i, w i ^ 2 := mul_le_mul_of_nonneg_right hcard hsq
    _ ≤ ((finrank ℝ E : ℝ) + 1) * ‖∑ i, w i • z i‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = ‖∑ i, w i • z i‖ ^ 2 * ((finrank ℝ E : ℝ) + 1) := mul_comm _ _

/-- If `‖m‖ ^ 2 ≤ ⟪m', m⟫` and `‖m'‖ = ‖m‖`, then `m' = m`. -/
private theorem eq_of_norm_sq_le_inner_of_norm_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m m' : E}
    (h : ‖m‖ ^ 2 ≤ ⟪m', m⟫_ℝ) (hn : ‖m'‖ = ‖m‖) : m' = m := by
  have hsub : ‖m' - m‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, hn]
    linarith
  have hzero : ‖m' - m‖ = 0 := by
    nlinarith [norm_nonneg (m' - m)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- A nonempty family of unit vectors with pairwise nonnegative inner products in a
finite-dimensional real inner-product space has a nonzero least-norm point `m` in its closed
convex hull. It satisfies `‖m‖ ^ 2 ≤ ⟪x, m⟫` on the closed convex hull, and every linear
isometry equivalence mapping the family into itself fixes `m`. -/
theorem exists_fixed_ne_zero_of_pairwise_inner_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Set E) (hS : S.Nonempty) (hunit : ∀ s ∈ S, ‖s‖ = 1)
    (hpos : ∀ s ∈ S, ∀ t ∈ S, 0 ≤ ⟪s, t⟫_ℝ) :
    ∃ m : E, m ≠ 0 ∧ m ∈ closure (convexHull ℝ S) ∧
      (∀ x ∈ closure (convexHull ℝ S), ‖m‖ ≤ ‖x‖) ∧
      (∀ x ∈ closure (convexHull ℝ S), ‖m‖ ^ 2 ≤ ⟪x, m⟫_ℝ) ∧
      (∀ U : E ≃ₗᵢ[ℝ] E, U '' S ⊆ S → U m = m) := by
  obtain ⟨s₀, hs₀⟩ := hS
  have hKne : (closure (convexHull ℝ S)).Nonempty :=
    ⟨s₀, subset_closure (subset_convexHull ℝ S hs₀)⟩
  have hKconv : Convex ℝ (closure (convexHull ℝ S)) := (convex_convexHull ℝ S).closure
  have hKcomp : IsComplete (closure (convexHull ℝ S)) := isClosed_closure.isComplete
  obtain ⟨m, hmK, hm⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKconv 0
  have hvar : ∀ x ∈ closure (convexHull ℝ S), ‖m‖ ^ 2 ≤ ⟪x, m⟫_ℝ := by
    intro x hx
    have h := (norm_eq_iInf_iff_real_inner_le_zero hKconv hmK).1 hm x hx
    rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at h
    linarith [real_inner_comm x m]
  have hbound : closure (convexHull ℝ S) ⊆ {x : E | 1 / ((finrank ℝ E : ℝ) + 1) ≤ ‖x‖ ^ 2} :=
    closure_minimal (fun x hx => one_div_finrank_succ_le_norm_sq hunit hpos hx)
      (isClosed_le continuous_const (continuous_norm.pow 2))
  have hm0 : m ≠ 0 := by
    intro h
    have hb : 1 / ((finrank ℝ E : ℝ) + 1) ≤ ‖m‖ ^ 2 := hbound hmK
    rw [h, norm_zero, zero_pow two_ne_zero] at hb
    have hp : 0 < 1 / ((finrank ℝ E : ℝ) + 1) := by positivity
    linarith
  refine ⟨m, hm0, hmK, ?_, hvar, ?_⟩
  · intro x hx
    have hmpos : 0 < ‖m‖ := norm_pos_iff.mpr hm0
    have h : ‖m‖ * ‖m‖ ≤ ‖x‖ * ‖m‖ := by
      calc ‖m‖ * ‖m‖ = ‖m‖ ^ 2 := (sq _).symm
        _ ≤ ⟪x, m⟫_ℝ := hvar x hx
        _ ≤ ‖x‖ * ‖m‖ := real_inner_le_norm x m
    exact le_of_mul_le_mul_right h hmpos
  · intro U hU
    have himage : U '' closure (convexHull ℝ S) ⊆ closure (convexHull ℝ S) := by
      calc U '' closure (convexHull ℝ S) ⊆ closure (U '' convexHull ℝ S) :=
            image_closure_subset_closure_image U.continuous
        _ ⊆ closure (convexHull ℝ S) := by
            rw [show U '' convexHull ℝ S = convexHull ℝ (U '' S) from
              LinearMap.image_convexHull (U.toLinearEquiv : E →ₗ[ℝ] E) S]
            exact closure_mono (convexHull_mono hU)
    exact eq_of_norm_sq_le_inner_of_norm_eq (hvar (U m) (himage ⟨m, hmK, rfl⟩))
      (U.norm_map m)

end D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector
