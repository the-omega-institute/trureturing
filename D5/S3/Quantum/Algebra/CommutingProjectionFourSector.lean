/- GID: D5/S3/Quantum/Algebra/CommutingProjectionFourSector
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/CommutingProjectionFourSector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Commuting orthogonal projections admit the common four-sector decompositions. -/

import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.TFAE

/- Library-search audit trail (2026-08-16):
   * Repository searches for the four-sector criterion and joint projection
     measures found no theorem with the statement below. The finite-matrix
     record-measurement declarations are narrower than the source statement.
   * Loogle's query `IsStarProjection (?p * ?q)` returned the exact theorem
     `IsStarProjection.mul`; it is imported and applied below.
   * Pinned Mathlib also supplied `isStarProjection_iff_eq_starProjection_range`,
     `Submodule.starProjection_comp_starProjection_eq_zero_iff`,
     `OrthogonalFamily.of_pairwise`, `OrthogonalFamily.independent`, and
     `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`.
   * LeanSearch found projection characterizations and direct-sum lemmas, but
     no declaration packaging all four equivalent conditions. -/

noncomputable section

open scoped InnerProductSpace
open ContinuousLinearMap

namespace D5.S3.Quantum.Algebra.CommutingProjectionFourSector

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The four products selected by membership in the ranges of `P` and `Q`. -/
def fourSector (P Q : E →L[𝕜] E) : Bool × Bool → E →L[𝕜] E
  | (false, false) => (1 - P) * (1 - Q)
  | (false, true) => (1 - P) * Q
  | (true, false) => P * (1 - Q)
  | (true, true) => P * Q

private def projectionChoice (P : E →L[𝕜] E) : Bool → E →L[𝕜] E
  | false => 1 - P
  | true => P

omit [CompleteSpace E] in
private theorem fourSector_eq_projectionChoices
    (P Q : E →L[𝕜] E) (a b : Bool) :
    fourSector P Q (a, b) = projectionChoice P a * projectionChoice Q b := by
  cases a <;> cases b <;> rfl

/-- A four-outcome projection measure, expressed by its finite algebraic data. -/
def IsFourOutcomeProjectionMeasure (R : Bool × Bool → E →L[𝕜] E) : Prop :=
  (∀ i, IsStarProjection (R i)) ∧
    Pairwise (fun i j => R i * R j = 0) ∧
    ∑ i, R i = 1

omit [CompleteSpace E] in
private theorem fourSector_sum (P Q : E →L[𝕜] E) :
    ∑ i, fourSector P Q i = 1 := by
  rw [show (Finset.univ : Finset (Bool × Bool)) =
    {(false, false), (false, true), (true, false), (true, true)} by decide]
  simp only [fourSector, Finset.mem_insert, Prod.mk.injEq, Bool.false_eq_true, and_false,
    and_true, Finset.mem_singleton, and_self, or_self, not_false_eq_true,
    Finset.sum_insert, Bool.true_eq_false, Finset.sum_singleton]
  noncomm_ring

private theorem fourSector_isStarProjection
    {P Q : E →L[𝕜] E} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPQ : Commute P Q) (i : Bool × Bool) :
    IsStarProjection (fourSector P Q i) := by
  have hP_Qc : Commute P (1 - Q) := by
    rw [commute_iff_eq]
    noncomm_ring [hPQ.eq]
  have hPc_Q : Commute (1 - P) Q := by
    rw [commute_iff_eq]
    noncomm_ring [hPQ.eq]
  have hPc_Qc : Commute (1 - P) (1 - Q) := by
    rw [commute_iff_eq]
    noncomm_ring [hPQ.eq]
  rcases i with ⟨a, b⟩
  cases a <;> cases b
  · exact hP.one_sub.mul hQ.one_sub hPc_Qc
  · exact hP.one_sub.mul hQ hPc_Q
  · exact hP.mul hQ.one_sub hP_Qc
  · exact hP.mul hQ hPQ

private theorem fourSector_mul_eq_zero_of_ne_commuting
    {P Q : E →L[𝕜] E} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPQ : Commute P Q) {i j : Bool × Bool} (hij : i ≠ j) :
    fourSector P Q i * fourSector P Q j = 0 := by
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, d⟩
  rw [fourSector_eq_projectionChoices, fourSector_eq_projectionChoices]
  have hCross : Commute (projectionChoice Q b) (projectionChoice P c) := by
    cases b <;> cases c
    all_goals rw [commute_iff_eq]
    all_goals simp only [projectionChoice]
    all_goals noncomm_ring [hPQ.eq]
  have hReorder :
      (projectionChoice P a * projectionChoice Q b) *
          (projectionChoice P c * projectionChoice Q d) =
        (projectionChoice P a * projectionChoice P c) *
          (projectionChoice Q b * projectionChoice Q d) := by
    calc
      (projectionChoice P a * projectionChoice Q b) *
          (projectionChoice P c * projectionChoice Q d) =
        projectionChoice P a *
            (projectionChoice Q b * projectionChoice P c) * projectionChoice Q d := by
          simp only [mul_assoc]
      _ = projectionChoice P a *
            (projectionChoice P c * projectionChoice Q b) * projectionChoice Q d := by
          rw [hCross.eq]
      _ = (projectionChoice P a * projectionChoice P c) *
          (projectionChoice Q b * projectionChoice Q d) := by
          simp only [mul_assoc]
  rw [hReorder]
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro hbd
      exact hij (Prod.ext hac hbd)
    have hZero : projectionChoice Q b * projectionChoice Q d = 0 := by
      cases b <;> cases d
      all_goals simp_all [projectionChoice, hQ.mul_one_sub_self, hQ.one_sub_mul_self]
    rw [hZero, mul_zero]
  · have hZero : projectionChoice P a * projectionChoice P c = 0 := by
      cases a <;> cases c
      all_goals simp_all [projectionChoice, hP.mul_one_sub_self, hP.one_sub_mul_self]
    rw [hZero, zero_mul]

omit [CompleteSpace E] in
private theorem fourSector_mul_eq_zero_of_ne_internal
    {P Q : E →L[𝕜] E}
    (hInternal : DirectSum.IsInternal (fun i => (fourSector P Q i).range))
    {i j : Bool × Bool} (hij : i ≠ j) :
    fourSector P Q i * fourSector P Q j = 0 := by
  ext x
  have hUnique :=
    (iSupIndep_iff_finsetSum_eq_imp_eq
      (fun i => (fourSector P Q i).range)).mp hInternal.submodule_iSupIndep
  have hComponents := hUnique Finset.univ
    (fun k => fourSector P Q k (fourSector P Q j x))
    (fun k => if k = j then fourSector P Q j x else 0) (by
      intro k hk
      constructor
      · exact ⟨fourSector P Q j x, rfl⟩
      · by_cases hkj : k = j
        · subst k
          rw [if_pos rfl]
          exact ⟨x, rfl⟩
        · simp only [if_neg hkj]
          exact Submodule.zero_mem _) (by
      calc
        (∑ k ∈ Finset.univ, fourSector P Q k (fourSector P Q j x)) =
            (∑ k, fourSector P Q k) (fourSector P Q j x) := by simp
        _ = fourSector P Q j x := by rw [fourSector_sum]; rfl
        _ = ∑ k ∈ Finset.univ, if k = j then fourSector P Q j x else 0 := by simp)
  have hi := hComponents i (Finset.mem_univ i)
  simpa [hij, mul_apply_eq_comp] using hi

omit [CompleteSpace E] in
private theorem commute_of_internal_fourSector_ranges
    {P Q : E →L[𝕜] E}
    (hInternal : DirectSum.IsInternal (fun i => (fourSector P Q i).range)) :
    P * Q = Q * P := by
  have hBA := fourSector_mul_eq_zero_of_ne_internal hInternal
    (i := (true, false)) (j := (true, true)) (by decide)
  have hDA := fourSector_mul_eq_zero_of_ne_internal hInternal
    (i := (false, false)) (j := (true, true)) (by decide)
  have hAB := fourSector_mul_eq_zero_of_ne_internal hInternal
    (i := (true, true)) (j := (true, false)) (by decide)
  have hCB := fourSector_mul_eq_zero_of_ne_internal hInternal
    (i := (false, true)) (j := (true, false)) (by decide)
  simp only [fourSector] at hBA hDA hAB hCB
  have hLeft : (1 - Q) * (P * Q) = 0 := by
    calc
      (1 - Q) * (P * Q) =
          (P + (1 - P)) * (1 - Q) * (P * Q) := by noncomm_ring
      _ = P * (1 - Q) * (P * Q) + (1 - P) * (1 - Q) * (P * Q) := by
        noncomm_ring
      _ = 0 := by rw [hBA, hDA, zero_add]
  have hRight : Q * (P * (1 - Q)) = 0 := by
    calc
      Q * (P * (1 - Q)) =
          (P + (1 - P)) * Q * (P * (1 - Q)) := by noncomm_ring
      _ = P * Q * (P * (1 - Q)) + (1 - P) * Q * (P * (1 - Q)) := by
        noncomm_ring
      _ = 0 := by rw [hAB, hCB, zero_add]
  calc
    P * Q = (Q + (1 - Q)) * (P * Q) := by noncomm_ring
    _ = Q * (P * Q) + (1 - Q) * (P * Q) := by noncomm_ring
    _ = Q * (P * Q) := by rw [hLeft, add_zero]
    _ = Q * (P * Q) + Q * (P * (1 - Q)) := by rw [hRight, add_zero]
    _ = Q * (P * Q + P * (1 - Q)) := by rw [mul_add]
    _ = Q * P := by
      congr 1
      noncomm_ring

/-- For two orthogonal projections on a complete real or complex inner-product space, commutation,
projection of all four sector products, orthogonal internal decomposition by their ranges, and
existence of a four-outcome projection measure with the stated marginals are equivalent. -/
theorem commuting_projection_four_sector_criterion
    (P Q : E →L[𝕜] E) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    List.TFAE
      [P * Q = Q * P,
        ∀ i, IsStarProjection (fourSector P Q i),
        OrthogonalFamily 𝕜 (fun i => (fourSector P Q i).range)
            (fun i => (fourSector P Q i).range.subtypeₗᵢ) ∧
          DirectSum.IsInternal (fun i => (fourSector P Q i).range),
        ∃ R : Bool × Bool → E →L[𝕜] E,
          IsFourOutcomeProjectionMeasure R ∧
            P = R (true, false) + R (true, true) ∧
            Q = R (false, true) + R (true, true)] := by
  tfae_have 1 → 2 := by
    intro h i
    exact fourSector_isStarProjection hP hQ ((commute_iff_eq P Q).mpr h) i
  tfae_have 2 → 1 := by
    intro h
    have hSelf := (h (true, true)).isSelfAdjoint.star_eq
    simp only [fourSector, star_mul, hP.isSelfAdjoint.star_eq,
      hQ.isSelfAdjoint.star_eq] at hSelf
    exact hSelf.symm
  tfae_have 1 → 3 := by
    intro h
    have hComm : Commute P Q := (commute_iff_eq P Q).mpr h
    have hProj : ∀ i, IsStarProjection (fourSector P Q i) :=
      fourSector_isStarProjection hP hQ hComm
    have hOrthogonal :
        OrthogonalFamily 𝕜 (fun i => (fourSector P Q i).range)
          (fun i => (fourSector P Q i).range.subtypeₗᵢ) := by
      apply OrthogonalFamily.of_pairwise
      intro i j hij
      obtain ⟨hi, hiEq⟩ := isStarProjection_iff_eq_starProjection_range.mp (hProj i)
      obtain ⟨hj, hjEq⟩ := isStarProjection_iff_eq_starProjection_range.mp (hProj j)
      letI := hi
      letI := hj
      change (fourSector P Q i).range ⟂ (fourSector P Q j).range
      rw [← Submodule.starProjection_comp_starProjection_eq_zero_iff]
      rw [← hiEq, ← hjEq]
      simpa only [ContinuousLinearMap.mul_def] using
        fourSector_mul_eq_zero_of_ne_commuting hP hQ hComm hij
    refine ⟨hOrthogonal, DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      hOrthogonal.independent ?_⟩
    apply top_unique
    intro x hx
    have hxSum : x = ∑ i, fourSector P Q i x := by
      have := DFunLike.congr_fun (fourSector_sum P Q) x
      simpa using this.symm
    rw [hxSum]
    exact Submodule.sum_mem_iSup fun i => ⟨x, rfl⟩
  tfae_have 3 → 1 := by
    intro h
    exact commute_of_internal_fourSector_ranges h.2
  tfae_have 1 → 4 := by
    intro h
    have hComm : Commute P Q := (commute_iff_eq P Q).mpr h
    refine ⟨fourSector P Q, ⟨?_, ?_, fourSector_sum P Q⟩, ?_, ?_⟩
    · exact fourSector_isStarProjection hP hQ hComm
    · intro i j hij
      exact fourSector_mul_eq_zero_of_ne_commuting hP hQ hComm hij
    · simp only [fourSector]
      noncomm_ring
    · simp only [fourSector]
      noncomm_ring
  tfae_have 4 → 1 := by
    rintro ⟨R, ⟨hRProj, hROrthogonal, _hRSum⟩, hPMarginal, hQMarginal⟩
    have h10_01 : R (true, false) * R (false, true) = 0 :=
      hROrthogonal (by decide)
    have h10_11 : R (true, false) * R (true, true) = 0 :=
      hROrthogonal (by decide)
    have h11_01 : R (true, true) * R (false, true) = 0 :=
      hROrthogonal (by decide)
    have h01_10 : R (false, true) * R (true, false) = 0 :=
      hROrthogonal (by decide)
    have h01_11 : R (false, true) * R (true, true) = 0 :=
      hROrthogonal (by decide)
    have h11_10 : R (true, true) * R (true, false) = 0 :=
      hROrthogonal (by decide)
    rw [hPMarginal, hQMarginal]
    calc
      (R (true, false) + R (true, true)) *
          (R (false, true) + R (true, true)) = R (true, true) := by
        noncomm_ring [h10_01, h10_11, h11_01,
          (hRProj (true, true)).isIdempotentElem.eq]
      _ = (R (false, true) + R (true, true)) *
          (R (true, false) + R (true, true)) := by
        symm
        noncomm_ring [h01_10, h01_11, h11_10,
          (hRProj (true, true)).isIdempotentElem.eq]
  tfae_finish

example : 𝕜 := 0

example :
    IsStarProjection (0 : ℝ →L[ℝ] ℝ) ∧ IsStarProjection (1 : ℝ →L[ℝ] ℝ) := by
  simp

#print axioms commuting_projection_four_sector_criterion

end D5.S3.Quantum.Algebra.CommutingProjectionFourSector
