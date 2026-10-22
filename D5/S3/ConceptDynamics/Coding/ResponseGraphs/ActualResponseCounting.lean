/- GID: D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualResponseCounting
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseGraphs/ActualResponseCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual numbered lift fibers count response columns without a compatibility certificate. -/

import D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.Full62
import D5.S3.ConceptDynamics.Coding.ResponseKernelRecursion
import D5.S3.ConceptDynamics.Coding.FirstResponseDiamond

/-! Actual numbered-edge response construction in the existing Coding domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualResponseCounting

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
open D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.Full62
open D5.S3.ConceptDynamics.Coding.FirstResponseDiamond
open scoped BigOperators

variable {n q : ℕ} {A : CountMat n n} {C : CountMat q q}

/-- The full lift fiber retains the number of each actual C edge. -/
noncomputable def responseEdgeEquiv (I : ActualIncoming C A) (d : ℕ)
    (F : Quotient (I.stateLift.response d)) (v : Fin q) :
    incomingResponseFiber I.stateLift d F v ≃
      {c : Edge C // c.target = v ∧ Quotient.mk (I.stateLift.response d) c.source = F} := by
  classical
  let forward : incomingResponseFiber I.stateLift d F v →
      {c : Edge C // c.target = v ∧ Quotient.mk (I.stateLift.response d) c.source = F} :=
    fun x => ⟨I.liftEdge x.val ⟨v, Classical.choose x.property⟩,
      I.lift_target _ _, Classical.choose_spec x.property⟩
  let backward :
      {c : Edge C // c.target = v ∧ Quotient.mk (I.stateLift.response d) c.source = F} →
      incomingResponseFiber I.stateLift d F v := fun x => by
    have hv : I.project v = (I.readout x.val).target :=
      (congrArg I.project x.property.1).symm.trans (I.read_target x.val).symm
    refine ⟨I.readout x.val, hv, ?_⟩
    change Quotient.mk (I.stateLift.response d)
      (I.liftEdge (I.readout x.val) ⟨v, hv⟩).source = F
    rw [I.unique _ _ x.val x.property.1 rfl]
    exact x.property.2
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      intro x
      apply Subtype.ext
      exact I.lift_read _ _
    right_inv := by
      intro x
      apply Subtype.ext
      exact I.unique _ _ x.val x.property.1 rfl }

private def edgeSourceEquiv (d : ℕ) (I : ActualIncoming C A)
    (F : Quotient (I.stateLift.response d)) (v : Fin q) :
    {c : Edge C // c.target = v ∧ Quotient.mk (I.stateLift.response d) c.source = F} ≃
      Σ u : Fin q, {h : Fin (C u v) // Quotient.mk (I.stateLift.response d) u = F} where
  toFun := by
    rintro ⟨⟨u, w, h⟩, ht, hs⟩
    change w = v at ht
    subst w
    exact ⟨u, h, hs⟩
  invFun := fun x => ⟨⟨x.1, v, x.2.val⟩, rfl, x.2.property⟩
  left_inv := by
    rintro ⟨⟨u, w, h⟩, ht, hs⟩
    change w = v at ht
    subst w
    rfl
  right_inv := by rintro ⟨u, h, hs⟩; rfl

open Classical in
/-- Count by actual source states, at every response depth, including zero. -/
theorem incoming_response_fiber_count (I : ActualIncoming C A) (d : ℕ)
    (F : Quotient (I.stateLift.response d)) (v : Fin q) :
    Nat.card (incomingResponseFiber I.stateLift d F v) =
      ∑ u : Fin q, if Quotient.mk (I.stateLift.response d) u = F then C u v else 0 := by
  classical
  rw [Nat.card_congr ((responseEdgeEquiv I d F v).trans (edgeSourceEquiv d I F v)),
    Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : Quotient.mk (I.stateLift.response d) u = F
  · simp [h, Nat.card_eq_fintype_card]
  · simp [h, Nat.card_eq_fintype_card]

/-- Every numbering and every section give the literal incidence compression. -/
theorem response_matrix_reindexed (I : ActualIncoming C A) (d r : ℕ)
    (e : Quotient (I.stateLift.response d) ≃ Fin r)
    (rep : Fin r → Fin q)
    (hrep : ∀ f, e (Quotient.mk (I.stateLift.response d) (rep f)) = f) :
    Matrix.reindex e e (incomingResponseMatrix I.stateLift d) =
      columnMembership (fun u => e (Quotient.mk (I.stateLift.response d) u)) *
        C * columnSelector rep := by
  classical
  ext f g
  have hr : I.stateLift.response d (Quotient.out (e.symm g)) (rep g) := by
    apply Quotient.exact
    exact (Quotient.out_eq _).trans (e.injective (by simpa using hrep g)).symm
  change Nat.card (incomingResponseFiber I.stateLift d (e.symm f)
    (Quotient.out (e.symm g))) = _
  rw [incoming_response_fiber_card_step I.stateLift d (e.symm f)
    ((response_zero_and_step I.stateLift).2 d hr), incoming_response_fiber_count]
  have he (u : Fin q) :
      (Quotient.mk (I.stateLift.response d) u = e.symm f) ↔
      e (Quotient.mk (I.stateLift.response d) u) = f := by
    constructor
    · intro h; rw [h, e.apply_symm_apply]
    · intro h; exact e.injective (h.trans (e.apply_symm_apply f).symm)
  calc
    (∑ u : Fin q, if Quotient.mk (I.stateLift.response d) u = e.symm f
        then C u (rep g) else 0) =
        ∑ u : Fin q, columnMembership
          (fun x => e (Quotient.mk (I.stateLift.response d) x)) f u * C u (rep g) := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : e (Quotient.mk (I.stateLift.response d) u) = f
      · simp [columnMembership, he u, h]
      · simp [columnMembership, he u, h]
    _ = (columnMembership (fun x => e (Quotient.mk (I.stateLift.response d) x)) *
        C * columnSelector rep) f g := by
      simp only [Matrix.mul_apply, columnSelector]
      simp

/-- First-response equality forces equality of actual numbered C columns. -/
theorem first_response_columns (I : ActualIncoming C A) {u v : Fin q}
    (h : I.stateLift.response 1 u v) : ∀ x, C x u = C x v := by
  intro x
  let F := Quotient.mk (I.stateLift.response 0) x
  have hc (w : Fin q) :
      Nat.card (incomingResponseFiber I.stateLift 0 F w) = C x w := by
    rw [incoming_response_fiber_count]
    have he (z : Fin q) :
        (Quotient.mk (I.stateLift.response 0) z = F) ↔ z = x := by
      constructor
      · intro hz
        have hh := Quotient.exact hz
        rw [(response_zero_and_step I.stateLift).1] at hh
        exact hh
      · intro hz; subst z; rfl
    simp_rw [he]
    simp
  exact (hc u).symm.trans ((incoming_response_fiber_card_step I.stateLift 0 F h).trans (hc v))

#print axioms incoming_response_fiber_count
#print axioms response_matrix_reindexed
#print axioms first_response_columns

end D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualResponseCounting
