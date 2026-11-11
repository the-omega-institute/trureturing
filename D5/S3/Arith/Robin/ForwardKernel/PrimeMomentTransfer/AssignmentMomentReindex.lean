/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AssignmentMomentReindex
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AssignmentMomentReindex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite assignment moments are invariant under enumeration. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticMomentDefs

/-! Finite assignment moments and ordered distinct-index moments agree under enumeration. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {ι A B : Type*} [Fintype ι] [Fintype B] [DecidableEq B] [CommRing A] [Algebra ℝ A]

omit [Fintype B] [DecidableEq B] in
/-- Any enumeration of a finite retained type gives the ordered distinct-index moment. -/
theorem assignment_moment_reindex {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (e : T ≃ Fin n) (w : T → ι → ℝ) :
    (∑ x : T → ι with Function.Injective x,
      (∏ t : T, w t (x t)) * ℓ (∏ t, Y (x t))) =
      distinctIndexMoment ℓ Y (fun i : Fin n => w (e.symm i)) := by
  unfold distinctIndexMoment
  apply Finset.sum_bij (fun x _ => x ∘ e.symm)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.comp e.symm.injective
  · intro x hx y hy hxy
    funext t
    have h := congrFun hxy (e t)
    simpa using h
  · intro y hy
    refine ⟨y ∘ e, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hy.comp e.injective
    · funext i
      simp
  · intro x hx
    congr 1
    · exact (Fintype.prod_equiv e
        (fun t => w t (x t)) (fun i => w (e.symm i)
          (x (e.symm i))) (by intro t; simp))
    · congr 1
      exact Fintype.prod_equiv e
        (fun t => Y (x t)) (fun i => Y (x (e.symm i)))
        (by intro t; simp)

omit [Fintype B] in
/-- Enumerating a finite retained set gives the existing ordered distinct-index moment. -/
theorem retained_assignment_reindex (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (S : Finset B) (w : B → ι → ℝ) :
    (∑ x : S → ι with Function.Injective x,
      (∏ t : S, w t (x t)) * ℓ (∏ t, Y (x t))) =
      distinctIndexMoment ℓ Y (fun i : Fin (Fintype.card S) =>
        w ((Fintype.equivFin S).symm i)) := by
  exact assignment_moment_reindex ℓ Y (Fintype.equivFin S) (fun t : S => w t)

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
