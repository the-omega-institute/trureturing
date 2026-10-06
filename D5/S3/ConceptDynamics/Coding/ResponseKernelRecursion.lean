/- GID: D5/S3/ConceptDynamics/Coding/ResponseKernelRecursion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseKernelRecursion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual numbered incoming lifts determine the full response successor relation. -/

/- The path and lift operations are those of CompatibleResponseForgetting.
   The local append-lift calculation follows the calculation in that module's
   incoming_response_step proof. That source is Copyright The Omega Institute
   and is licensed under Apache-2.0. -/

import D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.ResponseKernelRecursion

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

/-- The successor response is exactly the common projection together with
    the preceding response of every actual incoming numbered edge lift. -/
theorem response_successor_iff {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q) (d : ℕ) (u v : Q) :
    L.response (d + 1) u v ↔
      L.project u = L.project v ∧
      ∀ (a : Edge A) (hu : L.project u = a.target)
        (hv : L.project v = a.target),
        L.response d (L.lift a ⟨u, hu⟩).val
          (L.lift a ⟨v, hv⟩).val := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h,
      fun a hu hv => incoming_response_step L d h a hu hv⟩
  · rintro ⟨hp, hstep⟩
    have splitLast : ∀ {r : ℕ} {i z : Fin n}
        (path : FinitePath A (r + 1) i z),
        ∃ (j : Fin n) (front : FinitePath A r i j)
          (last : Fin (A j z)), appendPath front last = path := by
      intro r
      induction r with
      | zero =>
          intro i z path
          cases path with
          | cons last tail =>
              cases tail with
              | nil _ => exact ⟨i, .nil i, last, rfl⟩
      | succ r ih =>
          intro i z path
          cases path with
          | cons first tail =>
              obtain ⟨j, front, last, heq⟩ := ih tail
              exact ⟨j, .cons first front, last, by
                simp only [appendPath, heq]⟩
    have liftAppend : ∀ {r : ℕ} {i j z : Fin n}
        (front : FinitePath A r i j) (last : Fin (A j z))
        (q : {x : Q // L.project x = z}),
        L.liftPath (appendPath front last) q =
          L.liftPath front (L.lift ⟨j, z, last⟩ q) := by
      intro r i j z front
      induction front with
      | nil i => intro last q; rfl
      | @cons r i j z first tail ih =>
          intro last q
          simp only [appendPath, IncomingLift.liftPath]
          exact congrArg (L.lift ⟨i, j, first⟩) (ih last q)
    change L.responseReadout (d + 1) u = L.responseReadout (d + 1) v
    apply Prod.ext hp
    funext i z path
    by_cases hu : L.project u = z
    · have hv : L.project v = z := hp.symm.trans hu
      simp only [IncomingLift.responseReadout, dif_pos hu, dif_pos hv,
        Option.some.injEq]
      obtain ⟨j, front, last, hpath⟩ := splitLast path
      have hr := hstep (⟨j, z, last⟩ : Edge A) hu hv
      have hrObs : L.responseReadout d
          (L.lift (⟨j, z, last⟩ : Edge A) ⟨u, hu⟩).val =
          L.responseReadout d
          (L.lift (⟨j, z, last⟩ : Edge A) ⟨v, hv⟩).val := hr
      have hobs := congrArg (fun obs => obs.2 i j front) hrObs
      have hleft : L.project (L.lift (⟨j, z, last⟩ : Edge A) ⟨u, hu⟩).val = j :=
        (L.lift (⟨j, z, last⟩ : Edge A) ⟨u, hu⟩).property
      have hright : L.project (L.lift (⟨j, z, last⟩ : Edge A) ⟨v, hv⟩).val = j :=
        (L.lift (⟨j, z, last⟩ : Edge A) ⟨v, hv⟩).property
      simp only [IncomingLift.responseReadout, dif_pos hleft, dif_pos hright,
        Option.some.injEq] at hobs
      rw [← hpath, liftAppend front last ⟨u, hu⟩,
        liftAppend front last ⟨v, hv⟩]
      exact hobs
    · have hv : L.project v ≠ z := fun h => hu (hp.trans h)
      simp only [IncomingLift.responseReadout, dif_neg hu, dif_neg hv]

#print axioms response_successor_iff

end D5.S3.ConceptDynamics.Coding.ResponseKernelRecursion
