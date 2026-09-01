/- GID: D5/S3/Observer/AgencyHolonomy/LocalEulerFrameHistoryNonreconstruction
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/LocalEulerFrameHistoryNonreconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Euler determinants cannot reconstruct prime-indexed frame history. -/

import D5.S3.Observer.AgencyHolonomy.LocalEulerTransitionNonreconstruction

/- Library-search audit trail (2026-09-02):
   * Current D5 contains the exact local determinant and unequal-transition
     carrier in `LocalEulerTransitionNonreconstruction`; it is imported and
     applied below. Its public statement does not expose distinct frame
     histories or the no-decoder consequence required here.
   * Pinned Mathlib supplies `Matrix.det_units_conj`, already used by that frozen
     owner. No upstream theorem packages the additional reconstruction clause.
   * Reachable GitHub Lean-code and repository searches for isospectral observer
     reconstruction and determinant/transition combinations found no exact hit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.LocalEulerFrameHistoryNonreconstruction

open D5.S3.Observer.AgencyHolonomy.LocalEulerTransitionNonreconstruction

noncomputable section

/-- The canonical prime-indexed two-branch local Euler determinants retain only
the eigenvalue shadow `1, chi p`. Two frame histories share every such scalar
determinant while remaining distinct and inducing different transitions, so no
decoder of the determinant family can reconstruct both histories. -/
theorem local_euler_determinants_do_not_reconstruct_frame_history
    (chi : Nat.Primes → Complex) :
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    let p3 : Nat.Primes := ⟨3, Nat.prime_three⟩
    let localOperator : Nat.Primes → Matrix (Fin 2) (Fin 2) Complex :=
      fun p => Matrix.diagonal fun branch => if branch = 0 then 1 else chi p
    ∃ firstFrame secondFrame : Nat.Primes → GL (Fin 2) Complex,
      (∀ p x,
        Matrix.det
            (1 - x •
              ((firstFrame p).val * localOperator p * ((firstFrame p)⁻¹).val)) =
          (1 - x) * (1 - x * chi p)) ∧
      (∀ p x,
        Matrix.det
            (1 - x •
              ((secondFrame p).val * localOperator p * ((secondFrame p)⁻¹).val)) =
          (1 - x) * (1 - x * chi p)) ∧
      firstFrame ≠ secondFrame ∧
      (firstFrame p3)⁻¹ * firstFrame p2 ≠
        (secondFrame p3)⁻¹ * secondFrame p2 ∧
      ¬ ∃ reconstruct :
          (Nat.Primes → Complex → Complex) →
            Nat.Primes → GL (Fin 2) Complex,
        reconstruct (fun p x =>
          Matrix.det
            (1 - x •
              ((firstFrame p).val * localOperator p *
                ((firstFrame p)⁻¹).val))) = firstFrame ∧
        reconstruct (fun p x =>
          Matrix.det
            (1 - x •
              ((secondFrame p).val * localOperator p *
                ((secondFrame p)⁻¹).val))) = secondFrame := by
  dsimp only
  obtain ⟨firstFrame, secondFrame, firstDeterminants,
      secondDeterminants, differentTransition⟩ :=
    local_euler_determinants_do_not_determine_transition chi
  have differentHistories : firstFrame ≠ secondFrame := by
    intro equalHistories
    apply differentTransition
    rw [equalHistories]
  have sameDeterminantFamily :
      (fun (p : Nat.Primes) (x : Complex) =>
        Matrix.det
          (1 - x •
            ((firstFrame p).val *
              (Matrix.diagonal fun branch : Fin 2 =>
                if branch = 0 then 1 else chi p) *
              ((firstFrame p)⁻¹).val))) =
        fun (p : Nat.Primes) (x : Complex) =>
          Matrix.det
            (1 - x •
              ((secondFrame p).val *
                (Matrix.diagonal fun branch : Fin 2 =>
                  if branch = 0 then 1 else chi p) *
                ((secondFrame p)⁻¹).val)) := by
    funext p x
    exact (firstDeterminants p x).trans (secondDeterminants p x).symm
  have noReconstructor :
      ¬ ∃ reconstruct :
          (Nat.Primes → Complex → Complex) →
            Nat.Primes → GL (Fin 2) Complex,
        reconstruct (fun p x =>
          Matrix.det
            (1 - x •
              ((firstFrame p).val *
                (Matrix.diagonal fun branch : Fin 2 =>
                  if branch = 0 then 1 else chi p) *
                ((firstFrame p)⁻¹).val))) = firstFrame ∧
        reconstruct (fun p x =>
          Matrix.det
            (1 - x •
              ((secondFrame p).val *
                (Matrix.diagonal fun branch : Fin 2 =>
                  if branch = 0 then 1 else chi p) *
                ((secondFrame p)⁻¹).val))) = secondFrame := by
    rintro ⟨reconstruct, recoversFirst, recoversSecond⟩
    apply differentHistories
    calc
      firstFrame = reconstruct (fun p x =>
          Matrix.det
            (1 - x •
              ((firstFrame p).val *
                (Matrix.diagonal fun branch : Fin 2 =>
                  if branch = 0 then 1 else chi p) *
                ((firstFrame p)⁻¹).val))) := recoversFirst.symm
      _ = reconstruct (fun p x =>
          Matrix.det
            (1 - x •
              ((secondFrame p).val *
                (Matrix.diagonal fun branch : Fin 2 =>
                  if branch = 0 then 1 else chi p) *
                ((secondFrame p)⁻¹).val))) :=
        congrArg reconstruct sameDeterminantFamily
      _ = secondFrame := recoversSecond
  exact ⟨firstFrame, secondFrame, firstDeterminants, secondDeterminants,
    differentHistories, differentTransition, noReconstructor⟩

#print axioms local_euler_determinants_do_not_reconstruct_frame_history

end

end D5.S3.Observer.AgencyHolonomy.LocalEulerFrameHistoryNonreconstruction
