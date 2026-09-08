/- GID: D5/S3/Observer/Hankel/ProjectedExactDescent
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/ProjectedExactDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Global one-step descent propagates through every driven time step. -/

import D5.S3.Observer.Hankel.ProjectedRealizationError

/- Reuse audit (2026-09-05): the exact-descent kernel criterion and iterate
   semiconjugacy already belong to the existing observer library/Mathlib.
   This module is the forced-input consumer for the newly constructed reduced
   model. It also corrects the theory-volume claim that a fixed global exact
   descent could later fail merely because hidden directions receive leakage. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.ProjectedExactDescent

open D5.S3.Observer.Hankel.ProjectedRealizationError

variable {U V W Y : Type}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A fixed global intertwining equation propagates to every driven time step. -/
theorem projectedState_eq_of_descent
    (A : V →L[ℝ] V) (B : U →L[ℝ] V)
    (P : V →L[ℝ] W) (J : W →L[ℝ] V)
    (descends : P.comp A = (reducedDynamics A P J).comp P)
    (input : ℕ → U) (n : ℕ) :
    P (drivenState A B input n) =
      drivenState (reducedDynamics A P J) (reducedInput B P) input n := by
  induction n with
  | zero => simp only [drivenState, map_zero]
  | succ n ih =>
      have step := congrArg
        (fun f : V →L[ℝ] W => f (drivenState A B input n)) descends
      change P (A (drivenState A B input n)) =
        reducedDynamics A P J (P (drivenState A B input n)) at step
      change P (A (drivenState A B input n) + B (input n)) =
        reducedDynamics A P J
          (drivenState (reducedDynamics A P J) (reducedInput B P) input n) +
        reducedInput B P (input n)
      rw [map_add, step, ih]
      rfl

/-- Exact visible descent preserves every output that factors through the
projection, even when the lift's full-state residual does not vanish. -/
theorem outputs_eq_of_descent
    (A : V →L[ℝ] V) (B : U →L[ℝ] V) (C : V →L[ℝ] Y)
    (P : V →L[ℝ] W) (J : W →L[ℝ] V)
    (descends : P.comp A = (reducedDynamics A P J).comp P)
    (outputFactors : C = (reducedOutput C J).comp P)
    (input : ℕ → U) (n : ℕ) :
    C (drivenState A B input n) =
      reducedOutput C J
        (drivenState (reducedDynamics A P J) (reducedInput B P) input n) := by
  calc
    _ = reducedOutput C J (P (drivenState A B input n)) :=
      congrArg (fun f : V →L[ℝ] Y => f (drivenState A B input n)) outputFactors
    _ = _ := congrArg (reducedOutput C J)
      (projectedState_eq_of_descent A B P J descends input n)

#print axioms projectedState_eq_of_descent
#print axioms outputs_eq_of_descent

end D5.S3.Observer.Hankel.ProjectedExactDescent
