/- GID: D5/S3/Observer/Reversal/QuadraticObservationClosure
   generality: G
   mirror-B: D5/B/S3/Observer/Reversal/QuadraticObservationClosure
   mirror-E: none(waiver:exact-symbolic-closure-criterion)
   anchors: []
   utility: none
   digest: Quadratic observed dynamics closes exactly when its hidden linear, hidden quadratic, and mixed terms vanish. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module

/-!
# Exact closure criterion for projected quadratic dynamics

For V(x)=Lx-B(x,x) and an idempotent observation P, closure is equivalent to
three coefficient conditions. Necessity is proved by the actual pairs b,-b
and a,a+b. Sufficiency uses the actual decomposition x=Px+(x-Px).
The closure map is allowed to be nonlinear. This is not merely an implication
from a supplied closure hypothesis or a definition of the desired conclusion.

The NS finite-mode consumer uses the canonical bilinear advection structure.
An application to the full PDE additionally needs the relevant function spaces
and Fourier/Leray identification. Source: the theory's Sections 1, 3 and 5.
Fang et al., arXiv:1112.0659, motivates full/partial scale reversal. Existing
AnswerabilityCriterion supplies the general fiber/factorization step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Observer.Reversal.QuadraticObservationClosure

open D5.S0.Rewriting.Quotients.AnswerabilityCriterion

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Linear drift minus the diagonal of a genuine bilinear map. -/
def vectorField (L : E →ₗ[ℝ] E) (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (x : E) : E :=
  L x - B x x

/-- The exact observed increment, including the hidden self-interaction. -/
theorem observed_increment (P L : E →ₗ[ℝ] E)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (a b : E) :
    P (vectorField L B (a + b)) - P (vectorField L B a) =
      P (L b) - P (B a b + B b a) - P (B b b) := by
  simp only [vectorField, map_sub, map_add, LinearMap.add_apply]
  module

/-- A complete necessary and sufficient condition for exact Markovian
closure of a quadratic vector field under a linear projection. -/
theorem quadratic_closure_iff (P L : E →ₗ[ℝ] E)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (hP : ∀ x, P (P x) = P x) :
    (∃ f : E → E, ∀ x, P (vectorField L B x) = f (P x)) ↔
      (∀ b, P b = 0 → P (L b) = 0) ∧
      (∀ b, P b = 0 → P (B b b) = 0) ∧
      (∀ a b, P a = a → P b = 0 → P (B a b + B b a) = 0) := by
  constructor
  · rintro ⟨f, hf⟩
    have hfzero : f 0 = 0 := by
      simpa only [vectorField, map_zero, LinearMap.zero_apply, sub_zero] using (hf 0).symm
    have hidden (b : E) (hb : P b = 0) : P (L b) = 0 ∧ P (B b b) = 0 := by
      have hplus : P (L b) - P (B b b) = 0 := by
        simpa only [vectorField, map_sub, hb, hfzero] using hf b
      have hminus : -P (L b) - P (B b b) = 0 := by
        simpa only [vectorField, map_neg, map_sub, LinearMap.neg_apply,
          neg_neg, hb, neg_zero, hfzero] using hf (-b)
      have hquadratic : P (B b b) = 0 := by
        calc
          P (B b b) = (-1 / 2 : ℝ) •
              ((P (L b) - P (B b b)) + (-P (L b) - P (B b b))) := by module
          _ = 0 := by rw [hplus, hminus, add_zero, smul_zero]
      have hlinear : P (L b) = 0 := by simpa only [hquadratic, sub_zero] using hplus
      exact ⟨hlinear, hquadratic⟩
    refine ⟨fun b hb => (hidden b hb).1, fun b hb => (hidden b hb).2, ?_⟩
    intro a b ha hb
    have hdiff : P (vectorField L B (a + b)) - P (vectorField L B a) = 0 := by
      rw [hf, hf, map_add, ha, hb, add_zero, sub_self]
    rw [observed_increment, (hidden b hb).1, (hidden b hb).2] at hdiff
    simpa only [zero_sub, sub_zero, neg_eq_zero] using hdiff
  · rintro ⟨hlinear, hquadratic, hmixed⟩
    refine ⟨fun y => P (vectorField L B y), ?_⟩
    intro x
    have hb : P (x - P x) = 0 := by rw [map_sub, hP x, sub_self]
    have hab : P x + (x - P x) = x := by module
    have h := observed_increment P L B (P x) (x - P x)
    rw [hab, hlinear _ hb, hmixed _ _ (hP x) hb, hquadratic _ hb,
      sub_zero, sub_zero] at h
    exact sub_eq_zero.mp h

/-- The coefficient criterion is equivalent to the pre-existing
answerability condition on all pairs in every observation fiber. -/
theorem quadratic_fiber_criterion (P L : E →ₗ[ℝ] E)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (hP : ∀ x, P (P x) = P x) :
    (∀ x y, P x = P y → P (vectorField L B x) = P (vectorField L B y)) ↔
      (∀ b, P b = 0 → P (L b) = 0) ∧
      (∀ b, P b = 0 → P (B b b) = 0) ∧
      (∀ a b, P a = a → P b = 0 → P (B a b + B b a) = 0) := by
  have hfactor := (answerability_criterion (0 : E) P
    (fun x => P (vectorField L B x))).1
  have hsame :
      (∃ f : E → E, (fun x => P (vectorField L B x)) = f ∘ P) ↔
        (∃ f : E → E, ∀ x, P (vectorField L B x) = f (P x)) := by
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨f, fun x => congrFun hf x⟩
    · rintro ⟨f, hf⟩
      exact ⟨f, funext hf⟩
  constructor
  · intro h
    apply (quadratic_closure_iff P L B hP).mp
    apply hsame.mp
    exact hfactor.mpr (fun {x y} hxy => h x y hxy)
  · intro h x y hxy
    obtain ⟨f, hf⟩ := (quadratic_closure_iff P L B hP).mpr h
    rw [hf, hf, hxy]

/-- Full and visible-only reversal have the same observed state. -/
theorem same_visible_negation (P : E →ₗ[ℝ] E) (a b : E) (hb : P b = 0) :
    P (-a - b) = -P a ∧ P (-a + b) = -P a := by
  simp only [map_sub, map_add, map_neg, hb, sub_zero, add_zero, and_self]

/-- The surviving mixed term is the exact difference between the two
observed accelerations. Linear hidden drift is the only extra hypothesis. -/
theorem reversal_acceleration_gap (P L : E →ₗ[ℝ] E)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (a b : E) (hlinear : P (L b) = 0) :
    P (vectorField L B (-a - b)) - P (vectorField L B (-a + b)) =
      (-2 : ℝ) • P (B a b + B b a) := by
  simp only [vectorField, map_sub, map_add, map_neg,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, neg_neg, hlinear]
  module

#print axioms vectorField
#print axioms observed_increment
#print axioms quadratic_closure_iff
#print axioms quadratic_fiber_criterion
#print axioms same_visible_negation
#print axioms reversal_acceleration_gap

end D5.S3.Observer.Reversal.QuadraticObservationClosure
