/- GID: D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct
   generality: I
   mirror-B: D5/B/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.claim; result=D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.result; claim=D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.claim
   digest: Two positive doubly stochastic kernels with P^2 = Q^2 = Pi can have opposite inner product 1 + r^2. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.TwoStepMixingOppositeProduct

open Finset

/-- A kernel on a finite space is positive and doubly stochastic. -/
def PositiveDoublyStochastic {X : Type} [Fintype X] (P : X → X → ℝ) : Prop :=
  (∀ x y, 0 < P x y) ∧ (∀ x, ∑ y, P x y = 1) ∧ ∀ y, ∑ x, P x y = 1

/-- Two steps of the kernel reach the uniform kernel `Π(x, z) = 1/|X|`. -/
def MixesInTwoSteps {X : Type} [Fintype X] (P : X → X → ℝ) : Prop :=
  ∀ x z, ∑ y, P x y * P y z = 1 / Fintype.card X

/-- The one-step opposite-direction inner product `E_U[n P(X₀, X₁) · n Q(X₁, X₀)]` under the
uniform product reference on pairs of states. -/
noncomputable def oppositeInnerProduct {X : Type} [Fintype X] (P Q : X → X → ℝ) : ℝ :=
  (1 / (Fintype.card X : ℝ) ^ 2) *
    ∑ x, ∑ y, (Fintype.card X * P x y) * (Fintype.card X * Q y x)

/-- A pair of kernels on one finite state space. -/
structure FiniteKernelPair where
  /-- The state space. -/
  State : Type
  [instFintype : Fintype State]
  /-- The first kernel. -/
  P : State → State → ℝ
  /-- The second kernel. -/
  Q : State → State → ℝ

attribute [instance] FiniteKernelPair.instFintype

/-- The claim that two-step mixing of two positive doubly stochastic kernels forces the
one-step opposite-direction inner product to equal one. -/
def claim : Prop :=
  ∀ k : FiniteKernelPair, PositiveDoublyStochastic k.P → PositiveDoublyStochastic k.Q →
    MixesInTwoSteps k.P → MixesInTwoSteps k.Q → oppositeInnerProduct k.P k.Q = 1

/-- **Two-step mixing does not force opposite orthogonality.** On `{−1, 1}²` the kernel
`P(x, y) = (1 + r x₁ y₂)/4` with `0 < r < 1` and its transpose `Q = Pᵀ` are positive, doubly
stochastic and satisfy `P² = Q² = Π`, yet their opposite-direction inner product is `1 + r²`;
at `r = 1/2` it is `5/4 ≠ 1`. -/
theorem result : ¬ claim := by
  intro h
  let sgn : Bool → ℝ := fun b => if b then 1 else -1
  let r : ℝ := 1 / 2
  let P : Bool × Bool → Bool × Bool → ℝ := fun x y => (1 + r * sgn x.1 * sgn y.2) / 4
  let Q : Bool × Bool → Bool × Bool → ℝ := fun x y => P y x
  have hcard : (Fintype.card (Bool × Bool) : ℝ) = 4 := by simp
  have hP : PositiveDoublyStochastic P := by
    refine ⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩
    · rcases x with ⟨_ | _, _ | _⟩ <;> rcases y with ⟨_ | _, _ | _⟩ <;> norm_num [P, sgn, r]
    · rcases x with ⟨_ | _, _ | _⟩ <;>
        simp [P, sgn, r, Fintype.sum_prod_type] <;> norm_num
    · rcases y with ⟨_ | _, _ | _⟩ <;>
        simp [P, sgn, r, Fintype.sum_prod_type] <;> norm_num
  have hQ : PositiveDoublyStochastic Q := by
    refine ⟨fun x y => hP.1 y x, fun x => hP.2.2 x, fun y => hP.2.1 y⟩
  have hPP : MixesInTwoSteps P := by
    intro x z
    rw [hcard]
    rcases x with ⟨_ | _, _ | _⟩ <;> rcases z with ⟨_ | _, _ | _⟩ <;>
      simp [P, sgn, r, Fintype.sum_prod_type] <;> norm_num
  have hQQ : MixesInTwoSteps Q := by
    intro x z
    rw [hcard]
    rcases x with ⟨_ | _, _ | _⟩ <;> rcases z with ⟨_ | _, _ | _⟩ <;>
      simp [Q, P, sgn, r, Fintype.sum_prod_type] <;> norm_num
  have hval : oppositeInnerProduct P Q = 5 / 4 := by
    unfold oppositeInnerProduct
    rw [hcard]
    simp [Q, P, sgn, r, Fintype.sum_prod_type]
    norm_num
  have := h ⟨Bool × Bool, P, Q⟩ hP hQ hPP hQQ
  rw [hval] at this
  norm_num at this

#print axioms result

end D5.S3.Estimation.TimeArrow.TwoStepMixingOppositeProduct
