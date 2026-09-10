/- GID: D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A rational coupling of two finite readouts lifts to the original carriers with every original marginal and every readout-pair expectation preserved, including null fibers. -/

import D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw

/-!
This is the finite rational disaggregation principle. It is classical, not a
new coupling theorem. The existing response-law and pushforward semantics are
retained. No positive-mass assumption is imposed: compatibility forces a coarse
cell to vanish whenever either of its marginal fibers has zero mass.

The consumer is UnknownCouplingFairMediation: a two-cell optimal transport plan
is lifted to the original mediator states before asserting causal attainment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.FiniteCouplingPushforwardLift

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

private theorem source_mass_zero (law : FiniteResponseLaw X) (f : X → A) (x : X)
    (zero : (pushforwardResponseLaw law f).mass (f x) = 0) : law.mass x = 0 := by
  classical
  have bound : law.mass x ≤ (pushforwardResponseLaw law f).mass (f x) := by
    change law.mass x ≤ ∑ t, if f t = f x then law.mass t else 0
    have h := Finset.single_le_sum (s := Finset.univ) (a := x)
      (f := fun t => if f t = f x then law.mass t else 0)
      (fun t _ => by
        split_ifs
        · exact law.nonnegative t
        · exact le_rfl)
      (Finset.mem_univ x)
    exact (if_pos rfl).symm.trans_le h
  rw [zero] at bound
  exact le_antisymm bound (law.nonnegative x)

private theorem cell_zero_left (joint : FiniteResponseLaw (A × B)) (a : A) (b : B)
    (zero : leftResponseMarginal joint.mass a = 0) : joint.mass (a, b) = 0 := by
  classical
  have bound : joint.mass (a, b) ≤ leftResponseMarginal joint.mass a :=
    Finset.single_le_sum (fun j _ => joint.nonnegative (a, j)) (Finset.mem_univ b)
  rw [zero] at bound
  exact le_antisymm bound (joint.nonnegative (a, b))

private theorem cell_zero_right (joint : FiniteResponseLaw (A × B)) (a : A) (b : B)
    (zero : rightResponseMarginal joint.mass b = 0) : joint.mass (a, b) = 0 := by
  classical
  have bound : joint.mass (a, b) ≤ rightResponseMarginal joint.mass b :=
    Finset.single_le_sum (fun i _ => joint.nonnegative (i, b)) (Finset.mem_univ a)
  rw [zero] at bound
  exact le_antisymm bound (joint.nonnegative (a, b))

private theorem sum_fiber_div (law : FiniteResponseLaw X) (f : X → A) (value : A → ℚ)
    (vanishes : ∀ a, (pushforwardResponseLaw law f).mass a = 0 → value a = 0) :
    (∑ x, (value (f x) / (pushforwardResponseLaw law f).mass (f x)) * law.mass x) =
      ∑ a, value a := by
  calc
    _ = ∑ a, (value a / (pushforwardResponseLaw law f).mass a) *
        (pushforwardResponseLaw law f).mass a :=
      (pushforward_linearObjective law f
        (fun a => value a / (pushforwardResponseLaw law f).mass a)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases zero : (pushforwardResponseLaw law f).mass a = 0
      · simp only [zero, vanishes a zero, zero_div, zero_mul]
      · exact div_mul_cancel₀ _ zero

/-- Explicit original-carrier weights from a compatible coarse coupling.
Division is total in Q; the theorems below separately justify all null fibers. -/
noncomputable def liftedCouplingMass (left : FiniteResponseLaw X) (right : FiniteResponseLaw Y)
    (f : X → A) (g : Y → B) (joint : FiniteResponseLaw (A × B)) (pair : X × Y) : ℚ :=
  joint.mass (f pair.1, g pair.2) *
    (left.mass pair.1 / (pushforwardResponseLaw left f).mass (f pair.1)) *
    (right.mass pair.2 / (pushforwardResponseLaw right g).mass (g pair.2))

private theorem lifted_left (left : FiniteResponseLaw X) (right : FiniteResponseLaw Y)
    (f : X → A) (g : Y → B) (joint : FiniteResponseLaw (A × B))
    (hl : ∀ a, leftResponseMarginal joint.mass a = (pushforwardResponseLaw left f).mass a)
    (hr : ∀ b, rightResponseMarginal joint.mass b = (pushforwardResponseLaw right g).mass b)
    (x : X) : leftResponseMarginal (liftedCouplingMass left right f g joint) x = left.mass x := by
  have cancel := sum_fiber_div right g (fun b => joint.mass (f x, b))
    (fun b zero => cell_zero_right joint (f x) b ((hr b).trans zero))
  calc
    _ = (left.mass x / (pushforwardResponseLaw left f).mass (f x)) *
        ∑ y, (joint.mass (f x, g y) / (pushforwardResponseLaw right g).mass (g y)) * right.mass y := by
      unfold leftResponseMarginal liftedCouplingMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = (left.mass x / (pushforwardResponseLaw left f).mass (f x)) *
        leftResponseMarginal joint.mass (f x) := by rw [cancel, leftResponseMarginal]
    _ = left.mass x := by
      rw [hl]
      by_cases zero : (pushforwardResponseLaw left f).mass (f x) = 0
      · simp only [zero, source_mass_zero left f x zero, zero_div, zero_mul]
      · exact div_mul_cancel₀ _ zero

private theorem lifted_right (left : FiniteResponseLaw X) (right : FiniteResponseLaw Y)
    (f : X → A) (g : Y → B) (joint : FiniteResponseLaw (A × B))
    (hl : ∀ a, leftResponseMarginal joint.mass a = (pushforwardResponseLaw left f).mass a)
    (hr : ∀ b, rightResponseMarginal joint.mass b = (pushforwardResponseLaw right g).mass b)
    (y : Y) : rightResponseMarginal (liftedCouplingMass left right f g joint) y = right.mass y := by
  have cancel := sum_fiber_div left f (fun a => joint.mass (a, g y))
    (fun a zero => cell_zero_left joint a (g y) ((hl a).trans zero))
  calc
    _ = (right.mass y / (pushforwardResponseLaw right g).mass (g y)) *
        ∑ x, (joint.mass (f x, g y) / (pushforwardResponseLaw left f).mass (f x)) * left.mass x := by
      unfold rightResponseMarginal liftedCouplingMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (right.mass y / (pushforwardResponseLaw right g).mass (g y)) *
        rightResponseMarginal joint.mass (g y) := by rw [cancel, rightResponseMarginal]
    _ = right.mass y := by
      rw [hr]
      by_cases zero : (pushforwardResponseLaw right g).mass (g y) = 0
      · simp only [zero, source_mass_zero right g y zero, zero_div, zero_mul]
      · exact div_mul_cancel₀ _ zero

/-- Normalize the explicit lift using the original laws, without changing either
original marginal or introducing a new law semantics. -/
noncomputable def liftCoarseCoupling (left : FiniteResponseLaw X) (right : FiniteResponseLaw Y)
    (f : X → A) (g : Y → B) (joint : FiniteResponseLaw (A × B))
    (hl : ∀ a, leftResponseMarginal joint.mass a = (pushforwardResponseLaw left f).mass a)
    (hr : ∀ b, rightResponseMarginal joint.mass b = (pushforwardResponseLaw right g).mass b) :
    FiniteResponseLaw (X × Y) where
  mass := liftedCouplingMass left right f g joint
  nonnegative := fun pair => mul_nonneg
    (mul_nonneg (joint.nonnegative _)
      (div_nonneg (left.nonnegative _) ((pushforwardResponseLaw left f).nonnegative _)))
    (div_nonneg (right.nonnegative _) ((pushforwardResponseLaw right g).nonnegative _))
  total := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ x, left.mass x := by
        apply Finset.sum_congr rfl
        intro x _
        exact lifted_left left right f g joint hl hr x
      _ = 1 := left.total

/-- Every original marginal is retained, not merely the two coarse readouts. -/
theorem liftCoarseCoupling_marginals (left : FiniteResponseLaw X) (right : FiniteResponseLaw Y)
    (f : X → A) (g : Y → B) (joint : FiniteResponseLaw (A × B))
    (hl : ∀ a, leftResponseMarginal joint.mass a = (pushforwardResponseLaw left f).mass a)
    (hr : ∀ b, rightResponseMarginal joint.mass b = (pushforwardResponseLaw right g).mass b) :
    (∀ x, leftResponseMarginal (liftCoarseCoupling left right f g joint hl hr).mass x = left.mass x) ∧
    (∀ y, rightResponseMarginal (liftCoarseCoupling left right f g joint hl hr).mass y = right.mass y) :=
  ⟨lifted_left left right f g joint hl hr, lifted_right left right f g joint hl hr⟩

/-- The same lifted law preserves every query of the paired readouts. This
includes the crossing event used by complete mediation and all coarse cells. -/
theorem liftCoarseCoupling_expectation (left : FiniteResponseLaw X) (right : FiniteResponseLaw Y)
    (f : X → A) (g : Y → B) (joint : FiniteResponseLaw (A × B))
    (hl : ∀ a, leftResponseMarginal joint.mass a = (pushforwardResponseLaw left f).mass a)
    (hr : ∀ b, rightResponseMarginal joint.mass b = (pushforwardResponseLaw right g).mass b)
    (query : A × B → ℚ) :
    linearObjective (fun pair => query (f pair.1, g pair.2))
        (liftCoarseCoupling left right f g joint hl hr).mass =
      linearObjective query joint.mass := by
  have inner (x : X) := sum_fiber_div right g (fun b => query (f x, b) * joint.mass (f x, b))
    (fun b zero => by rw [cell_zero_right joint (f x) b ((hr b).trans zero), mul_zero])
  have outer := sum_fiber_div left f (fun a => ∑ b, query (a, b) * joint.mass (a, b))
    (fun a zero => by
      apply Finset.sum_eq_zero
      intro b _
      rw [cell_zero_left joint a b ((hl a).trans zero), mul_zero])
  change (∑ pair, query (f pair.1, g pair.2) * liftedCouplingMass left right f g joint pair) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x, (left.mass x / (pushforwardResponseLaw left f).mass (f x)) *
        ∑ y, ((query (f x, g y) * joint.mass (f x, g y)) /
          (pushforwardResponseLaw right g).mass (g y)) * right.mass y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      unfold liftedCouplingMass
      ring
    _ = ∑ x, ((∑ b, query (f x, b) * joint.mass (f x, b)) /
        (pushforwardResponseLaw left f).mass (f x)) * left.mass x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [inner x]
      ring
    _ = ∑ a, ∑ b, query (a, b) * joint.mass (a, b) := outer
    _ = linearObjective query joint.mass := by
      rw [linearObjective, Fintype.sum_prod_type]

#print axioms liftCoarseCoupling_marginals
#print axioms liftCoarseCoupling_expectation

end D5.S3.ConceptDynamics.CausalMoments.FiniteCouplingPushforwardLift
