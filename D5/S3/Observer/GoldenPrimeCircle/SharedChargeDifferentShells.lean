/- GID: D5/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells
   generality: G
   mirror-B: D5/B/S3/Observer/GoldenPrimeCircle/SharedChargeDifferentShells
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct observer shells may factor through the same charge readout while retaining different residual information. -/

import Mathlib

/-!
The shared charge is a common quotient of observer shells. Equality of that
quotient does not identify the observers themselves. The concrete Boolean
model supplies a strict information-refinement witness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenPrimeCircle.SharedChargeDifferentShells

universe u v w z

/-- A shell readout factors through a prescribed charge observation. -/
def CarriesCharge {X : Type u} {Y : Type v} {C : Type w}
    (shell : X → Y) (chargeOnShell : Y → C) (charge : X → C) : Prop :=
  ∀ x, chargeOnShell (shell x) = charge x

/-- Two shells carrying the same charge agree after their charge projections. -/
theorem common_charge_agreement
    {X : Type u} {Y₁ : Type v} {Y₂ : Type w} {C : Type z}
    {shell₁ : X → Y₁} {shell₂ : X → Y₂}
    {charge₁ : Y₁ → C} {charge₂ : Y₂ → C} {charge : X → C}
    (h₁ : CarriesCharge shell₁ charge₁ charge)
    (h₂ : CarriesCharge shell₂ charge₂ charge) (x : X) :
    charge₁ (shell₁ x) = charge₂ (shell₂ x) := by
  rw [h₁ x, h₂ x]

/-- A coarse shell reading only the common charge. -/
def coarseShell (x : Bool × Bool) : Bool := x.1

/-- A finer shell retaining both charge and residual state. -/
def fineShell (x : Bool × Bool) : Bool × Bool := x

/-- Charge projection from the fine shell. -/
def fineCharge (x : Bool × Bool) : Bool := x.1

/-- Both concrete shells carry the same charge. -/
theorem concrete_shells_carry_same_charge :
    CarriesCharge coarseShell id Prod.fst ∧
      CarriesCharge fineShell fineCharge Prod.fst := by
  constructor <;> intro x <;> rfl

/-- One collision of the coarse shell is separated by the fine shell. -/
theorem same_charge_different_observer_witness :
    coarseShell (true, false) = coarseShell (true, true) ∧
      fineShell (true, false) ≠ fineShell (true, true) := by
  decide

/-- Shared charge therefore does not force equal observer kernels. -/
theorem shared_charge_does_not_force_same_resolution :
    ∃ x y : Bool × Bool,
      coarseShell x = coarseShell y ∧ fineShell x ≠ fineShell y := by
  exact ⟨(true, false), (true, true), same_charge_different_observer_witness⟩

#print axioms common_charge_agreement
#print axioms concrete_shells_carry_same_charge
#print axioms same_charge_different_observer_witness
#print axioms shared_charge_does_not_force_same_resolution

end D5.S3.Observer.GoldenPrimeCircle.SharedChargeDifferentShells
