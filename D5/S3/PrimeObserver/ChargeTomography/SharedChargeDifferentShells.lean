/- GID: D5/S3/PrimeObserver/ChargeTomography/SharedChargeDifferentShells
   generality: G
   mirror-B: D5/B/S3/PrimeObserver/ChargeTomography/SharedChargeDifferentShells
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Multiple observer shells can factor to the same charge readout while retaining different kernels and therefore remaining distinct observers. -/

import Mathlib

/- Library-search audit trail (2026-08-30):
   * Repository searches for shared-charge factorization across observer shells
     and an explicit different-kernel witness found no exact D5 owner.
   * Existing observer refinement modules provide general kernel calculus; this
     owner isolates the typed shell/charge distinction used by the golden route.
   * Pinned Mathlib supplies only elementary function logic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeObserver.ChargeTomography.SharedChargeDifferentShells

universe u v w

/-- A shell reads a common charge when its output admits a decoder back to the
same charge function. -/
def ReadsCharge {X : Type u} {C : Type v} {Y : Type w}
    (shell : X → Y) (decode : Y → C) (charge : X → C) : Prop :=
  decode ∘ shell = charge

/-- Equality under any shell that reads a charge implies equality of that
charge. -/
theorem shell_equality_implies_charge_equality
    {X : Type u} {C : Type v} {Y : Type w}
    {shell : X → Y} {decode : Y → C} {charge : X → C}
    (hReads : ReadsCharge shell decode charge)
    {x y : X} (hShell : shell x = shell y) :
    charge x = charge y := by
  have hPointwise : ∀ z, decode (shell z) = charge z := by
    intro z
    exact congrFun hReads z
  rw [← hPointwise x, ← hPointwise y, hShell]

/-- A family of shells sharing one charge readout has a common lower-bound
kernel given by charge equality. -/
theorem family_shell_equality_implies_charge_equality
    {X : Type u} {C : Type v} {I : Type w}
    {Y : I → Type*}
    (shell : (i : I) → X → Y i)
    (decode : (i : I) → Y i → C)
    (charge : X → C)
    (hReads : ∀ i, ReadsCharge (shell i) (decode i) charge)
    {i : I} {x y : X} (hShell : shell i x = shell i y) :
    charge x = charge y :=
  shell_equality_implies_charge_equality (hReads i) hShell

/-- The identity shell and the charge-only shell read the same charge on pairs. -/
theorem pair_shells_read_same_charge :
    ReadsCharge (fun x : Bool × Bool => x) Prod.fst Prod.fst ∧
      ReadsCharge Prod.fst id Prod.fst := by
  constructor <;> rfl

/-- Sharing a charge does not identify observer shells: one shell can retain a
hidden coordinate that another shell discards. -/
theorem shared_charge_does_not_force_same_kernel :
    (∀ x y : Bool × Bool, x = y → Prod.fst x = Prod.fst y) ∧
      (∃ x y : Bool × Bool, Prod.fst x = Prod.fst y ∧ x ≠ y) := by
  constructor
  · intro x y h
    exact congrArg Prod.fst h
  · exact ⟨(false, false), (false, true), rfl, by decide⟩

/-- In the concrete witness, the fine shell is faithful and the charge-only
shell is not. -/
theorem fine_and_charge_shells_have_different_faithfulness :
    Function.Injective (fun x : Bool × Bool => x) ∧
      ¬ Function.Injective (fun x : Bool × Bool => x.1) := by
  constructor
  · exact Function.injective_id
  · intro hInjective
    have hEq : (false, false) = (false, true) := hInjective rfl
    decide at hEq

/-- The carrier and hypotheses are inhabited by explicit distinct shells. -/
example :
    ReadsCharge (fun x : Bool × Bool => x) Prod.fst Prod.fst := by
  rfl

#print axioms shell_equality_implies_charge_equality
#print axioms family_shell_equality_implies_charge_equality
#print axioms pair_shells_read_same_charge
#print axioms shared_charge_does_not_force_same_kernel
#print axioms fine_and_charge_shells_have_different_faithfulness

end D5.S3.PrimeObserver.ChargeTomography.SharedChargeDifferentShells
