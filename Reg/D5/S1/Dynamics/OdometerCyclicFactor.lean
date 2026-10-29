import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.OdometerCyclicFactor
import Reg.Support.DependentFamily

/-! Full-telescope reconstruction readout for the canonical odometer factor. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.OdometerCyclicFactor

namespace Reg.D5.S1.Dynamics.OdometerCyclicFactor

noncomputable section
universe u

structure Parameters where
  p : ℕ
  prime : p.Prime
  A : Type u
  Φ : @PadicInt p ⟨prime⟩ → ℤ → A
  x : @PadicInt p ⟨prime⟩
  n : ℤ

abbrev signature : Signature where
  Params := Parameters.{u}
  State P := P.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def equalityReadout (P : Parameters.{u}) (a : P.A) : Bool := by
  classical
  exact decide (P.Φ P.x P.n = a)

def actual : Realization signature.{u} :=
  realize signature (fun _ P a => equalityReadout P a) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Only the final reconstruction equality is varied; the prime, topology,
continuity, equivariance, quotient and complete two-sided telescope are kept. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : ℕ) [Fact p.Prime]
    {A : Type u} [TopologicalSpace A] [DiscreteTopology A]
    (Φ : ℤ_[p] → ℤ → A) (_hΦ : Continuous Φ)
    (_hshift : ∀ (x : ℤ_[p]) (n : ℤ), Φ (x + 1) n = Φ x (n + 1)),
    ∃ (N : ℕ) (w : ZMod (p ^ N) → A), ∀ (x : ℤ_[p]) (n : ℤ),
      R.readout () ⟨p, Fact.out, A, Φ, x, n⟩
        (w (PadicInt.toZModPow N x + (n : ZMod (p ^ N)))) = true

private theorem actual_law : arena.{u}.Law actual := by
  simpa only [arena, actual, realize, equalityReadout, decide_eq_true_eq] using
    (@exists_cyclic_factor_of_shift_equivariant.{u})

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨N, w, hw⟩ := @h 2 inferInstance (ULift.{u} Unit) inferInstance inferInstance
    (fun _ _ => ⟨()⟩) continuous_const (by intros; rfl)
  have hf := hw 0 0
  change false = true at hf
  contradiction

def family : Registration arena.{u}
    (type_of% (@exists_cyclic_factor_of_shift_equivariant.{u})) where
  actual := actual
  bridge := by simp only [arena, actual, realize, equalityReadout, decide_eq_true_eq]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let P : Parameters.{u} := ⟨2, by decide, ULift.{u} Bool, fun _ _ => ⟨false⟩, 0, 0⟩
    refine ⟨P, ULift.up false, ULift.up true, ?_⟩
    simp [actual, realize, equalityReadout, P]
    intro h
    cases h

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_cyclic_factor_of_shift_equivariant.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.OdometerCyclicFactor.cyclicFactorUnit
  realizationName := `Reg.D5.S1.Dynamics.OdometerCyclicFactor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ P a => equalityReadout P a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.OdometerCyclicFactor
    definition := none
    coordinates := #[0, 2, 5, 10, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end
end Reg.D5.S1.Dynamics.OdometerCyclicFactor
