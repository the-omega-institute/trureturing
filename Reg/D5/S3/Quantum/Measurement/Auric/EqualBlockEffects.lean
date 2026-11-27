import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.Auric.EqualBlockEffects
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the attained spectral entropy maximum. -/

namespace Reg.D5.S3.Quantum.Measurement.Auric.EqualBlockEffects

open _root_.D5.S3.Quantum.Measurement.Auric.EqualBlockEffects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

set_option autoImplicit false

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Set ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (c : Bool) (m : ℕ)
    (_ : 3 * (Fintype.card n - m) ≤ Fintype.card n),
    R.readout () () {s : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m A,
      effectEntropy c A hA.1 = s} (entropyBound c m (Fintype.card n))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) false 1 (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), {0}, ∅, ?_⟩
  intro h
  have he : IsGreatest ({0} : Set ℝ) 0 = IsGreatest (∅ : Set ℝ) 0 := congrFun h 0
  exact (Eq.mp he (by simp [IsGreatest, upperBounds])).1

def sourceRegistration : Registration arena.{u} (type_of% @isGreatest_effectEntropy.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isGreatest_effectEntropy.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@isGreatest_effectEntropy.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Measurement.Auric.EqualBlockEffects.isGreatest_effectEntropy.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.EqualBlockEffects.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.EqualBlockEffects
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S3.Quantum.Measurement.Auric.EqualBlockEffects
