import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.Auric.EqualBlockProjection
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the attained coordinate-record entropy gain. -/

namespace Reg.D5.S3.Quantum.Measurement.Auric.EqualBlockProjection

open _root_.D5.S3.Quantum.Measurement.Auric.EqualBlockEffects (entropyBound)
open _root_.D5.S3.Quantum.Measurement.Auric.EqualBlockProjection
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
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (c : ι → Fin 3) (m r : ℕ) (_ : 0 < m) (hr : 0 < r)
    (_ : ∀ j, Fintype.card {i // c i = j} = m) (_ : r ≤ 3 * m),
    R.readout () () {s : ℝ | ∃ P : Matrix ι ι ℂ, ∃ hP : FlatProjection r P,
      gain c (flatState hr hP) = s}
      (entropyBound (@decide (3 * m - r < r) (Classical.propDecidable _))
        m (min r (3 * m - r)) / r)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (ι := ULift.{u} (Fin 3)) (fun i => i.down) 1 1 (by decide) (by decide)
    (by intro j; fin_cases j <;> decide) (by decide)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), {0}, ∅, ?_⟩
  intro h
  have he : IsGreatest ({0} : Set ℝ) 0 = IsGreatest (∅ : Set ℝ) 0 := congrFun h 0
  exact (Eq.mp he (by simp [IsGreatest, upperBounds])).1

def sourceRegistration : Registration arena.{u} (type_of% @isGreatest_flat_record_gain.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isGreatest_flat_record_gain.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@isGreatest_flat_record_gain.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Measurement.Auric.EqualBlockProjection.isGreatest_flat_record_gain.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.EqualBlockProjection.sourceRegistration
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
    owner := `D5.S3.Quantum.Measurement.Auric.EqualBlockProjection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S3.Quantum.Measurement.Auric.EqualBlockProjection
