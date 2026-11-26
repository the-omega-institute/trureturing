import D5.S3.Arith.CMJet.Basic
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Mathlib.Algebra.Ring.ULift

/-! The factorial in the highest column is a readout independent of the coefficient ring. -/

noncomputable section
universe u

namespace Reg.D5.S3.Arith.CMJet.Basic

open LeanInformationAudit Polynomial
open scoped Polynomial
open _root_.D5.S3.Arith.CMJet
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

abbrev readoutSignature : Signature :=
  signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ _ s => (2 * s + 1).factorial) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {A : Type u} [CommRing A] (s : ℕ),
    atO (iter (2 * s + 1) (poly (X ^ (2 * s + 1) : A[X]))) =
      (R.readout () () s : A)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := h (A := ULift.{u} ℤ) 0
  rw [odd_top_jet] at hbad
  simp [rejected, realize] at hbad

def family : Registration arena.{u} (type_of% @odd_top_jet.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@odd_top_jet.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (1 : ℕ) ≠ 6
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@odd_top_jet.{u}) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.CMJet.Basic.unit
  realizationName := `Reg.D5.S3.Arith.CMJet.Basic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature (fun _ _ s => (2 * s + 1).factorial) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.CMJet.Basic
    definition := none
    coordinates :=  #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.CMJet.Basic
