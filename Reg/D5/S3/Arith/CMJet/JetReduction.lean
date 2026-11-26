import D5.S3.Arith.CMJet.JetReduction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Observation of the section jet as the column varies. -/

noncomputable section

namespace Reg.D5.S3.Arith.CMJet.JetReduction

open LeanInformationAudit
open _root_.D5.S3.Arith.CMJet.ActualRestricted
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

abbrev readoutSignature : Signature :=
  signature (Σ _ : ℕ, Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun phn => ZMod phn.1)

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ phn j => (jet phn.2.1 phn.2.2 j : ZMod phn.1)) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ (p h n j : ℕ), R.readout () ⟨p, h, n⟩ j =
    evalJet (ZMod p) (extendedIter (ZMod p) (h : ℤ) n (sectionElement (ZMod p) j))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 3 0 0 0
  rw [← jet_reduce_cast, jet_zero_order] at hbad
  simpa [rejected, realize] using hbad

def family : Registration arena (type_of% @jet_reduce_cast) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@jet_reduce_cast, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    change ∃ (phn : Σ _ : ℕ, Σ _ : ℕ, ℕ) (l r : ℕ),
      (jet phn.2.1 phn.2.2 l : ZMod phn.1) ≠ (jet phn.2.1 phn.2.2 r : ZMod phn.1)
    refine ⟨⟨3, 0, 0⟩, 0, 1, ?_⟩
    simp [jet_zero_order]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@jet_reduce_cast) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.CMJet.JetReduction.unit
  realizationName := `Reg.D5.S3.Arith.CMJet.JetReduction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature
    (fun _ phn j => (jet phn.2.1 phn.2.2 j : ZMod phn.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.CMJet.JetReduction
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.CMJet.JetReduction
