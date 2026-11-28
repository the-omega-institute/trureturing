import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
open PairedSpectralTrace LiteralPairedRibbon
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev ChartParams := Σ q : ℕ, Fin (q+1) → Bool
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ChartParams (fun p => Sites p.1 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p h => flaggedValue p.2 h) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (u : Fin (q+1) → Bool),
    (∀ h : Sites q → ℝ, (∀ j, |h j| ≤ 1) → R.readout () ⟨q,u⟩ h ≤ 5/4) ∧
    (∃ h : Sites q → ℝ, (∀ j, h j = 1 ∨ h j = -1) ∧ flaggedValue u h = 5/4) ∧
    (∀ (b : Bool) (f : (Fin (q+1) → K) → ℝ), (∀ x, |f x| ≤ 1) →
        flaggedValue u (fun j => f (bank q b j)) = 1) ∧
    (∀ (polarity : K) (a b : Fin (q+1) → K),
        flaggedValue u (fun j => sign polarity * recordPhase q a b j) = 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hv := (h 0 (fun _=>false)).1 (fun _ => 0) (by simp)
  change (2:ℝ) ≤ 5/4 at hv
  norm_num at hv

def family : Registration arena (type_of% @actual_joint_bit_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ u=>actual_joint_bit_gap u, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    let u : Fin 1 → Bool := fun _=>false
    obtain ⟨h,_,hv⟩ := (actual_joint_bit_gap u).2.1
    refine ⟨⟨0,u⟩,h,(fun _=>0),?_⟩
    change flaggedValue u h≠flaggedValue u (fun _=>0)
    rw [hv]
    have h0 := (actual_joint_bit_gap u).2.2.1 false (fun _ => 0) (by simp)
    change flaggedValue u (fun _=>0)=1 at h0
    rw [h0]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@actual_joint_bit_gap) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","fn","arg","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit
