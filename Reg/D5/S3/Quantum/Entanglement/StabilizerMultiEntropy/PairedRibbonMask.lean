import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonMask
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonMask
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonMask
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
open PairedSpectralTrace PairedBellSign LiteralPairedRibbon
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev ChartParams := Σ q : ℕ, Σ _ : (Fin (q+1) → Bool), Sites q
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ChartParams (fun p => Sites p.1) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p j => ribbonAmplitude p.2.1 p.2.2 j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q:ℕ) (u:Fin (q+1)→Bool),
    (∀ l j : Sites q,
      R.readout () ⟨q,u,l⟩ j =
        ∏ i, localAmplitude (u i) (siteCoords q l i) (siteCoords q j i)) ∧
    (∀ (v:Bool) (l j:Fin 4),
      localAmplitude v l j = sign (tau v*firstBit l*secondBit l) *
        (quantumBell l j : ℝ) / Real.sqrt 2)

private def u0 : Fin 1→Bool := fun _=>false
private def label0 : Sites 0 := (0:Fin 4)
private def coord0 : Sites 0 := (0:Fin 4)
private def coord1 : Sites 0 := (1:Fin 4)

private theorem oneNonzero : localAmplitude false 0 0 ≠ 0 := by
  rw [(literal_tensor_transport u0).2]
  have p : quantumBell 0 0=1 := by decide
  rw [p]
  have h : tau false = 0 := rfl
  rw [h]
  simp [sign_zero,show Real.sqrt 2 ≠ 0 by positivity]

private theorem oneZero : localAmplitude false 0 1 = 0 := by
  rw [(literal_tensor_transport u0).2]
  have p : quantumBell 0 1=0 := by decide
  simp [p]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hv := (h 0 u0).1 label0 coord1
  rw [Fin.prod_univ_one] at hv
  change (2:ℝ)=localAmplitude false 0 1 at hv
  rw [oneZero] at hv
  norm_num at hv

def family : Registration arena (type_of% @literal_tensor_transport) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ u=>literal_tensor_transport u, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨0,u0,label0⟩,coord0,coord1,?_⟩
    change ribbonAmplitude u0 label0 coord0 ≠ ribbonAmplitude u0 label0 coord1
    rw [(literal_tensor_transport u0).1, (literal_tensor_transport u0).1,
      Fin.prod_univ_one,Fin.prod_univ_one]
    change localAmplitude false 0 0 ≠ localAmplitude false 0 1
    rw [oneZero]
    exact oneNonzero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@literal_tensor_transport) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonMask.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonMask.family
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
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonMask
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","fn","arg","body","body","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonMask
