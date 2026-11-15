import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
import Reg.Support.SingleDependentReadout

/-! The original double addressed operations are observed on their full binary-label domains. -/

namespace Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
open QuantumAlg.WireAddress
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

namespace Flip
abbrev Params := Σ n : Nat, Fin n
abbrev signature := Reg.Support.SingleDependentReadout.signature Params
  (fun p => Fin (2 ^ p.1)) (fun p => Fin (2 ^ p.1))
def actual : Realization signature :=
  realize signature (fun _ p x => flipBit p.2 (flipBit p.2 x)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {n : Nat} (target : Fin n) (x : Fin (2 ^ n)),
    R.readout () ⟨n, target⟩ x = x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h (0 : Fin 1) (1 : Fin (2 ^ 1))
  change (0 : Fin (2 ^ 1)) = 1 at h1
  exact (by decide : (0 : Fin (2 ^ 1)) ≠ 1) h1
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  change flipBit (0 : Fin 1) (flipBit 0 (0 : Fin (2 ^ 1))) ≠ flipBit 0 (flipBit 0 1)
  simp only [flipBit_flipBit]
  decide
def source_registration : Registration arena (type_of% @flipBit_flipBit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@flipBit_flipBit, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@flipBit_flipBit) (Realization signature) Unit Unit := {
  unitName := `QuantumAlg.WireAddress.flipBit_flipBit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.Flip.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => flipBit p.2 (flipBit p.2 x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Flip

namespace Cnot
abbrev Params := Σ n : Nat, Σ control : Fin n, {target : Fin n // control ≠ target}
abbrev signature := Reg.Support.SingleDependentReadout.signature Params
  (fun p => Fin (2 ^ p.1)) (fun p => Fin (2 ^ p.1))
def actual : Realization signature :=
  realize signature
    (fun _ p x => cnotMap p.2.1 p.2.2.1 (cnotMap p.2.1 p.2.2.1 x)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {n : Nat} {control target : Fin n} (hct : control ≠ target) (x : Fin (2 ^ n)),
    R.readout () ⟨n, control, target, hct⟩ x = x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h (n := 2) (control := 0) (target := 1) (by decide) (1 : Fin (2 ^ 2))
  change (0 : Fin (2 ^ 2)) = 1 at h1
  exact (by decide : (0 : Fin (2 ^ 2)) ≠ 1) h1
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨2, 0, 1, by decide⟩, 0, 1, ?_⟩
  change cnotMap (0 : Fin 2) 1 (cnotMap 0 1 (0 : Fin (2 ^ 2))) ≠ cnotMap 0 1 (cnotMap 0 1 1)
  simp only [cnotMap_cnotMap (by decide : (0 : Fin 2) ≠ 1)]
  decide
def source_registration : Registration arena (type_of% @cnotMap_cnotMap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cnotMap_cnotMap, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cnotMap_cnotMap) (Realization signature) Unit Unit := {
  unitName := `QuantumAlg.WireAddress.cnotMap_cnotMap.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.Cnot.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p x => cnotMap p.2.1 p.2.2.1 (cnotMap p.2.1 p.2.2.1 x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Cnot

namespace Toffoli
abbrev Params := Σ n : Nat, Σ a : Fin n, Σ b : Fin n,
  {target : Fin n // a ≠ target ∧ b ≠ target}
abbrev signature := Reg.Support.SingleDependentReadout.signature Params
  (fun p => Fin (2 ^ p.1)) (fun p => Fin (2 ^ p.1))
def actual : Realization signature :=
  realize signature (fun _ p x => toffoliMap p.2.1 p.2.2.1 p.2.2.2.1
    (toffoliMap p.2.1 p.2.2.1 p.2.2.2.1 x)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {n : Nat} {controlA controlB target : Fin n}
    (ha : controlA ≠ target) (hb : controlB ≠ target) (x : Fin (2 ^ n)),
    R.readout () ⟨n, controlA, controlB, target, ha, hb⟩ x = x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h (n := 2) (controlA := 0) (controlB := 0) (target := 1)
    (by decide) (by decide) (1 : Fin (2 ^ 2))
  change (0 : Fin (2 ^ 2)) = 1 at h1
  exact (by decide : (0 : Fin (2 ^ 2)) ≠ 1) h1
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨2, 0, 0, 1, by decide, by decide⟩, 0, 1, ?_⟩
  change toffoliMap (0 : Fin 2) 0 1 (toffoliMap 0 0 1 (0 : Fin (2 ^ 2))) ≠
    toffoliMap 0 0 1 (toffoliMap 0 0 1 1)
  simp only [toffoliMap_toffoliMap (by decide : (0 : Fin 2) ≠ 1) (by decide : (0 : Fin 2) ≠ 1)]
  decide
def source_registration : Registration arena (type_of% @toffoliMap_toffoliMap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@toffoliMap_toffoliMap, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@toffoliMap_toffoliMap) (Realization signature) Unit Unit := {
  unitName := `QuantumAlg.WireAddress.toffoliMap_toffoliMap.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.Toffoli.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => toffoliMap p.2.1 p.2.2.1 p.2.2.2.1
    (toffoliMap p.2.1 p.2.2.1 p.2.2.2.1 x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Toffoli

end
end Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
