import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
import Reg.Support.SingleDependentReadout
import Reg.Support.UniverseSingleReadout

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

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.LittleEndianIndex
abbrev Params : Type _ := Σ' x0 : (Nat), PUnit.{1}
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Params
  (fun p => let x0 := p.1; (Fin x0)) (fun p => let x0 := p.1; (Fin x0))
def actual : Realization signature :=
  realize signature (fun _ p x => let x0 := p.1; let x1 := x; (@QuantumAlg.WireAddress.bitIndex x0 (@QuantumAlg.WireAddress.littleEndianWire x0 x1))) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (x0 : (Nat)) (x1 : (Fin x0)), R.readout () ⟨x0, PUnit.unit⟩ x1 = (x1)
def source_bridge : (type_of% @QuantumAlg.WireAddress.bitIndex_littleEndianWire) ↔ arena.Law actual := Iff.rfl
def actual_positive : arena.Law actual := @QuantumAlg.WireAddress.bitIndex_littleEndianWire
def rejected : Realization signature :=
  realize signature (fun _ p x => ⟨0, by have hx := x.isLt; omega⟩) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 (1 : Fin 2)
  change (0 : Fin 2) = 1 at hh
  exact (by decide : (0 : Fin 2) ≠ 1) hh
def source_registration : Registration arena (type_of% @QuantumAlg.WireAddress.bitIndex_littleEndianWire) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨2, PUnit.unit⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
    change QuantumAlg.WireAddress.bitIndex (QuantumAlg.WireAddress.littleEndianWire (0 : Fin 2)) ≠
      QuantumAlg.WireAddress.bitIndex (QuantumAlg.WireAddress.littleEndianWire (1 : Fin 2))
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumAlg.WireAddress.bitIndex_littleEndianWire) (Realization signature) Unit Unit := {
  unitName := `QuantumAlg.WireAddress.bitIndex_littleEndianWire.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.LittleEndianIndex.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => let x0 := p.1; let x1 := x; (@QuantumAlg.WireAddress.bitIndex x0 (@QuantumAlg.WireAddress.littleEndianWire x0 x1))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.LittleEndianIndex

namespace Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.FlipBit
abbrev Params : Type _ := Σ' x0 : (Nat), Σ' x1 : (Fin x0), Σ' x2 : (Fin x0), PUnit.{1}
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Params
  (fun p => let x0 := p.1; let x1 := p.2.1; let x2 := p.2.2.1; (Fin
  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0))) (fun p => let x0 := p.1; let x1 := p.2.1; let x2 := p.2.2.1; (Bool))
def actual : Realization signature :=
  realize signature (fun _ p x => let x0 := p.1; let x1 := p.2.1; let x2 := p.2.2.1; let x3 := x; ((@Fin.val
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0)
      (@QuantumAlg.WireAddress.flipBit x0 x1 x3)).testBit
  (@Fin.val x0 (@QuantumAlg.WireAddress.bitIndex x0 x2)))) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (x0 : (Nat)) (x1 : (Fin x0)) (x2 : (Fin x0)) (x3 : (Fin
  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0))), R.readout () ⟨x0, x1, x2, PUnit.unit⟩ x3 = (((@Fin.val
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0)
          x3).testBit
      (@Fin.val x0 (@QuantumAlg.WireAddress.bitIndex x0 x2))).xor
  (@Decidable.decide (@Eq (Fin x0) x1 x2) (instDecidableEqFin x0 x1 x2)))
def source_bridge : (type_of% @QuantumAlg.WireAddress.bit_flipBit) ↔ arena.Law actual := Iff.rfl
def actual_positive : arena.Law actual := @QuantumAlg.WireAddress.bit_flipBit
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (0 : Fin 1) (0 : Fin 1) (0 : Fin (2 ^ 1))
  change false = true at hh
  cases hh
def source_registration : Registration arena (type_of% @QuantumAlg.WireAddress.bit_flipBit) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨1, 0, 0, PUnit.unit⟩, (0 : Fin (2 ^ 1)), (1 : Fin (2 ^ 1)), ?_⟩
    change (QuantumAlg.WireAddress.flipBit (0 : Fin 1) (0 : Fin (2 ^ 1))).val.testBit 0 ≠
      (QuantumAlg.WireAddress.flipBit (0 : Fin 1) (1 : Fin (2 ^ 1))).val.testBit 0
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumAlg.WireAddress.bit_flipBit) (Realization signature) Unit Unit := {
  unitName := `QuantumAlg.WireAddress.bit_flipBit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.FlipBit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => let x0 := p.1; let x1 := p.2.1; let x2 := p.2.2.1; let x3 := x; ((@Fin.val
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0)
      (@QuantumAlg.WireAddress.flipBit x0 x1 x3)).testBit
  (@Fin.val x0 (@QuantumAlg.WireAddress.bitIndex x0 x2)))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.FlipBit

namespace Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.FlipBitOther
abbrev Params : Type _ := Σ' x0 : (Nat), Σ' x1 : (Fin x0), Σ' x2 : (Fin x0), Σ' x3 : (@Ne (Fin x0) x1 x2), PUnit.{1}
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Params
  (fun p => let x0 := p.1; let x1 := p.2.1; let x2 := p.2.2.1; let x3 := p.2.2.2.1; (Fin
  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0))) (fun p => let x0 := p.1; let x1 := p.2.1; let x2 := p.2.2.1; let x3 := p.2.2.2.1; (Bool))
def actual : Realization signature :=
  realize signature (fun _ p x => let x0 := p.1; let x1 := p.2.1; let x2 := p.2.2.1; let x3 := p.2.2.2.1; let x4 := x; ((@Fin.val
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0)
      (@QuantumAlg.WireAddress.flipBit x0 x1 x4)).testBit
  (@Fin.val x0 (@QuantumAlg.WireAddress.bitIndex x0 x2)))) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (x0 : (Nat)) (x1 : (Fin x0)) (x2 : (Fin x0)) (x3 : (@Ne (Fin x0) x1 x2)) (x4 : (Fin
  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0))), R.readout () ⟨x0, x1, x2, x3, PUnit.unit⟩ x4 = ((@Fin.val
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0)
      x4).testBit
  (@Fin.val x0 (@QuantumAlg.WireAddress.bitIndex x0 x2)))
def source_bridge : (type_of% @QuantumAlg.WireAddress.bit_flipBit_of_ne) ↔ arena.Law actual := Iff.rfl
def actual_positive : arena.Law actual := @QuantumAlg.WireAddress.bit_flipBit_of_ne
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 (0 : Fin 2) (1 : Fin 2) (by decide) (1 : Fin (2 ^ 2))
  change false = true at hh
  cases hh
def source_registration : Registration arena (type_of% @QuantumAlg.WireAddress.bit_flipBit_of_ne) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨2, 0, 1, (by decide : (0 : Fin 2) ≠ 1), PUnit.unit⟩, (0 : Fin (2 ^ 2)), (1 : Fin (2 ^ 2)), ?_⟩
    change (QuantumAlg.WireAddress.flipBit (0 : Fin 2) (0 : Fin (2 ^ 2))).val.testBit 0 ≠
      (QuantumAlg.WireAddress.flipBit (0 : Fin 2) (1 : Fin (2 ^ 2))).val.testBit 0
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumAlg.WireAddress.bit_flipBit_of_ne) (Realization signature) Unit Unit := {
  unitName := `QuantumAlg.WireAddress.bit_flipBit_of_ne.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.FlipBitOther.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => let x0 := p.1; let x1 := p.2.1; let x2 := p.2.2.1; let x3 := p.2.2.2.1; let x4 := x; ((@Fin.val
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0)
      (@QuantumAlg.WireAddress.flipBit x0 x1 x4)).testBit
  (@Fin.val x0 (@QuantumAlg.WireAddress.bitIndex x0 x2)))) (fun e => nomatch e))
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
      stateOperand := some #["fn", "arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.FlipBitOther

namespace Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.FlipBitSelf
abbrev Params : Type _ := Σ' x0 : (Nat), Σ' x1 : (Fin x0), PUnit.{1}
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Params
  (fun p => let x0 := p.1; let x1 := p.2.1; (Fin
  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0))) (fun p => let x0 := p.1; let x1 := p.2.1; (Bool))
def actual : Realization signature :=
  realize signature (fun _ p x => let x0 := p.1; let x1 := p.2.1; let x2 := x; ((@Fin.val
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0)
      (@QuantumAlg.WireAddress.flipBit x0 x1 x2)).testBit
  (@Fin.val x0 (@QuantumAlg.WireAddress.bitIndex x0 x1)))) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (x0 : (Nat)) (x1 : (Fin x0)) (x2 : (Fin
  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0))), R.readout () ⟨x0, x1, PUnit.unit⟩ x2 = (((@Fin.val
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0)
        x2).testBit
    (@Fin.val x0 (@QuantumAlg.WireAddress.bitIndex x0 x1))).not)
def source_bridge : (type_of% @QuantumAlg.WireAddress.bit_flipBit_self) ↔ arena.Law actual := Iff.rfl
def actual_positive : arena.Law actual := @QuantumAlg.WireAddress.bit_flipBit_self
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (0 : Fin 1) (0 : Fin (2 ^ 1))
  change false = true at hh
  cases hh
def source_registration : Registration arena (type_of% @QuantumAlg.WireAddress.bit_flipBit_self) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨1, 0, PUnit.unit⟩, (0 : Fin (2 ^ 1)), (1 : Fin (2 ^ 1)), ?_⟩
    change (QuantumAlg.WireAddress.flipBit (0 : Fin 1) (0 : Fin (2 ^ 1))).val.testBit 0 ≠
      (QuantumAlg.WireAddress.flipBit (0 : Fin 1) (1 : Fin (2 ^ 1))).val.testBit 0
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumAlg.WireAddress.bit_flipBit_self) (Realization signature) Unit Unit := {
  unitName := `QuantumAlg.WireAddress.bit_flipBit_self.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.FlipBitSelf.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => let x0 := p.1; let x1 := p.2.1; let x2 := x; ((@Fin.val
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x0)
      (@QuantumAlg.WireAddress.flipBit x0 x1 x2)).testBit
  (@Fin.val x0 (@QuantumAlg.WireAddress.bitIndex x0 x1)))) (fun e => nomatch e))
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
      stateOperand := some #["fn", "arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.FlipBitSelf
namespace Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.BitIndexInjective
abbrev signature := Reg.Support.UniverseSingleReadout.signature Nat (fun n => Fin n) (fun n => Fin n)
def actual : Realization signature := realize signature
  (fun _ _ x => QuantumAlg.WireAddress.bitIndex x) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {n : Nat}, Function.Injective (R.readout () n)
def source_bridge : (type_of% @QuantumAlg.WireAddress.bitIndex_injective) ↔ arena.Law actual := Iff.rfl
def actual_positive : arena.Law actual := @QuantumAlg.WireAddress.bitIndex_injective
def rejected : Realization signature := realize signature
  (fun _ n x => ⟨0, by have hx := x.isLt; omega⟩) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 2)
  have impossible := hh (a₁ := 0) (a₂ := 1) (by rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) impossible
def source_registration : Registration arena (type_of% @QuantumAlg.WireAddress.bitIndex_injective) where
  actual := actual
  bridge := source_bridge
  variation := ⟨@actual_positive, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(2 : Nat), (0 : Fin 2), (1 : Fin 2), ?_⟩
    change QuantumAlg.WireAddress.bitIndex (0 : Fin 2) ≠ QuantumAlg.WireAddress.bitIndex (1 : Fin 2)
    decide
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumAlg.WireAddress.bitIndex_injective) (Realization signature) Unit Unit := {
  unitName := `QuantumAlg.WireAddress.bitIndex_injective.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.BitIndexInjective.source_registration
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
  (fun _ _ x => QuantumAlg.WireAddress.bitIndex x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress.BitIndexInjective
end
