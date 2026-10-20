/- GID: Reg/D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational
   generality: G
   mirror-B: none
   mirror-E: none
   anchors: []
   utility: none
   digest: Source-bound registrations for signed testing and attainment. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.KyFanGap.SignedVariational
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for signed testing and attainment. -/

noncomputable section
open _root_.D5.S3.Combinatorics.Graph.KyFanGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Combinatorics.Graph.KyFanGap.SignedVariational
namespace PairingBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n : ℕ} (W : SignedWitness k n)
    (M : Matrix (Fin n) (Fin n) ℝ), M.IsSymm →
    R.readout () () (signedPairing W M) (kyFan k M)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  let W : SignedWitness 0 0 := {
    vectors := fun i => Fin.elim0 i
    orthonormal_vectors := by rw [orthonormal_iff_ite]; intro i; exact Fin.elim0 i
    signs := fun i => Fin.elim0 i
    signs_sq := fun i => Fin.elim0 i }
  exact h W 0 (by exact Matrix.isSymm_zero)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he (1/2)
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@signed_pairing_le_kyFan)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signed_pairing_le_kyFan, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signed_pairing_le_kyFan) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.signed_pairing_le_kyFan.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.SignedVariational.PairingBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.SignedVariational
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PairingBound
namespace PairingAttainment
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n : ℕ}, k ≤ n →
    ∀ (M : Matrix (Fin n) (Fin n) ℝ), M.IsSymm →
      ∃ W : SignedWitness k n, R.readout () () (signedPairing W M) (kyFan k M)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨W, hW⟩ := h (k := 0) (n := 0) le_rfl 0 Matrix.isSymm_zero
  exact hW
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : ℝ)
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@exists_signed_pairing_eq_kyFan)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_signed_pairing_eq_kyFan, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_signed_pairing_eq_kyFan) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.exists_signed_pairing_eq_kyFan.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.SignedVariational.PairingAttainment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.SignedVariational
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PairingAttainment
end Reg.D5.S3.Combinatorics.Graph.KyFanGap.SignedVariational
