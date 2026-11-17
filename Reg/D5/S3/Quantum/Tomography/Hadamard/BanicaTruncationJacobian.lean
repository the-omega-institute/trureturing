import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian
import Reg.Support.UniverseSingleReadout

/-! Source-bound registrations of Jacobian coordinates and phase-space dimension laws. -/

namespace Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian
open _root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Topology ContDiff
open Filter
noncomputable section
universe u v

namespace phase_jacobian_apply
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Unit
    (fun _ => ℂ) (fun _ => ℂ → Prop)
def actual : Realization signature := realize signature (fun _ _ a b => a = b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n] [LinearOrder m]
      (H : Matrix m n ℂ) (η : m → n → ℝ) (e : RowPairs m),
    R.readout () () (phaseJacobian H η e) (Complex.I * ∑ j,
      H e.1.1 j * star (H e.1.2 j) * ((η e.1.1 j - η e.1.2 j : ℝ) : ℂ))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (m := ULift.{u} (Fin 2)) (n := ULift.{v} Unit) 0 0
    ⟨(⟨0⟩, ⟨1⟩), by decide⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := (congrFun h 0).mp rfl
  exact one_ne_zero hh
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.phase_jacobian_apply)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.phase_jacobian_apply, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.phase_jacobian_apply) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.phase_jacobian_apply.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.phase_jacobian_apply.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end phase_jacobian_apply

namespace row_column_finrank_le
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n],
    R.readout () () (Module.finrank ℝ (LinearMap.range (rowColumnMap (m := m) (n := n))))
      (Fintype.card m + Fintype.card n)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (m := ULift.{u} Unit) (n := ULift.{v} Unit)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := (congrFun h 0).mp (le_refl (0 : ℕ))
  exact Nat.not_succ_le_zero 0 hh
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.row_column_finrank_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.row_column_finrank_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.row_column_finrank_le) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.row_column_finrank_le.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.row_column_finrank_le.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end row_column_finrank_le

namespace row_pairs_card_twice
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ a b => a = b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Type u} [Fintype m] [LinearOrder m],
    R.readout () () (2 * Fintype.card (RowPairs m))
      (Fintype.card m * (Fintype.card m - 1))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (m := ULift.{u} Unit)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := (congrFun h 0).mp rfl
  exact one_ne_zero hh
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.row_pairs_card_twice)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.row_pairs_card_twice, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.row_pairs_card_twice) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.row_pairs_card_twice.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.row_pairs_card_twice.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end row_pairs_card_twice

namespace phase_jacobian_rank_nullity
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ a b => a = b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n] [LinearOrder m]
      (H : Matrix m n ℂ) (_hsurj : Function.Surjective (phaseJacobian H)),
    R.readout () () (Module.finrank ℝ (LinearMap.ker (phaseJacobian H).toLinearMap) +
      Fintype.card m * (Fintype.card m - 1)) (Fintype.card m * Fintype.card n)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  apply h (m := ULift.{u} Unit) (n := ULift.{v} Unit) 0
  intro y
  refine ⟨0, ?_⟩
  ext e
  exact (ne_of_lt e.2 (Subsingleton.elim _ _)).elim
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := (congrFun h 0).mp rfl
  exact one_ne_zero hh
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.phase_jacobian_rank_nullity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.phase_jacobian_rank_nullity, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.phase_jacobian_rank_nullity) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.phase_jacobian_rank_nullity.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian.phase_jacobian_rank_nullity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end phase_jacobian_rank_nullity



end
end Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian
