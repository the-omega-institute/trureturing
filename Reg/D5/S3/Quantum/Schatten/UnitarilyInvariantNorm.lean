import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import Reg.Support.SingleDependentReadout

/-! Full-statement source registrations for unitarily invariant norm comparisons. -/

namespace Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm

open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.Quantum.Schatten.UINorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

def zeroDimNorm : UINorm 0 where
  N _ := 0
  nonneg _ := le_rfl
  eq_zero_iff X := ⟨fun _ => Subsingleton.elim X 0, fun _ => rfl⟩
  add_le _ _ := by simp
  smul_eq _ _ := by simp
  unitary_invariant _ _ _ _ _ := rfl

abbrev relationSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def equalityActual : Realization relationSignature :=
  realize relationSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def orderActual : Realization relationSignature :=
  realize relationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization relationSignature :=
  realize relationSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem equality_dependence : ObservationalDependence relationSignature equalityActual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

theorem order_dependence : ObservationalDependence relationSignature orderActual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hbad

namespace SingularValues

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (X : Matrix (Fin n) (Fin n) ℂ),
    R.readout () () (ν.N X) (ν.N (diagonal (fun i => (singularValues X i : ℂ))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 zeroDimNorm 0

def source_registration : Registration arena (type_of% @N_eq_singularValues) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@N_eq_singularValues, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law equalityActual rejected
    rejected_law
  dependence := equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@N_eq_singularValues) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.N_eq_singularValues.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.SingularValues.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
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
  options := #[] }

end SingularValues

namespace ConjTranspose

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (X : Matrix (Fin n) (Fin n) ℂ),
    R.readout () () (ν.N Xᴴ) (ν.N X)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 zeroDimNorm 0

def source_registration : Registration arena (type_of% @N_conjTranspose) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@N_conjTranspose, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law equalityActual rejected
    rejected_law
  dependence := equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@N_conjTranspose) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.N_conjTranspose.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.ConjTranspose.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
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
  options := #[] }

end ConjTranspose

namespace Transpose

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (X : Matrix (Fin n) (Fin n) ℂ),
    R.readout () () (ν.N Xᵀ) (ν.N X)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 zeroDimNorm 0

def source_registration : Registration arena (type_of% @N_transpose) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@N_transpose, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law equalityActual rejected
    rejected_law
  dependence := equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@N_transpose) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.N_transpose.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.Transpose.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
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
  options := #[] }

end Transpose

namespace DiagonalContract

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (x c : Fin n → ℝ) (_hc : ∀ i, |c i| ≤ 1),
    R.readout () () (ν.N (diagonal (fun i => ((c i * x i : ℝ) : ℂ))))
      (ν.N (diagonal (fun i => (x i : ℂ))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 zeroDimNorm (fun _ => 0) (fun _ => 0) (by intro i; exact Fin.elim0 i)

def source_registration : Registration arena (type_of% @N_diagonal_contract) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@N_diagonal_contract, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law orderActual rejected
    rejected_law
  dependence := order_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@N_diagonal_contract) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.N_diagonal_contract.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.DiagonalContract.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
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
  options := #[] }

end DiagonalContract

namespace DiagonalMono

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (x y : Fin n → ℝ) (_hxy : ∀ i, |x i| ≤ |y i|),
    R.readout () () (ν.N (diagonal (fun i => (x i : ℂ))))
      (ν.N (diagonal (fun i => (y i : ℂ))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 zeroDimNorm (fun _ => 0) (fun _ => 0) (by intro i; exact Fin.elim0 i)

def source_registration : Registration arena (type_of% @N_diagonal_mono) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@N_diagonal_mono, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law orderActual rejected
    rejected_law
  dependence := order_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@N_diagonal_mono) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.N_diagonal_mono.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.DiagonalMono.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
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
  options := #[] }

end DiagonalMono

namespace DiagonalWeakMajorization

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (z q : Fin n → ℝ) (_hz : Antitone z)
    (_hz0 : ∀ i, 0 ≤ z i) (_hq0 : ∀ i, 0 ≤ q i)
    (_hpre : ∀ k, prefixSum k z ≤ prefixSum k q),
    R.readout () () (ν.N (diagonal (fun i => (z i : ℂ))))
      (ν.N (diagonal (fun i => (q i : ℂ))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 zeroDimNorm (fun _ => 0) (fun _ => 0)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro k; exact le_rfl)

def source_registration : Registration arena (type_of% @N_diagonal_weakMajorization) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@N_diagonal_weakMajorization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law orderActual rejected
    rejected_law
  dependence := order_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@N_diagonal_weakMajorization) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.N_diagonal_weakMajorization.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.DiagonalWeakMajorization.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
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
  options := #[] }

end DiagonalWeakMajorization


namespace DiagonalPerm

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)),
    R.readout () () (ν.N (diagonal (fun i => (x (σ i) : ℂ))))
      (ν.N (diagonal (fun i => (x i : ℂ))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 zeroDimNorm (fun _ => 0) 1

def source_registration : Registration arena (type_of% @N_diagonal_perm) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@N_diagonal_perm, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law equalityActual rejected
    rejected_law
  dependence := equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@N_diagonal_perm) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.N_diagonal_perm.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.DiagonalPerm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
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
  options := #[] }

end DiagonalPerm

namespace DiagonalPermMatrix

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)),
    R.readout () () (ν.N (diagonal (fun i => (a i : ℂ)) * σ.permMatrix ℂ *
      diagonal (fun i => (b i : ℂ))))
      (ν.N (diagonal (fun i => ((a i * b (σ i) : ℝ) : ℂ))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 zeroDimNorm (fun _ => 0) (fun _ => 0) 1

def source_registration : Registration arena (type_of% @N_diagonal_permMatrix) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@N_diagonal_permMatrix, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law equalityActual rejected
    rejected_law
  dependence := equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@N_diagonal_permMatrix) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.N_diagonal_permMatrix.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.DiagonalPermMatrix.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
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
  options := #[] }

end DiagonalPermMatrix

end
end Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
