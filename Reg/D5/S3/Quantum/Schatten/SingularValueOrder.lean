import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.SingularValueOrder
import Reg.Support.SingleDependentReadout

/-! Full-source registrations for singular-value order and its spectral coordinates. -/

namespace Reg.D5.S3.Quantum.Schatten.SingularValueOrder
open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def equalityActual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def orderActual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem equality_dependence : ObservationalDependence signature equalityActual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

private theorem order_dependence : ObservationalDependence signature orderActual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hbad

namespace SpectralCoordinates
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))), R.readout () () (singularValuesSorted A i)
      (Real.sqrt ((isHermitian_mul_conjTranspose_self Aᴴ).eigenvalues₀ i))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 0 ⟨0, by simp⟩

def source_registration : Registration arena (type_of% @singularValuesSorted_eq_sqrt_eigenvalues_zero) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@singularValuesSorted_eq_sqrt_eigenvalues_zero, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law equalityActual rejected rejected_law
  dependence := equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@singularValuesSorted_eq_sqrt_eigenvalues_zero) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.singularValuesSorted_eq_sqrt_eigenvalues_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.SingularValueOrder.SpectralCoordinates.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.SingularValueOrder
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
end SpectralCoordinates

namespace GramOrder
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (_h : (Bᴴ * B - Aᴴ * A).PosSemidef) (i : Fin (Fintype.card (Fin n))),
    R.readout () () (singularValuesSorted A i) (singularValuesSorted B i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 0 0 (by simpa using (PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef)) ⟨0, by simp⟩

def source_registration : Registration arena (type_of% @gram_singularValuesSorted_mono) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@gram_singularValuesSorted_mono, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law orderActual rejected rejected_law
  dependence := order_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@gram_singularValuesSorted_mono) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.gram_singularValuesSorted_mono.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.SingularValueOrder.GramOrder.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.SingularValueOrder
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
end GramOrder

namespace UnitaryLeft
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℂ)
    (_h : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))),
    R.readout () () (singularValuesSorted (U * A) i) (singularValuesSorted A i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 1 0 (by simp) ⟨0, by simp⟩

def source_registration : Registration arena (type_of% @singularValuesSorted_unitary_mul) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@singularValuesSorted_unitary_mul, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law equalityActual rejected rejected_law
  dependence := equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@singularValuesSorted_unitary_mul) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.singularValuesSorted_unitary_mul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.SingularValueOrder.UnitaryLeft.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.SingularValueOrder
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
end UnitaryLeft

namespace Scaling
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (_hr : 0 ≤ r)
    (i : Fin (Fintype.card (Fin n))),
    R.readout () () (singularValuesSorted ((r : ℂ) • A) i) (r * singularValuesSorted A i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 0 0 le_rfl ⟨0, by simp⟩

def source_registration : Registration arena (type_of% @singularValuesSorted_smul_nonneg) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@singularValuesSorted_smul_nonneg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law equalityActual rejected rejected_law
  dependence := equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@singularValuesSorted_smul_nonneg) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.singularValuesSorted_smul_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.SingularValueOrder.Scaling.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.SingularValueOrder
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
end Scaling

namespace Adjoint
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))), R.readout () () (singularValuesSorted Aᴴ i) (singularValuesSorted A i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 0 ⟨0, by simp⟩

def source_registration : Registration arena (type_of% @singularValuesSorted_conjTranspose) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@singularValuesSorted_conjTranspose, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law equalityActual rejected rejected_law
  dependence := equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@singularValuesSorted_conjTranspose) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.singularValuesSorted_conjTranspose.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.SingularValueOrder.Adjoint.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.SingularValueOrder
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
end Adjoint
namespace EigenvalueOrder
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {H K : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian), (K-H).PosSemidef →
    ∀ i : Fin (Fintype.card (Fin n)), R.readout () () (hH.eigenvalues₀ i) (hK.eigenvalues₀ i)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) (H := 0) (K := 0) Matrix.isHermitian_zero Matrix.isHermitian_zero
    (by simpa using (PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
    ⟨0, by simp⟩
def family : Registration arena (type_of% (@eigenvalues_zero_mono)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@eigenvalues_zero_mono, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law orderActual rejected rejectedLaw
  dependence := order_dependence
def audit :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@eigenvalues_zero_mono) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Schatten.eigenvalues_zero_mono.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.SingularValueOrder.EigenvalueOrder.family
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
    owner := `D5.S3.Quantum.Schatten.SingularValueOrder
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
end EigenvalueOrder

namespace EigenvalueScale
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (q : ℝ), 0 ≤ q → ∀ (hQ : ((q : ℂ) • H).IsHermitian)
    (i : Fin (Fintype.card (Fin n))), R.readout () () (hQ.eigenvalues₀ i) (q*hH.eigenvalues₀ i)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) 0 Matrix.isHermitian_zero 0 le_rfl (by simp) ⟨0, by simp⟩
def family : Registration arena (type_of% (@eigenvalues_zero_smul)) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@eigenvalues_zero_smul, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equalityActual rejected rejectedLaw
  dependence := equality_dependence
def audit :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@eigenvalues_zero_smul) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Schatten.eigenvalues_zero_smul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.SingularValueOrder.EigenvalueScale.family
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
    owner := `D5.S3.Quantum.Schatten.SingularValueOrder
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
end EigenvalueScale
end
end Reg.D5.S3.Quantum.Schatten.SingularValueOrder
