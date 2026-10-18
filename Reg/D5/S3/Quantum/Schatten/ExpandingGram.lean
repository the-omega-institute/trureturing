import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.ExpandingGram
import Reg.Support.SingleDependentReadout

/-! Full-source registrations for expanding square matrices. -/
namespace Reg.D5.S3.Quantum.Schatten.ExpandingGram
open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Invertibility
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ z => IsUnit z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (_h : (Tᴴ * T - 1).PosSemidef), R.readout () () T.det
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 1 (by simpa using (PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  intro he
  have hh : IsUnit (0 : ℂ) := Eq.mpr he (by simp [actual, realize])
  norm_num at hh
def source_registration : Registration arena (type_of% @expanding_isUnit_det) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@expanding_isUnit_det, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@expanding_isUnit_det) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.expanding_isUnit_det.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.ExpandingGram.Invertibility.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => IsUnit z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.ExpandingGram
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Invertibility
namespace Adjoint
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℂ) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ M => M.PosSemidef) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (_h : (Tᴴ * T - 1).PosSemidef), R.readout () n (T * Tᴴ - 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 1 (by simpa using (PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Matrix (Fin 1) (Fin 1) ℂ), -1, ?_⟩
  intro he
  have hh : (- (1 : Matrix (Fin 1) (Fin 1) ℂ)).PosSemidef :=
    Eq.mp he PosSemidef.zero
  have hd := hh.diag_nonneg (i := (0 : Fin 1))
  change (0 : ℂ) ≤ -1 at hd
  norm_num [Complex.le_def] at hd
def source_registration : Registration arena (type_of% @expanding_adjoint) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@expanding_adjoint, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@expanding_adjoint) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.expanding_adjoint.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.ExpandingGram.Adjoint.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.ExpandingGram
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Adjoint
namespace RightMultiply
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A T : Matrix (Fin n) (Fin n) ℂ)
    (_h : (Tᴴ * T - 1).PosSemidef) (i : Fin (Fintype.card (Fin n))),
    R.readout () () (singularValuesSorted A i) (singularValuesSorted (A * T) i)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 0 1 (by simpa using (PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef)) ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hh
def source_registration : Registration arena (type_of% @expanding_right_singularValuesSorted) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@expanding_right_singularValuesSorted, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@expanding_right_singularValuesSorted) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.expanding_right_singularValuesSorted.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.ExpandingGram.RightMultiply.source_registration
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
    owner := `D5.S3.Quantum.Schatten.ExpandingGram
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

end RightMultiply
end
end Reg.D5.S3.Quantum.Schatten.ExpandingGram
