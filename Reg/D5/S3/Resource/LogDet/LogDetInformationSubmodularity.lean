import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Resource.LogDet.LogDetInformationSubmodularity
import Reg.Support.UniverseSingleReadout

/-! Source-bound registration for logarithmic determinant monotonicity. -/

namespace Reg.D5.S3.Resource.LogDet.LogDetInformationSubmodularity

open _root_.D5.S3.Resource.LogDet.LogDetInformationSubmodularity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u

open scoped ComplexOrder MatrixOrder

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature
    (Σ Index : Type u, Σ _ : Fintype Index, DecidableEq Index)
    (fun p => Matrix (Sigma.fst p) (Sigma.fst p) ℂ) (fun _ => ℝ)

def actual : Realization signature.{u} :=
  realize signature (fun _ p right =>
    letI := Sigma.fst (Sigma.snd p)
    letI := Sigma.snd (Sigma.snd p)
    Real.log right.det.re) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Index : Type u} [ft : Fintype Index] [de : DecidableEq Index] [Nonempty Index]
    {left right : Matrix Index Index ℂ},
    left.PosDef → right.PosDef → left ≤ right →
      Real.log left.det.re ≤ R.readout () ⟨Index, ft, de⟩ right

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let M : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ := (2 : ℂ) • 1
  have hM : M.PosDef := by
    dsimp [M]
    exact Matrix.PosDef.one.smul (by norm_num [Complex.pos_iff])
  have hh := h (Index := ULift.{u} (Fin 1)) (left := M) (right := M) hM hM le_rfl
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  norm_num [rejected, realize, M, Matrix.det_unique] at hh
  linarith

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let M₁ : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ := 1
  let M₂ : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ := (2 : ℂ) • 1
  refine ⟨⟨ULift.{u} (Fin 1), inferInstance, inferInstance⟩, M₁, M₂, ?_⟩
  norm_num [actual, realize, M₁, M₂, Matrix.det_unique]
  exact ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))

def source_registration : Registration arena.{u}
    (type_of% @log_det_mono.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨log_det_mono,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_det_mono.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Resource.LogDet.LogDetInformationSubmodularity.unit
  realizationName := `Reg.D5.S3.Resource.LogDet.LogDetInformationSubmodularity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p right =>
    letI := Sigma.fst (Sigma.snd p)
    letI := Sigma.snd (Sigma.snd p)
    Real.log right.det.re)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Resource.LogDet.LogDetInformationSubmodularity
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Resource.LogDet.LogDetInformationSubmodularity
