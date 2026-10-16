import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Matrix.DivisionFreeSchur

namespace Reg.D5.S3.Quantum.Matrix.DivisionFreeSchur
open _root_.D5.S3.Quantum.Matrix.DivisionFreeSchur
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
universe u v
noncomputable section

/-- The entire family of finite output carriers is retained, including empty
carriers. Variation is required of the family, not of every degenerate fiber. -/
abbrev signature : Signature where
  Params := Σ J : Type v, Fintype J
  State p := Matrix p.1 p.1 ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => by
    classical
    exact (-1 : Matrix p.1 p.1 ℝ)) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨ULift.{v} (Fin 1), inferInstance⟩, 0, 1, ?_⟩
  intro he
  have h := congrFun (congrFun he ⟨0⟩) ⟨0⟩
  norm_num [actual, realize] at h

namespace Schur
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    {K : Matrix I I ℝ}, K.PosSemidef → ∀ (v : I → ℝ) (U : Matrix I J ℝ),
      (O.readout () ⟨J, inferInstance⟩ (schur K v U)).PosSemidef

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (I := ULift.{u} (Fin 1)) (J := ULift.{v} (Fin 1)) (K := 0) Matrix.PosSemidef.zero 0 0
  have hn := bad.diag_nonneg (i := ⟨0⟩)
  norm_num [rejected, realize] at hn

def evidence : Registration arena (type_of% (@schur_posSemidef.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨schur_posSemidef, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Matrix.DivisionFreeSchur.schur_posSemidef.{u,v})
      (type_of% (realize signature (fun _ _ X => X) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.DivisionFreeSchur.schur_posSemidef.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.DivisionFreeSchur.Schur.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Schur

namespace Mixed
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    {K₀ K₁ : Matrix I I ℝ}, K₀.PosSemidef → K₁.PosSemidef →
    ∀ (v : I → ℝ) (U : Matrix I J ℝ),
      (O.readout () ⟨J, inferInstance⟩ (mixed K₀ K₁ v U)).PosSemidef

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (I := ULift.{u} (Fin 1)) (J := ULift.{v} (Fin 1)) (K₀ := 0) (K₁ := 0)
    Matrix.PosSemidef.zero Matrix.PosSemidef.zero 0 0
  have hn := bad.diag_nonneg (i := ⟨0⟩)
  norm_num [rejected, realize] at hn

def evidence : Registration arena (type_of% (@mixed_posSemidef.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_posSemidef, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Matrix.DivisionFreeSchur.mixed_posSemidef.{u,v})
      (type_of% (realize signature (fun _ _ X => X) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.DivisionFreeSchur.mixed_posSemidef.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.DivisionFreeSchur.Mixed.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Mixed

/- The source-selection ties for computed matrix operands are unfinished.
These source terms assert no validated binding; use existing issues 17689 and
17734 when reporting missing compiler/inspector evidence. -/
end
end Reg.D5.S3.Quantum.Matrix.DivisionFreeSchur
