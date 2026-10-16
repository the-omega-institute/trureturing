import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Matrix.DivisionFreeSchur

namespace Reg.D5.S3.Quantum.Matrix.DivisionFreeSchur
open _root_.D5.S3.Quantum.Matrix.DivisionFreeSchur
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit _root_.Matrix
universe u v
noncomputable section
open Classical

/-- The entire family of finite output carriers is retained, including empty
carriers. Variation is required of the family, not of every degenerate fiber. -/
abbrev signature : Signature where
  Params := Type v
  State p := Matrix p p ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature.{v} (fun _ _ X => decide X.PosSemidef) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

private theorem negative_not_psd :
    ¬ (-1 : Matrix (ULift.{_} (Fin 1)) (ULift.{_} (Fin 1)) ℝ).PosSemidef := by
  intro h
  have hn := h.diag_nonneg (i := ⟨0⟩)
  norm_num at hn

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨ULift.{_} (Fin 1), 0, -1, ?_⟩
  change decide (0 : Matrix (ULift.{_} (Fin 1)) (ULift.{_} (Fin 1)) ℝ).PosSemidef ≠
    decide (-1 : Matrix (ULift.{_} (Fin 1)) (ULift.{_} (Fin 1)) ℝ).PosSemidef
  simp [negative_not_psd, Matrix.PosSemidef.zero]

namespace Schur
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    {K : Matrix I I ℝ}, K.PosSemidef → ∀ (v : I → ℝ) (U : Matrix I J ℝ),
      O.readout () J (schur K v U) = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (I := ULift.{_} (Fin 1)) (J := ULift.{_} (Fin 1)) (K := 0) Matrix.PosSemidef.zero 0 0
  norm_num [rejected, realize] at bad
  cases bad

def evidence : Registration arena (type_of% (@schur_posSemidef.{u,v})) where
  actual := actual
  bridge := by
    constructor
    · intro source I J _ _ K hK v U
      exact decide_eq_true (source hK v U)
    · intro law I J _ _ K hK v U
      exact of_decide_eq_true (law hK v U)
  variation := ⟨by
    intro I J _ _ K hK v U
    exact decide_eq_true (schur_posSemidef hK v U), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Matrix.DivisionFreeSchur.schur_posSemidef.{u,v})
      (type_of% (realize signature.{v} (fun _ _ X => decide X.PosSemidef) (fun e => nomatch e))) Unit Unit := {
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
  readout := some (realize signature.{v} (fun _ _ X => decide X.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.DivisionFreeSchur
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
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
      O.readout () J (mixed K₀ K₁ v U) = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (I := ULift.{_} (Fin 1)) (J := ULift.{_} (Fin 1)) (K₀ := 0) (K₁ := 0)
    Matrix.PosSemidef.zero Matrix.PosSemidef.zero 0 0
  norm_num [rejected, realize] at bad
  cases bad

def evidence : Registration arena (type_of% (@mixed_posSemidef.{u,v})) where
  actual := actual
  bridge := by
    constructor
    · intro source I J _ _ K₀ K₁ h₀ h₁ v U
      exact decide_eq_true (source h₀ h₁ v U)
    · intro law I J _ _ K₀ K₁ h₀ h₁ v U
      exact of_decide_eq_true (law h₀ h₁ v U)
  variation := ⟨by
    intro I J _ _ K₀ K₁ h₀ h₁ v U
    exact decide_eq_true (mixed_posSemidef h₀ h₁ v U), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Matrix.DivisionFreeSchur.mixed_posSemidef.{u,v})
      (type_of% (realize signature.{v} (fun _ _ X => decide X.PosSemidef) (fun e => nomatch e))) Unit Unit := {
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
  readout := some (realize signature.{v} (fun _ _ X => decide X.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.DivisionFreeSchur
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Mixed

/- The PSD observation retains the computed matrix operand and the full
source telescope. Current compiler and inspector evidence determines binding
status; unresolved failures are disclosed under issue 17734. -/
end
end Reg.D5.S3.Quantum.Matrix.DivisionFreeSchur
