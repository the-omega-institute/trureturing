import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus
import Reg.Support.DependentFamily
/-! Complete source telescopes with typed variation, sensitivity and dependence proofs. -/
namespace Reg.D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus
open _root_.D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MvPolynomial
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Slice
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ →L[ℝ] ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ →L[ℝ] ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => Complex.reCLM) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (κ : Type*) (F : MvPolynomial (Fin 2 ⊕ κ) ℝ) (θ : κ → ℝ) (z : ℂ),
    HasFDerivAt (fun w : ℂ => eval (slice θ w) F) (A.readout () () (sliceDerivative F θ z)) z
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h PUnit 0 (fun _ => 0) 0
  have he := congrArg (fun D : ℂ →L[ℝ] ℝ => D 1)
    (hh.unique (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : ℂ)))
  norm_num [rejected,realize] at he
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,Complex.reCLM,?_⟩
  intro h
  have he := congrArg (fun D : ℂ →L[ℝ] ℝ => D 1) h
  norm_num [actual,realize] at he
def source_registration : Registration arena (type_of% @hasFDerivAt_slice) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasFDerivAt_slice,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hasFDerivAt_slice) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus.hasFDerivAt_slice.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus.Slice.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Slice
namespace Determinant
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (D : ℂ →L[ℝ] ℂ), A.readout () () (LinearMap.det D.toLinearMap) =
    (D 1).re*(D Complex.I).im-(D Complex.I).re*(D 1).im
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (ContinuousLinearMap.id ℝ ℂ)
  norm_num [rejected,realize] at hh
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]
def source_registration : Registration arena (type_of% @real_det) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@real_det,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@real_det) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus.real_det.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus.Determinant.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Determinant
namespace Cleared
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (κ : Type*) (F H : MvPolynomial (Fin 2 ⊕ κ) ℝ) (θ : κ → ℝ) (z : ℂ)
    (f : ℂ → ℂ) (D : ℂ →L[ℝ] ℂ) (c e : ℂ → ℝ), f z = 0 → HasFDerivAt f D z →
    DifferentiableAt ℝ c z → DifferentiableAt ℝ e z →
    ((fun w => eval (slice θ w) F) =ᶠ[nhds z] fun w => c w*(f w).re) →
    ((fun w => eval (slice θ w) H) =ᶠ[nhds z] fun w => e w*(f w).im) →
    A.readout () () (eval (slice θ z) (trialJacobian F H)) = c z*e z*LinearMap.det D.toLinearMap
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hF : (fun w : ℂ => eval (slice (fun _ : PUnit => (0 : ℝ)) w) (X (Sum.inl 0))) =ᶠ[nhds 0]
      fun w => (1 : ℝ)*w.re := Filter.Eventually.of_forall (by intro w; simp [slice])
  have hH : (fun w : ℂ => eval (slice (fun _ : PUnit => (0 : ℝ)) w) (X (Sum.inl 1))) =ᶠ[nhds 0]
      fun w => (1 : ℝ)*w.im := Filter.Eventually.of_forall (by intro w; simp [slice])
  have hh := h PUnit (X (Sum.inl 0)) (X (Sum.inl 1)) (fun _ => 0) 0 id
    (ContinuousLinearMap.id ℝ ℂ) (fun _ => 1) (fun _ => 1) rfl (hasFDerivAt_id 0)
    (differentiableAt_const 1) (differentiableAt_const 1) hF hH
  norm_num [rejected,realize] at hh
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]
def source_registration : Registration arena (type_of% @cleared_jacobian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cleared_jacobian,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cleared_jacobian) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus.cleared_jacobian.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus.Cleared.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Cleared
end
end Reg.D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus
