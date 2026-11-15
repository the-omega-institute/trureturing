import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial
import Reg.Support.DependentFamily
/-! Complete source telescopes with typed variation, sensitivity and dependence proofs. -/
namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality
open _root_.D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance
open _root_.D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MvPolynomial
open scoped Matrix ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
private lemma fixed_regular : Regular fixedSector := by
  norm_num [Regular,fixedSector,delta,alpha,beta,Complex.normSq_apply]
namespace Clear
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
  Law A := ∀ (p q : ℕ) (s : Sector), Regular s → ∀ (l r : Fin 2 → ℂ) (z₀ z : ℂ), z ≠ 0 →
    A.readout () () (eval (slice (coordinates s l r z₀) z) (FL p q)) =
      cL s p z*(residual s p q (leftTarget s z₀ l p) (rightTarget s z₀ r q) z).re ∧
    A.readout () () (eval (slice (coordinates s l r z₀) z) (FR p q)) =
      cR s q z*(residual s p q (leftTarget s z₀ l p) (rightTarget s z₀ r q) z).im
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_,_,_,_,_,L,C,R,e,u,v,he,hd,_,hne,_⟩ :=
    interior_q2_fixed_target_witness 1 1 (by omega) (by omega)
  have hzero : (fun w : ℂ => (residual fixedSector 1 1
      (leftTarget fixedSector 1 leftBoundary 1) (rightTarget fixedSector 1 rightBoundary 1) w).re) =ᶠ[nhds 1]
      fun _ => 0 := by
    filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0)] with w hw
    have hh := (h 1 1 fixedSector fixed_regular leftBoundary rightBoundary 1 w hw).1
    have hc := (clearance_positive fixedSector fixed_regular w hw 1 1).1.ne'
    have hz : cL fixedSector 1 w*(residual fixedSector 1 1 (leftTarget fixedSector 1 leftBoundary 1)
        (rightTarget fixedSector 1 rightBoundary 1) w).re = 0 := by simpa [rejected,realize] using hh.symm
    exact (mul_eq_zero.mp hz).resolve_left hc
  have hdre := Complex.reCLM.hasFDerivAt.comp 1 hd
  have hd0 := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (1 : ℂ)).congr_of_eventuallyEq hzero
  have hh := congrArg (fun T : ℂ →L[ℝ] ℝ => T 1) (hdre.unique hd0)
  have hL : L = 0 := by simpa [he] using hh
  exact hne (by simp [hL])
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]
def source_registration : Registration arena (type_of% @polynomial_clear) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@polynomial_clear,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@polynomial_clear) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial.polynomial_clear.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial.Clear.source_registration
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
end Clear
namespace Derivative
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
  Law A := ∀ (p q : ℕ) (s : Sector), Regular s → ∀ (l r : Fin 2 → ℂ) (z₀ : ℂ), z₀ ≠ 0 →
    ∀ (D : ℂ →L[ℝ] ℂ), HasFDerivAt (residual s p q (leftTarget s z₀ l p) (rightTarget s z₀ r q)) D z₀ →
    A.readout () () (eval (coordinates s l r z₀) (b p q)) = cL s p z₀*cR s q z₀*LinearMap.det D.toLinearMap
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_,_,_,_,_,L,C,R,e,u,v,he,hd,_,hne,_⟩ :=
    interior_q2_fixed_target_witness 1 1 (by omega) (by omega)
  have hh := h 1 1 fixedSector fixed_regular leftBoundary rightBoundary 1 (by norm_num) e hd
  have hv := b_eval_derivative 1 1 fixedSector fixed_regular leftBoundary rightBoundary 1 (by norm_num) e hd
  have hb := (b_nonzero 1 1 (by omega) (by omega)).1
  apply hb
  rw [hv]
  simpa [rejected,realize] using hh.symm
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]
def source_registration : Registration arena (type_of% @b_eval_derivative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@b_eval_derivative,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@b_eval_derivative) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial.b_eval_derivative.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial.Derivative.source_registration
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
end Derivative
namespace Nonzero
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
  Law A := ∀ (p q : ℕ), 1 ≤ p → 1 ≤ q →
    A.readout () () (eval (coordinates fixedSector leftBoundary rightBoundary 1) (b p q)) ≠ 0 ∧ b p q ≠ 0
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 1 (by omega) (by omega)).1
  exact hh rfl
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]
def source_registration : Registration arena (type_of% @b_nonzero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@b_nonzero,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@b_nonzero) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial.b_nonzero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial.Nonzero.source_registration
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
end Nonzero
namespace Scale
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
  Law A := ∀ (p q : ℕ) (θ : Fin 16 → ℝ) (a : ℝ),
    A.readout () () (eval (scaleRight a θ) (b p q)) = a^4*eval θ (b p q)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1 (coordinates fixedSector leftBoundary rightBoundary 1) 1
  have hb := (b_nonzero 1 1 (by omega) (by omega)).1
  apply hb
  simpa [rejected,realize] using hh.symm
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]
def source_registration : Registration arena (type_of% @b_right_scale) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@b_right_scale,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@b_right_scale) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial.b_right_scale.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial.Scale.source_registration
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
end Scale
namespace Ambiguity
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (p q : ℕ), 1 ≤ p → 1 ≤ q → ∀ (s : Sector), Regular s →
    ∀ (z₀ : ℂ), z₀ ≠ 0 → ∀ (l r : Fin 2 → ℂ),
    (leftTarget s z₀ l p).PosDef → (rightTarget s z₀ r q).PosDef →
    eval (coordinates s l r z₀) (b p q) ≠ 0 →
    A.readout () () (∃ φ : Word ((p + 2) + q) → ℂ,
      φ ∈ openBoundaryMPS ((p + 2) + q) ∧ φ ≠ 0 ∧
      _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.rawInterior p 2 q φ =
        _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.rawInterior p 2 q
          (mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r) ∧
      ¬ ∃ η : ℂ, ‖η‖ = 1 ∧ φ =
        η • mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hP,hH,_⟩ := interior_q2_fixed_target_witness 1 1 (by omega) (by omega)
  exact h 1 1 (by omega) (by omega) fixedSector fixed_regular 1 (by norm_num)
    leftBoundary rightBoundary hP hH (b_nonzero 1 1 (by omega) (by omega)).1
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (show False = True from h).mpr trivial
def source_registration : Registration arena (type_of% @nonzero_locus_actual_ambiguity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonzero_locus_actual_ambiguity,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@nonzero_locus_actual_ambiguity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial.nonzero_locus_actual_ambiguity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial.Ambiguity.source_registration
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
end Ambiguity

end
end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial
