import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality
import Reg.Support.DependentFamily

/-! The readout is the ordinary real derivative assertion for the exact native
fixed-target residual; the law retains the complete original telescope. -/
namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Matrix ComplexOrder Matrix.Norms.Elementwise
set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℂ ≃L[ℝ] ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ pq e => HasFDerivAt
    (residual fixedSector pq.1 pq.2 (leftTarget fixedSector 1 leftBoundary pq.1)
      (rightTarget fixedSector 1 rightBoundary pq.2)) (e : ℂ →L[ℝ] ℂ))
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law Z := ∀ (p q : ℕ), 1 ≤ p → 1 ≤ q →
    (leftTarget fixedSector 1 leftBoundary p).PosDef ∧
    (rightTarget fixedSector 1 rightBoundary q).PosDef ∧
    trialLeft fixedSector p (leftTarget fixedSector 1 leftBoundary p) 1 =
      vecMulVec (star leftBoundary) leftBoundary ∧
    trialRight fixedSector q (rightTarget fixedSector 1 rightBoundary q) 1 =
      vecMulVec rightBoundary (star rightBoundary) ∧
    residual fixedSector p q (leftTarget fixedSector 1 leftBoundary p)
      (rightTarget fixedSector 1 rightBoundary q) 1 = 0 ∧
    ∃ (L C R : ℝ) (e : ℂ ≃L[ℝ] ℂ) (u v : ℤ),
      (∀ w, e w = ((L*w.re : ℝ) : ℂ) + Complex.I * ((C*w.re+R*w.im : ℝ) : ℂ)) ∧
      Z.readout () ⟨p, q⟩ e 1 ∧
      (!![L, 0; C, R] : Matrix (Fin 2) (Fin 2) ℝ).det = L*R ∧ L*R ≠ 0 ∧
      5^p*L = (u : ℝ) ∧ 5^q*R = (v : ℝ) ∧
      5^(p+q)*(L*R) = ((u*v : ℤ) : ℝ) ∧
      ((u*v : ℤ) : ZMod 5) = 2*(-1)^(q+1)*3^q

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, _, L, C, R, e, u, v, _, hd, _⟩ := h 1 1 (by omega) (by omega)
  exact hd

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨_, _, _, _, _, L, C, R, e, u, v, _, hd, _⟩ :=
    interior_q2_fixed_target_witness 1 1 (by omega) (by omega)
  let two : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft
    (R₁ := ℝ) (M₁ := ℂ) (Units.mk0 (2 : ℝ) (by norm_num))
  let e2 := e.trans two
  refine ⟨⟨1, 1⟩, e, e2, ?_⟩
  intro he
  have hd2 : HasFDerivAt
      (residual fixedSector 1 1 (leftTarget fixedSector 1 leftBoundary 1)
        (rightTarget fixedSector 1 rightBoundary 1)) (e2 : ℂ →L[ℝ] ℂ) 1 :=
    Eq.mp (congrFun he 1) hd
  have heq := congrArg (fun f : ℂ →L[ℝ] ℂ => f 1) (hd.unique hd2)
  have hz : e 1 = 0 := by
    have ha : e 1 + e 1 = e 1 + 0 := by
      simpa [e2, two, two_smul] using heq.symm
    exact add_left_cancel ha
  have h1 : (1 : ℂ) = 0 := e.injective (by simpa using hz)
  exact one_ne_zero h1

def source_registration : Registration arena
    (type_of% @interior_q2_fixed_target_witness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@interior_q2_fixed_target_witness, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@interior_q2_fixed_target_witness) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality.interior_q2_fixed_target_witness.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ pq e => HasFDerivAt
    (residual fixedSector pq.1 pq.2 (leftTarget fixedSector 1 leftBoundary pq.1)
      (rightTarget fixedSector 1 rightBoundary pq.2)) (e : ℂ →L[ℝ] ℂ))
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end
end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality
