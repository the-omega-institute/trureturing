import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Estimation.WhiteBoxLossFiberLaw.PartialAbsorption

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Estimation.WhiteBoxLossFiberLaw.PartialAbsorption
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.WhiteBoxLossFiberLaw.PartialAbsorption
open _root_.D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching
open LeanInformationAudit Set
open scoped Topology RealInnerProductSpace
universe u

@[reducible] def signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p*x*(1-x)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam p0 pA pAB pB : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hp0 : 0 ≤ p0) (hpA : 0 ≤ pA) (hpAB : 0 ≤ pAB) (hpB : 0 ≤ pB)
    (hprob : p0+pA+pAB+pB = 1)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hAB : 0 < pAB) (hB : 0 < pB),
    let D := rotatingDictionary u v hu hv huv
    let J := objective lam p0 pA pAB pB u v hu hv huv
    (D (Real.pi/4)).1 1 = bisector u v ∧ (D (Real.pi/2)).1 1 = v ∧
    (∀ α x, ∃ c, FeasibleCode c ∧ codeCost lam x (D α) = codeEnergy lam x (D α) c) ∧
    (∃ U : Set ℝ, IsOpen U ∧ Real.pi/4 ∈ U ∧ ∀ α ∈ U, DifferentiableAt ℝ J α) ∧
    (∃ V : Set ℝ, IsOpen V ∧ Real.pi/2 ∈ V ∧ ∀ α ∈ V, DifferentiableAt ℝ J α) ∧
    HasDerivAt J (-pB*(1/Real.sqrt 2-lam)/Real.sqrt 2) (Real.pi/4) ∧
    HasDerivAt J (R.readout ⟨()⟩ pAB lam) (Real.pi/2) ∧
    HasDerivWithinAt J (-pB*(1/Real.sqrt 2-lam)/Real.sqrt 2)
      (Icc (Real.pi/4) (Real.pi/2)) (Real.pi/4) ∧
    HasDerivWithinAt J (pAB*lam*(1-lam)) (Icc (Real.pi/4) (Real.pi/2)) (Real.pi/2) ∧
    -pB*(1/Real.sqrt 2-lam)/Real.sqrt 2 < 0 ∧ 0 < pAB*lam*(1-lam) ∧
    (∀ α ∈ Icc (Real.pi/4) (Real.pi/2),
      IsMinOn J (Icc (Real.pi/4) (Real.pi/2)) α → α ∈ Ioo (Real.pi/4) (Real.pi/2)) ∧
    ∃ α ∈ Ioo (Real.pi/4) (Real.pi/2), J α < J (Real.pi/4) ∧ J α < J (Real.pi/2)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let e : EuclideanSpace ℝ (ULift.{u} (Fin 2)) := EuclideanSpace.single ⟨0⟩ 1
  let f : EuclideanSpace ℝ (ULift.{u} (Fin 2)) := EuclideanSpace.single ⟨1⟩ 1
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.single]
  have hf : ‖f‖ = 1 := by simp [f, EuclideanSpace.single]
  have hef : inner ℝ e f = 0 := by
    simp [e, f, EuclideanSpace.inner_single_left, EuclideanSpace.single, PiLp.single_apply]
  have hsmall : (1/4 : ℝ) < 1/Real.sqrt 2 := by
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hc := h (1/4) 0 0 (1/2) (1/2) e f he hf hef
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hsmall (by norm_num) (by norm_num)
  have ha := partial_absorption (1/4) 0 0 (1/2) (1/2) e f he hf hef
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hsmall (by norm_num) (by norm_num)
  rcases hc with ⟨_,_,_,_,_,_,hbad,_,_,_,_,_,_⟩
  rcases ha with ⟨_,_,_,_,_,_,hactual,_,_,_,_,_,_⟩
  have heq := hbad.unique hactual
  norm_num [rejected, realize] at heq

def family : Registration arena.{u} (type_of% (@partial_absorption.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@partial_absorption.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1/2,1/4,1/2,?_⟩
    norm_num [actual, realize]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@partial_absorption.{u}) (type_of% (realize signature.{u}
      (fun _ p x => p*x*(1-x)) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Estimation.WhiteBoxLossFiberLaw.PartialAbsorption.partial_absorption.__information_unit
  realizationName := `Reg.D5.S3.Estimation.WhiteBoxLossFiberLaw.PartialAbsorption.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p x => p*x*(1-x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Estimation.WhiteBoxLossFiberLaw.PartialAbsorption
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Estimation.WhiteBoxLossFiberLaw.PartialAbsorption
