import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing
import Reg.Support.FactorialFockMetric

/-! Whole-family observations for affine square bounds, joint convergence and sewing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Ring
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing
open D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
open D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
open D5.S3.VertexAlgebra.FactorialFockMetric (weight weight_pos)
universe u
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing

namespace Majorant
abbrev signature : Signature where
  Params := Σ I : Type u, Σ _ : I →₀ ℕ, ℕ
  State p := ((p.1 ⊕ Unit) →₀ ℕ) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize _ (fun _ p f => f (p.2.1.sumElim (Finsupp.single () p.2.2))) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize _ (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨PUnit.{u+1}, 0, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (mu : I → ℂ)
    (_hsym : ∀ i j, A i j = A j i)
    (_hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1),
    Summable (fun d : I →₀ ℕ => (weight d : ℝ) *
      (∑ k ∈ Finset.range (d.degree + 1),
        ‖R.readout () ⟨I, d, k⟩ (gaussianCoefficient (affineKernel A mu))‖) ^ 2)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance inferInstance 0 0 (fun _ _ => rfl) (by simp)
  have hs : Summable (fun _ : PUnit.{u+1} →₀ ℕ => (1 : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun _ => zero_le_one) _ hh
    intro d
    simp only [rejected, realize, norm_one, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    have hw : (1 : ℝ) ≤ weight d := by exact_mod_cast weight_pos d
    have hd : (1 : ℝ) ≤ (d.degree + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 d.degree
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (sq_nonneg ((d.degree + 1 : ℕ) : ℝ))]
  simp only [summable_const_iff, one_ne_zero, or_false] at hs

def family : Registration arena.{u} (type_of% (@affine_majorant_summable.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@affine_majorant_summable.{u}, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@affine_majorant_summable.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing.Majorant.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing.Majorant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing
    definition := none
    coordinates := #[0, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Majorant

namespace Joint
abbrev signature : Signature where
  Params := Σ I : Type u, (I →₀ ℕ) × (ℕ × ℕ)
  State p := ((p.1 ⊕ Unit) →₀ ℕ) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize _ (fun _ p f => f (p.2.1.sumElim (Finsupp.single () p.2.2.1))) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize _ (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨PUnit.{u+1}, 0, (0,0)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (mu nu : I → ℂ)
    (_hAsym : ∀ i j, A i j = A j i) (_hBsym : ∀ i j, B i j = B j i)
    (_hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (_hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1),
    Summable (fun p : (I →₀ ℕ) × (ℕ × ℕ) => ‖(weight p.1 : ℂ) *
      R.readout () ⟨I, p⟩ (gaussianCoefficient (affineKernel A mu)) *
      gaussianCoefficient (affineKernel B nu) (p.1.sumElim (Finsupp.single () p.2.2))‖)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance inferInstance 0 0 0 0
    (fun _ _ => rfl) (fun _ _ => rfl) (by simp) (by simp)
  have hi : Function.Injective (fun k : ℕ => ((0 : PUnit.{u+1} →₀ ℕ), (k, 0))) := by
    intro k l hkl
    exact congrArg (fun p => p.2.1) hkl
  have hs := hh.comp_injective hi
  have hc : Summable (fun _ : ℕ => (1 : ℝ)) := by
    simpa [Function.comp_def, rejected, realize, weight, gaussianCoefficient_zero] using hs
  simp only [summable_const_iff, one_ne_zero, or_false] at hc

def family : Registration arena.{u} (type_of% (@affine_joint_norm_summable.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@affine_joint_norm_summable.{u}, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@affine_joint_norm_summable.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing.Joint.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing.Joint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing
    definition := none
    coordinates := #[0, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Joint

namespace Sewing
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
abbrev signature := complexSignature
abbrev actual := complexEqual
abbrev rejected := complexFalse

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (mu nu : I → ℂ)
    (_hAsym : ∀ i j, A i j = A j i) (_hBsym : ∀ i j, B i j = B j i)
    (_hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (_hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1),
    Summable (fun d : I →₀ ℕ => ‖(weight d : ℂ) *
      affineCoefficient A mu d * affineCoefficient B nu d‖) ∧
    R.readout () ()
      (∑' d : I →₀ ℕ, (weight d : ℂ) * affineCoefficient A mu d * affineCoefficient B nu d)
      (Complex.exp ((1 / 2 : ℂ) *
        ∑' n : ℕ, Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ)) *
      Complex.exp ((1 / 2 : ℂ) * ∑ x, ∑ y,
        D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.effectiveKernel
          (0 : Matrix Unit Unit ℂ) (0 : Matrix Unit Unit ℂ) A B
          (fun _ i => mu i) (fun i _ => nu i) x y))

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  exact (@h PUnit.{u+1} inferInstance inferInstance 0 0 0 0
    (fun _ _ => rfl) (fun _ _ => rfl) (by simp) (by simp)).2

def family : Registration arena.{u} (type_of% (@finite_affine_sewing.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_affine_sewing.{u}, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_affine_sewing.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing.Sewing.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing.Sewing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Sewing

end Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing
