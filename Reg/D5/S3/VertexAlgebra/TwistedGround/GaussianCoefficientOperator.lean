import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientOperator

/-! Source-bound exponential readout for the full heterogeneous operator norm law. -/

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
open _root_.D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientOperator
open scoped lp

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientOperator
universe u v

/-- The varying readout is the actual exponential on the source's bound operand. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

/-- The entire original telescope is retained, including degenerate mode types. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {S : Type u} {T : Type v} [DecidableEq S] [DecidableEq T]
    (D : Data (S ⊕ T)),
    ‖coefficientOperator D‖ ≤ R.readout () () (D.massBound / (4 * (1 - D.q ^ 2)))

private def zeroData (I : Type*) [DecidableEq I] : Data I where
  oneParticle := 0
  q := 0
  massBound := 0
  q_nonneg := le_refl _
  q_lt_one := by norm_num
  opNorm_le := by simp
  symmetric := by intros; simp
  square_summable := by simp
  square_sum_le := by simp

private theorem actual_law : arena.{u,v}.Law actual := by
  intro S T _ _ D
  exact coefficientOperator_norm_le D

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hn := h (S := ULift.{u} Empty) (T := ULift.{v} Empty) (zeroData _)
  change ‖coefficientOperator (zeroData (ULift.{u} Empty ⊕ ULift.{v} Empty))‖ ≤ (-1 : ℝ) at hn
  linarith [norm_nonneg (coefficientOperator (zeroData (ULift.{u} Empty ⊕ ULift.{v} Empty)))]

def normFamily : Registration arena.{u,v} (type_of% (@coefficientOperator_norm_le.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law.{u,v}, rejected, rejected_law.{u,v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law.{u,v}⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    exact Real.exp_injective.ne (by norm_num : (0 : ℝ) ≠ 1)

def normRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coefficientOperator_norm_le.{u,v})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName :=
    `D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientOperator.coefficientOperator_norm_le.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientOperator.normFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨normFamily.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientOperator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms normFamily
#print axioms normRegistration
end Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientOperator
