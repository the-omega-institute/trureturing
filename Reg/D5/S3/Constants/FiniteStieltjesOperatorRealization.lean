import D5.S3.Constants.FiniteStieltjesOperatorRealization
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full-telescope source-family audits for the public finite Stieltjes suppliers. -/

namespace Reg.D5.S3.Constants.FiniteStieltjesOperatorRealization
open _root_.D5.S3.Constants.FiniteStieltjesOperatorRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped InnerProductSpace
universe u
noncomputable section

structure FiniteIndex where
  carrier : Type u
  finite : Fintype carrier

attribute [instance] FiniteIndex.finite

namespace Nonnegative
abbrev signature : Signature where
  Params := FiniteIndex.{u}
  State p := p.carrier → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Module.End ℝ (EuclideanSpace ℝ p.carrier)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ node => diagonalOperator node) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => diagonalOperator (fun _ => (-1 : ℝ)))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {ι : Type u} [hι : Fintype ι] (node : ι → ℝ)
    (_hn : ∀ i, 0 ≤ node i),
    IsNonnegativeOperator (O.readout () ⟨ι, hι⟩ node)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance (fun _ => 0) (fun _ => le_rfl)
  have hv := hh (WithLp.toLp 2 (fun _ => (1 : ℝ)))
  norm_num [rejected, realize, diagonalOperator, PiLp.inner_apply, Real.inner_apply] at hv

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro _
  refine ⟨⟨ULift.{u} Unit, inferInstance⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hv := congrArg
    (fun A : Module.End ℝ (EuclideanSpace ℝ (ULift.{u} Unit)) =>
      (A (WithLp.toLp 2 (fun _ => (1 : ℝ)))) (ULift.up ())) he
  norm_num [actual, realize, diagonalOperator] at hv

def family : Registration arena.{u} (type_of% (@diagonal_operator_nonnegative.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonal_operator_nonnegative.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@diagonal_operator_nonnegative.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Constants.FiniteStieltjesOperatorRealization.diagonal_operator_nonnegative.__information_unit
  realizationName := `Reg.D5.S3.Constants.FiniteStieltjesOperatorRealization.Nonnegative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Constants.FiniteStieltjesOperatorRealization
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Nonnegative

namespace Pairing
structure Parameters where
  index : FiniteIndex.{u}
  node : index.carrier → ℝ
  weight : index.carrier → ℝ

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p n => finiteMoment p.node p.weight n) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {ι : Type u} [hι : Fintype ι] (node weight : ι → ℝ)
    (_hw : ∀ i, 0 ≤ weight i) (n : ℕ),
    O.readout () ⟨⟨ι, hι⟩, node, weight⟩ n =
      inner ℝ (((diagonalOperator node)^n) (rootWeightVector weight))
        (rootWeightVector weight)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance (fun _ => 1) (fun _ => 1)
    (fun _ => zero_le_one) 0
  change (0 : ℝ) = inner ℝ
    (rootWeightVector (fun _ : ULift.{u} Unit => (1 : ℝ)))
    (rootWeightVector (fun _ : ULift.{u} Unit => (1 : ℝ))) at hh
  rw [PiLp.inner_apply] at hh
  norm_num [rootWeightVector, Real.inner_apply] at hh

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro _
  refine ⟨⟨⟨ULift.{u} Unit, inferInstance⟩, (fun _ => 2), (fun _ => 1)⟩, 0, 1, ?_⟩
  norm_num [actual, realize, finiteMoment]

def family : Registration arena.{u} (type_of% (@moment_eq_operator_pairing.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moment_eq_operator_pairing.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@moment_eq_operator_pairing.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Constants.FiniteStieltjesOperatorRealization.moment_eq_operator_pairing.__information_unit
  realizationName := `Reg.D5.S3.Constants.FiniteStieltjesOperatorRealization.Pairing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Constants.FiniteStieltjesOperatorRealization
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Pairing
end
end Reg.D5.S3.Constants.FiniteStieltjesOperatorRealization
