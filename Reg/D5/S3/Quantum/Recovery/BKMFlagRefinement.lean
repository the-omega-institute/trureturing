import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Recovery.BKMFlagRefinement

/-! Scalar equality readouts for both physical defects under classical flag refinement. -/

noncomputable section

open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement

namespace Reg.D5.S3.Quantum.Recovery.BKMFlagRefinement

universe u v z

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected (role : Bool) : Realization signature :=
  realize signature (fun j _ x y => if j = role then False else x = y) (fun e => nomatch e)

private theorem rejectOne {law : Realization signature → Prop}
    (h : ∀ role, ¬ law (rejected role)) : Sensitivity ⟨signature, law⟩ actual := by
  constructor
  · intro role
    refine ⟨rejected role, ?_, rfl, h role⟩
    intro j hj
    funext parameter x y
    simp [rejected, actual, realize, hj]
  · intro e
    exact nomatch e

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro equality
  have impossible := congrFun equality 0
  norm_num [actual, realize] at impossible

private theorem unitJointTrace :
    (joint (fun _ : ULift.{v} Unit => (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ))).trace =
      1 := by
  rw [Matrix.trace_blockDiagonal]
  simp [Matrix.trace_one]

namespace Defects

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} {ι : Type v}
    [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    {J : ι → Type z} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1)
    (K : Matrix n n ℂ),
    R.readout false () (logDefect (joint (refinedBlocks w T)) K) (logDefect (joint T) K) ∧
    R.readout true () (bkmGap (joint (refinedBlocks w T)) K) (bkmGap (joint T) K)

private theorem rejected_law (role : Bool) : ¬ arena.{u, v, z}.Law (rejected role) := by
  intro h
  let n := ULift.{u} Unit
  let ι := ULift.{v} Unit
  let T : ι → Matrix n n ℂ := fun _ => 1
  let w : ∀ _ : ι, ULift.{z} Unit → ℝ := fun _ _ => 1
  have result := h (J := fun _ => ULift.{z} Unit) T (fun _ => Matrix.PosDef.one)
    w (fun _ _ => zero_lt_one) (fun _ => by simp [w]) 0
  cases role
  · simpa [rejected, realize] using result.1
  · simpa [rejected, realize] using result.2

def family : Registration arena.{u, v, z} (type_of% @refine_defects.{u, v, z}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@refine_defects.{u, v, z}, rejected false, rejected_law false⟩
  sensitivity := rejectOne rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@refine_defects.{u, v, z}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMFlagRefinement.refine_defects.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMFlagRefinement.Defects.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, z}⟩
  objectArena := .source ⟨arena.{u, v, z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, z} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMFlagRefinement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Defects

namespace Physical

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} {ι : Type v}
    [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    {J : ι → Type z} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)] [Nonempty ι]
    (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef) (htr : (joint T).trace = 1)
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1)
    (K : Matrix n n ℂ) (hK : K.IsHermitian),
    (joint T).PosDef ∧ (joint (refinedBlocks w T)).PosDef ∧
    (joint (refinedBlocks w T)).trace = 1 ∧ (marginal T).PosDef ∧
    (marginal T).trace = 1 ∧ marginal (refinedBlocks w T) = marginal T ∧
    (lift (ι := ι) K).IsHermitian ∧ (lift (ι := Σ i, J i) K).IsHermitian ∧
    R.readout false () (logDefect (joint (refinedBlocks w T)) K) (logDefect (joint T) K) ∧
    R.readout true () (bkmGap (joint (refinedBlocks w T)) K) (bkmGap (joint T) K)

private theorem rejected_law (role : Bool) : ¬ arena.{u, v, z}.Law (rejected role) := by
  intro h
  let n := ULift.{u} Unit
  let ι := ULift.{v} Unit
  let T : ι → Matrix n n ℂ := fun _ => 1
  let w : ∀ _ : ι, ULift.{z} Unit → ℝ := fun _ _ => 1
  have result := h (J := fun _ => ULift.{z} Unit) T (fun _ => Matrix.PosDef.one) unitJointTrace
    w (fun _ _ => zero_lt_one) (fun _ => by simp [w]) 0 Matrix.isHermitian_zero
  cases role
  · simpa [rejected, realize] using result.2.2.2.2.2.2.2.2.1
  · simpa [rejected, realize] using result.2.2.2.2.2.2.2.2.2

def family : Registration arena.{u, v, z} (type_of% @physical_refinement.{u, v, z}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_refinement.{u, v, z}, rejected false, rejected_law false⟩
  sensitivity := rejectOne rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_refinement.{u, v, z}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMFlagRefinement.physical_refinement.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMFlagRefinement.Physical.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, z}⟩
  objectArena := .source ⟨arena.{u, v, z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, z} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMFlagRefinement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Physical

end Reg.D5.S3.Quantum.Recovery.BKMFlagRefinement
