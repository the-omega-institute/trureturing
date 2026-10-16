import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.checkUnivs false
noncomputable section
universe u v w

namespace Blocks

/-- The block family occurring in the positive-semidefinite conclusion. -/
abbrev signature : Signature where
  Params := Σ ι : Type u, ι → Type v
  State p := ∀ i, Matrix (p.2 i) (p.2 i) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ∀ i, Matrix (p.2 i) (p.2 i) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ M i => -(M i)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type v} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : ∀ i, Matrix (κ i) (κ i) ℂ), (∀ i, (M i).PosSemidef) →
    (Matrix.blockDiagonal' (R.readout () ⟨ι, κ⟩ M)).PosSemidef

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let ι := ULift.{u} Unit
  let κ : ι → Type v := fun _ => ULift.{v} Unit
  have hp := h (ι := ι) (κ := κ) (fun _ => 1) (fun _ => Matrix.PosSemidef.one)
  have hd := hp.diag_nonneg (i := ⟨⟨()⟩, ⟨()⟩⟩)
  norm_num [rejected, realize, Matrix.blockDiagonal'_apply_eq, Complex.le_def] at hd

def source_registration : Registration arena.{u,v}
    (type_of% @posSemidef_blockDiagonal.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨posSemidef_blockDiagonal, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Unit, fun _ => ULift.{v} Unit⟩,
      (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have he := congrArg (fun M => M ⟨()⟩ ⟨()⟩ ⟨()⟩) h
    change (0 : ℂ) = 1 at he
    exact zero_ne_one he

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@posSemidef_blockDiagonal.{u,v})
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.Blocks.unit
  realizationName :=
    .str `Reg.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.Blocks
      "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Blocks

namespace PartialTrace

/-- The matrix operand in the partial trace on the left side. -/
abbrev signature : Signature where
  Params := Σ _R : Type v, Type w
  State p := Matrix (p.1 × p.2) (p.1 × p.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.1 × p.2) (p.1 × p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ X => X.transpose) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v,w}
  Law r := ∀ {S : Type u} {R : Type v} {A : Type w} [DistribSMul S ℂ] [Fintype A]
    (c : S) (X : Matrix (R × A) (R × A) ℂ),
    partialTraceRight (c • r.readout () ⟨R, A⟩ X) = c • partialTraceRight X

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S := ULift.{u} ℂ
  let R := ULift.{v} Bool
  let A := ULift.{w} Unit
  let X : Matrix (R × A) (R × A) ℂ :=
    fun i j => if i.1.down = false ∧ j.1.down = true then 1 else 0
  have he := h (S := S) (R := R) (A := A) (1 : S) X
  have hx := congrArg (fun M : Matrix R R ℂ => M ⟨false⟩ ⟨true⟩) he
  norm_num [rejected, realize, partialTraceRight, X, Matrix.transpose] at hx

def source_registration : Registration arena.{u,v,w}
    (type_of% @partialTraceRight_smul.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨partialTraceRight_smul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{v} Unit, ULift.{w} Unit⟩, 0, 1, ?_⟩
    intro h
    have he := congrArg (fun M => M (⟨()⟩, ⟨()⟩) (⟨()⟩, ⟨()⟩)) h
    change (0 : ℂ) = 1 at he
    exact zero_ne_one he

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@partialTraceRight_smul.{u,v,w})
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.PartialTrace.unit
  realizationName :=
    .str `Reg.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.PartialTrace
      "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end PartialTrace

namespace RatioSets

/-- Equality with a contextual comparison set is an observation of a ratio set. -/
abbrev signature : Signature where
  Params := Set ℝ
  State _ := Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ S T => decide (S = T)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Both universal clauses are retained, observing the orthogonal-set equality. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (A B : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (N : QuantumChannel A B),
    (∀ γ : ℝ, 1 ≤ γ →
      r.readout () (ratios N γ false) (ratios N γ true) = true) ∧
    (∀ γ δ : ℝ, 1 ≤ γ → 1 ≤ δ → ratios N γ false = ratios N δ false)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let N : QuantumChannel Unit Unit :=
    { toCompletelyPositiveMap := {
        toLinearMap := LinearMap.id
        map_cstarMatrix_nonneg' := by intro k M hM; simpa using hM }
      trace_preserving := fun _ => rfl }
  have hf := (h Unit Unit N).1 1 le_rfl
  change false = true at hf
  cases hf

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp only [actual, realize, claim, decide_eq_true_eq]
  variation := ⟨by
    intro A B _ _ _ _ N
    exact ⟨fun γ hγ => decide_eq_true ((result A B N).1 γ hγ), (result A B N).2⟩,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨∅, ∅, Set.univ, ?_⟩
    simp [actual, realize, Set.empty_ne_univ]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.RatioSets.unit
  realizationName :=
    .str `Reg.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.RatioSets
      "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
    definition := some {
      owner := `D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
      name := `D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end RatioSets

end
end Reg.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
