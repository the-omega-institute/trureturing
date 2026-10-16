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
universe u_1 u_2 u_3

namespace Blocks

/-- Evaluate the block-diagonal construction at its source block family. -/
abbrev signature : Signature where
  Params := Σ ι : Type u_1, Σ κ : ι → Type u_2, ∀ i, Matrix (κ i) (κ i) ℂ
  State p := (∀ i, Matrix (p.2.1 i) (p.2.1 i) ℂ) →
    Matrix (Sigma p.2.1) (Sigma p.2.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Sigma p.2.1) (Sigma p.2.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p blockDiagonal => blockDiagonal p.2.2) (fun e => Empty.elim e)

def rejected : Realization signature :=
  realize signature (fun _ p blockDiagonal => -(blockDiagonal p.2.2)) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u_2} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : ∀ i, Matrix (κ i) (κ i) ℂ), (∀ i, (M i).PosSemidef) →
    (R.readout () ⟨ι, ⟨κ, M⟩⟩ Matrix.blockDiagonal').PosSemidef

theorem rejected_law : ¬ arena.{u_1,u_2}.Law rejected := by
  intro h
  let ι := ULift.{u_1} Unit
  let κ : ι → Type u_2 := fun _ => ULift.{u_2} Unit
  have hp := h (ι := ι) (κ := κ) (fun _ => 1) (fun _ => Matrix.PosSemidef.one)
  have hd := hp.diag_nonneg (i := ⟨⟨()⟩, ⟨()⟩⟩)
  norm_num [rejected, realize, Matrix.blockDiagonal'_apply_eq, Complex.le_def] at hd

def source_registration : Registration arena.{u_1,u_2}
    (type_of% @posSemidef_blockDiagonal.{u_1,u_2}) where
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
    refine ⟨⟨ULift.{u_1} Unit, ⟨fun _ => ULift.{u_2} Unit, fun _ => 0⟩⟩,
      (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have he := congrArg (fun M => M ⟨⟨()⟩, ⟨()⟩⟩ ⟨⟨()⟩, ⟨()⟩⟩) h
    change (0 : ℂ) = 1 at he
    exact zero_ne_one he

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@posSemidef_blockDiagonal.{u_1,u_2})
      (Realization signature.{u_1,u_2}) Unit Unit := {
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
  readout := some
    (realize signature (fun _ p blockDiagonal => blockDiagonal p.2.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
    definition := none
    coordinates := #[0, 3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Blocks

namespace PartialTrace

/-- Evaluate the source partial-trace map at its unscaled matrix. -/
abbrev signature : Signature where
  Params := Σ R : Type u_2, Σ A : Type u_3, Matrix (R × A) (R × A) ℂ
  State p := Matrix (p.1 × p.2.1) (p.1 × p.2.1) ℂ → Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p traceRight => traceRight p.2.2) (fun e => Empty.elim e)

def rejected : Realization signature :=
  realize signature (fun _ p traceRight => traceRight p.2.2.transpose) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u_2,u_3}
  Law r := ∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [DistribSMul S ℂ] [Fintype A]
    (c : S) (X : Matrix (R × A) (R × A) ℂ),
    partialTraceRight (c • X) = c • r.readout () ⟨R, ⟨A, X⟩⟩ partialTraceRight

theorem rejected_law : ¬ arena.{u_1,u_2,u_3}.Law rejected := by
  intro h
  let S := ULift.{u_1} ℂ
  let R := ULift.{u_2} Bool
  let A := ULift.{u_3} Unit
  let X : Matrix (R × A) (R × A) ℂ :=
    fun i j => if i.1.down = false ∧ j.1.down = true then 1 else 0
  have he := h (S := S) (R := R) (A := A) (1 : S) X
  change partialTraceRight ((1 : ℂ) • X) = (1 : ℂ) • partialTraceRight X.transpose at he
  simp only [one_smul] at he
  have hx := congrArg (fun M : Matrix R R ℂ => M ⟨false⟩ ⟨true⟩) he
  norm_num [rejected, realize, partialTraceRight, X, Matrix.transpose] at hx

def source_registration : Registration arena.{u_1,u_2,u_3}
    (type_of% @partialTraceRight_smul.{u_1,u_2,u_3}) where
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
    refine ⟨⟨ULift.{u_2} Unit, ⟨ULift.{u_3} Unit, 0⟩⟩,
      (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have he := congrArg (fun M => M ⟨()⟩ ⟨()⟩) h
    change (0 : ℂ) = 1 at he
    exact zero_ne_one he

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@partialTraceRight_smul.{u_1,u_2,u_3})
      (Realization signature.{u_2,u_3}) Unit Unit := {
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
  readout := some
    (realize signature (fun _ p traceRight => traceRight p.2.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
    definition := none
    coordinates := #[1, 2, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end PartialTrace

namespace RatioSets

/-- Evaluate the channel's ratio family at gamma and the orthogonal flag. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ → Bool → Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ γ ratioFamily => ratioFamily γ true) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ γ ratioFamily => (ratioFamily γ true)ᶜ) (fun e => nomatch e)

/-- Retain both universal clauses and observe the orthogonal ratio set. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (A B : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (N : QuantumChannel A B),
    (∀ γ : ℝ, 1 ≤ γ →
      ratios N γ false = r.readout () γ (ratios N)) ∧
    (∀ γ δ : ℝ, 1 ≤ γ → 1 ≤ δ → ratios N γ false = ratios N δ false)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let N : QuantumChannel Unit Unit :=
    { toCompletelyPositiveMap := {
        toLinearMap := LinearMap.id
        map_cstarMatrix_nonneg' := by intro k M hM; simpa using hM }
      trace_preserving := fun _ => rfl }
  have hf := (h Unit Unit N).1 1 le_rfl
  change ratios N 1 false = (ratios N 1 true)ᶜ at hf
  rw [(result Unit Unit N).1 1 le_rfl] at hf
  have hm := Set.ext_iff.mp hf 0
  by_cases hx : 0 ∈ ratios N 1 true
  · exact hm.mp hx hx
  · exact hx (hm.mpr hx)

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, (fun _ _ => ∅), (fun _ _ => Set.univ), ?_⟩
    exact Set.empty_ne_univ

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
  readout := some
    (realize signature (fun _ γ ratioFamily => ratioFamily γ true) (fun e => nomatch e))
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
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end RatioSets

end
end Reg.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
