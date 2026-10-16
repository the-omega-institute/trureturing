import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
open _root_.D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

namespace DiagonalWeights

set_option linter.checkUnivs false in
/-- Observe a real diagonal coefficient at its original pair of indices. -/
abbrev signature : Signature where
  Params := Σ A : Type u, Σ B : Type v, A × B
  State p := p.1 × p.2.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p r => r p.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit, (ULift.up (), ULift.up ())⟩,
    (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

end DiagonalWeights

namespace Right
open DiagonalWeights

set_option linter.checkUnivs false in
/-- Preserve the complete right marginal identity, observing the input coefficients. -/
abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {A : Type u} {B : Type v} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (r : A × B → ℝ),
    partialTraceRight (diagonal (fun x => (R.readout () ⟨A, B, x⟩ r : ℂ))) =
      diagonal (fun a => ((∑ b, r (a,b) : ℝ) : ℂ))

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have he := h (A := ULift.{u} Unit) (B := ULift.{v} Unit) (fun _ => 1)
  have hc := congrArg (fun M : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ =>
    M (ULift.up ()) (ULift.up ())) he
  norm_num [rejected, realize, partialTraceRight, Matrix.diagonal] at hc

def source_registration : Registration arena.{u,v}
    (type_of% @partialTraceRight_diagonal.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@partialTraceRight_diagonal.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@partialTraceRight_diagonal.{u,v}) (Realization signature.{u,v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.Right.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.Right.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p r => r p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
    definition := none
    coordinates := #[0, 1, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Right

namespace Left
open DiagonalWeights

set_option linter.checkUnivs false in
/-- Preserve the complete left marginal identity, observing the input coefficients. -/
abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {A : Type u} {B : Type v} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (r : A × B → ℝ),
    partialTraceLeft (diagonal (fun x => (R.readout () ⟨A, B, x⟩ r : ℂ))) =
      diagonal (fun b => ((∑ a, r (a,b) : ℝ) : ℂ))

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have he := h (A := ULift.{u} Unit) (B := ULift.{v} Unit) (fun _ => 1)
  have hc := congrArg (fun M : Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ =>
    M (ULift.up ()) (ULift.up ())) he
  norm_num [rejected, realize, partialTraceLeft, Matrix.diagonal] at hc

def source_registration : Registration arena.{u,v}
    (type_of% @partialTraceLeft_diagonal.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@partialTraceLeft_diagonal.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@partialTraceLeft_diagonal.{u,v}) (Realization signature.{u,v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.Left.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.Left.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p r => r p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
    definition := none
    coordinates := #[0, 1, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Left

end
end Reg.D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
