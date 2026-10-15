import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.CoherentCopyCorrelationTax
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Information.CoherentCopyCorrelationTax
open _root_.D5.S3.Quantum.Information.CoherentCopyCorrelationTax
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Entry

/-- Read the input entry retained between correlated basis vectors. -/
abbrev signature : Signature where
  Params := Σ n : Type u, Σ _a : n × n, n × n
  State p := Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p M => M p.2.1.1 p.2.2.1) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (a b : n × n),
    copyMatrix M a b =
      if a.1 = a.2 then if b.1 = b.2 then R.readout () ⟨n, a, b⟩ M else 0 else 0

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (n := ULift.{u} Unit) 1 (ULift.up (), ULift.up ())
    (ULift.up (), ULift.up ())
  simp [copyMatrix_entry, rejected, realize] at he

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, (ULift.up (), ULift.up ()),
    (ULift.up (), ULift.up ())⟩, 0, (fun _ _ => 1), ?_⟩
  simp [actual, realize]

def source_registration : Registration arena.{u} (type_of% @copyMatrix_entry.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨copyMatrix_entry, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@copyMatrix_entry.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.CoherentCopyCorrelationTax.Entry.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.CoherentCopyCorrelationTax.Entry.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p M => M p.2.1.1 p.2.2.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.CoherentCopyCorrelationTax
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg",
        "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Entry

namespace Marginal

/-- Read the diagonal input entry entering the reduced matrix. -/
abbrev signature : Signature where
  Params := Σ n : Type u, n
  State p := Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p M => M p.2 p.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ),
    partialTraceRight (copyMatrix M) = Matrix.diagonal (fun i => R.readout () ⟨n, i⟩ M)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (n := ULift.{u} Unit) 1
  rw [partialTraceRight_copyMatrix] at he
  have hc := congrArg (fun M : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ =>
    M (ULift.up ()) (ULift.up ())) he
  simp [rejected, realize] at hc

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, ULift.up ()⟩, 0, (fun _ _ => 1), ?_⟩
  simp [actual, realize]

def source_registration : Registration arena.{u} (type_of% @partialTraceRight_copyMatrix.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨partialTraceRight_copyMatrix, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@partialTraceRight_copyMatrix.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.CoherentCopyCorrelationTax.Marginal.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.CoherentCopyCorrelationTax.Marginal.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p M => M p.2 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.CoherentCopyCorrelationTax
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Marginal

end
end Reg.D5.S3.Quantum.Information.CoherentCopyCorrelationTax
