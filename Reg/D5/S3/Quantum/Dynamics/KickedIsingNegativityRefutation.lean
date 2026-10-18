import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
open _root_.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace JointMatrix

/-- Observe the joint matrix entering the reduced-state expression. -/
abbrev signature : Signature where
  Params := Σ _a : Type, Type
  State p := Matrix (p.1 × p.2) (p.1 × p.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.1 × p.2) (p.1 × p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ρ => ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Unit, Unit⟩, 0, 1, ?_⟩
  intro he
  have hc := congrArg (fun M : Matrix (Unit × Unit) (Unit × Unit) ℂ => M ((), ()) ((), ())) he
  change (0 : ℂ) = 1 at hc
  norm_num at hc

end JointMatrix

namespace ConjugateRight

abbrev signature := JointMatrix.signature
abbrev actual := JointMatrix.actual
abbrev rejected := JointMatrix.rejected
abbrev dependence := JointMatrix.dependence

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (V : Matrix b b ℂ) (_hV : Vᴴ * V = 1),
    partialTraceRight (((1 : Matrix a a ℂ) ⊗ₖ V) * ρ *
      ((1 : Matrix a a ℂ) ⊗ₖ V)ᴴ) = partialTraceRight (R.readout () ⟨a, b⟩ ρ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (a := Unit) (b := Unit) 1 1 (by simp)
  have hc := congrArg (fun M : Matrix Unit Unit ℂ => M () ()) he
  norm_num [rejected, JointMatrix.rejected, realize, partialTraceRight,
    Matrix.one_kronecker_one] at hc
  change (1 : ℂ) = 0 at hc
  norm_num at hc

def source_registration : Registration arena (type_of% @trace_conjugate_right) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_conjugate_right, rejected, rejected_law⟩
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
      (@trace_conjugate_right) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.ConjugateRight.unit
  realizationName := Lean.Name.str
    (Lean.Name.str
      `Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
      "ConjugateRight") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ConjugateRight

namespace ConjugateLeft

abbrev signature := JointMatrix.signature
abbrev actual := JointMatrix.actual
abbrev rejected := JointMatrix.rejected
abbrev dependence := JointMatrix.dependence

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (U : Matrix a a ℂ),
    partialTraceRight ((U ⊗ₖ (1 : Matrix b b ℂ)) * ρ *
      (U ⊗ₖ (1 : Matrix b b ℂ))ᴴ) =
      U * partialTraceRight (R.readout () ⟨a, b⟩ ρ) * Uᴴ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (a := Unit) (b := Unit) 1 1
  have hc := congrArg (fun M : Matrix Unit Unit ℂ => M () ()) he
  norm_num [rejected, JointMatrix.rejected, realize, partialTraceRight,
    Matrix.one_kronecker_one] at hc
  change (1 : ℂ) = 0 at hc
  norm_num at hc

def source_registration : Registration arena (type_of% @trace_conjugate_left) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_conjugate_left, rejected, rejected_law⟩
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
      (@trace_conjugate_left) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.ConjugateLeft.unit
  realizationName := Lean.Name.str
    (Lean.Name.str
      `Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
      "ConjugateLeft") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ConjugateLeft

namespace LocalRight

abbrev signature := JointMatrix.signature
abbrev actual := JointMatrix.actual
abbrev rejected := JointMatrix.rejected
abbrev dependence := JointMatrix.dependence

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (U : Matrix a a ℂ) (V : Matrix b b ℂ) (_hV : Vᴴ * V = 1),
    partialTraceRight ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) =
      U * partialTraceRight (R.readout () ⟨a, b⟩ ρ) * Uᴴ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (a := Unit) (b := Unit) 1 1 1 (by simp)
  have hc := congrArg (fun M : Matrix Unit Unit ℂ => M () ()) he
  norm_num [rejected, JointMatrix.rejected, realize, partialTraceRight,
    Matrix.one_kronecker_one] at hc
  change (1 : ℂ) = 0 at hc
  norm_num at hc

def source_registration : Registration arena (type_of% @trace_local_right) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_local_right, rejected, rejected_law⟩
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
      (@trace_local_right) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.LocalRight.unit
  realizationName := Lean.Name.str
    (Lean.Name.str
      `Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
      "LocalRight") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end LocalRight

namespace LocalLeft

abbrev signature := JointMatrix.signature
abbrev actual := JointMatrix.actual
abbrev rejected := JointMatrix.rejected
abbrev dependence := JointMatrix.dependence

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (U : Matrix a a ℂ) (V : Matrix b b ℂ) (_hU : Uᴴ * U = 1),
    partialTraceLeft ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) =
      V * partialTraceLeft (R.readout () ⟨a, b⟩ ρ) * Vᴴ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (a := Unit) (b := Unit) 1 1 1 (by simp)
  have hc := congrArg (fun M : Matrix Unit Unit ℂ => M () ()) he
  norm_num [rejected, JointMatrix.rejected, realize, partialTraceLeft,
    Matrix.one_kronecker_one] at hc
  change (1 : ℂ) = 0 at hc
  norm_num at hc

def source_registration : Registration arena (type_of% @trace_local_left) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_local_left, rejected, rejected_law⟩
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
      (@trace_local_left) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.LocalLeft.unit
  realizationName := Lean.Name.str
    (Lean.Name.str
      `Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
      "LocalLeft") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end LocalLeft

namespace PartialTransposeKroneckerConj

/-- Observe the partial transpose after local conjugation. -/
abbrev signature : Signature where
  Params := Σ _ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, Matrix (Fin 2) (Fin 2) ℂ
  State _ := Matrix (Fin 2) (Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

open _root_.D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
  (partialTransposeB)

def actual : Realization signature :=
  realize signature
    (fun _ p V => partialTransposeB ((p.2 ⊗ₖ V) * p.1 * (p.2 ⊗ₖ V)ᴴ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ),
    R.readout () ⟨ρ, U⟩ V =
      (U ⊗ₖ V.map star) * partialTransposeB ρ * (U ⊗ₖ V.map star)ᴴ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 1 1
  have hc := congrArg (fun M => M (0, 0) (0, 0)) he
  norm_num [rejected, realize, partialTransposeB] at hc
  change (1 : ℂ) = 0 at hc
  exact one_ne_zero hc

def source_registration : Registration arena (type_of% @partialTransposeB_kronecker_conj) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨partialTransposeB_kronecker_conj, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
    intro he
    have hc := congrArg (fun M => M (0, 0) (0, 0)) he
    norm_num [actual, realize, Matrix.one_kronecker_one, partialTransposeB] at hc

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@partialTransposeB_kronecker_conj) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.PartialTransposeKroneckerConj.unit
  realizationName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
      "PartialTransposeKroneckerConj") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p V => partialTransposeB ((p.2 ⊗ₖ V) * p.1 * (p.2 ⊗ₖ V)ᴴ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end PartialTransposeKroneckerConj

end
end Reg.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
