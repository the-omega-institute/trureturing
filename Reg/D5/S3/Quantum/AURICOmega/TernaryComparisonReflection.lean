import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.TernaryComparisonReflection
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
import Reg.Support.DependentFamily

/-! Source-bound audits of reflection sequences in ternary comparison structures.

The model used for the rejected laws and for observational dependence is the two-point structure
with exclusive-or transfer and orthonormal indicator reading. -/

namespace Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonReflection

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonReflection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup (twoPoint featureTrue featureFalse)

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-! Powers of the second point in the group at the first point, for `reflectionSeq_eq_pow`. -/
namespace Power

abbrev signature : Signature where
  Params := Σ M : Type u, Σ _ : TernaryComparison M, Σ _ : M, M
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => (letI := p.2.1.groupAt p.2.2.1; p.2.2.2 ^ s)) (fun e => nomatch e)

def constant : Realization signature.{u} :=
  realize signature (fun _ p _ => p.2.2.2) (fun e => nomatch e)

/-- Retain the complete carrier, structure, point and index telescope of
`reflectionSeq_eq_pow`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} (C : TernaryComparison M) (a b : M) (n : ℕ),
    reflectionSeq C a b n = r.readout () ⟨M, C, a, b⟩ n

theorem rejected_law : ¬ arena.{u}.Law constant := by
  intro h
  have hh := h twoPoint.{u} ⟨false⟩ ⟨true⟩ 0
  revert hh
  decide

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} Bool, twoPoint, ⟨false⟩, ⟨true⟩⟩, 0, 1, ?_⟩
  decide

def source_registration :
    Registration arena.{u} (type_of% @reflectionSeq_eq_pow.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reflectionSeq_eq_pow.{u}, constant, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨constant, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Power

/-! The reading against the starting point, for `kappa_reflectionSeq_add`. -/
namespace Spacing

abbrev signature : Signature where
  Params := Σ M : Type u, Σ _ : TernaryComparison M, M
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.2.1.kappa p.2.2 s) (fun e => nomatch e)

def constant : Realization signature.{u} :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- Retain the complete carrier, structure, point and index telescope of
`kappa_reflectionSeq_add`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} (C : TernaryComparison M) (a b : M) (m n : ℕ),
    C.kappa (reflectionSeq C a b m) (reflectionSeq C a b (m + n)) =
      r.readout () ⟨M, C, a⟩ (reflectionSeq C a b n)

theorem rejected_law : ¬ arena.{u}.Law constant := by
  intro h
  have hh := h twoPoint.{u} ⟨true⟩ ⟨true⟩ 0 0
  rw [Nat.add_zero, TernaryComparison.kappa_self] at hh
  norm_num [constant, realize] at hh

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Bool, twoPoint, ⟨true⟩⟩, ⟨true⟩, ⟨false⟩, ?_⟩
  change twoPoint.kappa ⟨true⟩ ⟨true⟩ ≠ twoPoint.kappa ⟨true⟩ ⟨false⟩
  norm_num [twoPoint, featureTrue, featureFalse]

def source_registration :
    Registration arena.{u} (type_of% @kappa_reflectionSeq_add.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kappa_reflectionSeq_add.{u}, constant, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨constant, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Spacing

def reflectionSeq_eq_pow_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@reflectionSeq_eq_pow.{u}) (Realization Power.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonReflection.reflectionSeq_eq_pow_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonReflection.Power.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Power.arena.{u}⟩
  objectArena := .source ⟨Power.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Power.arena.{u} ⟨Power.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Power.signature.{u}
    (fun _ p s => (letI := p.2.1.groupAt p.2.2.1; p.2.2.2 ^ s)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonReflection
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def kappa_reflectionSeq_add_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@kappa_reflectionSeq_add.{u}) (Realization Spacing.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonReflection.kappa_reflectionSeq_add_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonReflection.Spacing.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Spacing.arena.{u}⟩
  objectArena := .source ⟨Spacing.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Spacing.arena.{u} ⟨Spacing.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Spacing.signature.{u} (fun _ p s => p.2.1.kappa p.2.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonReflection
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonReflection
