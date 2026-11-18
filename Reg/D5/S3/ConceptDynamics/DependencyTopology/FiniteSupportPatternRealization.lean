import D5.S3.ConceptDynamics.DependencyTopology.FiniteSupportPatternRealization
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The source readout retains the full finite carrier and family of the realization theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ConceptDynamics.DependencyTopology.FiniteSupportPatternRealization

open _root_.D5.S3.ConceptDynamics.DependencyTopology
open FiniteSupportPatternRealization LegalLedgerFixedSet SupportFamilyNotIntersectionClosed
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Nat
  State n := Finset (Finset (Fin n))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (Set Formula)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ F => supportFamily (kernel F)) (fun a => nomatch a)

def rejected : Realization signature := realize signature
  (fun _ _ _ => ∅) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {n : Nat} (F : Finset (Finset (Fin n))), Pattern F →
    SourceLaws (kernel F) ∧
      obs.readout () n F = {Y | ∃ A ∈ F, Y = (↑(A.image e) : Set Formula)}

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hp : Pattern ({∅} : Finset (Finset (Fin 0))) := by unfold Pattern; decide
  have he := (h ({∅} : Finset (Finset (Fin 0))) hp).2
  have hem : (∅ : Set Formula) ∈
      {Y | ∃ A ∈ ({∅} : Finset (Finset (Fin 0))), Y = (↑(A.image e) : Set Formula)} :=
    ⟨∅, by simp, by simp⟩
  rw [← he] at hem
  exact hem

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let F₀ : Finset (Finset (Fin 1)) := {∅}
  let F₁ : Finset (Finset (Fin 1)) := {∅, {0}}
  have h₀ : Pattern F₀ := by unfold Pattern; decide
  have h₁ : Pattern F₁ := by unfold Pattern; decide
  refine ⟨1, F₀, F₁, ?_⟩
  change supportFamily (kernel F₀) ≠ supportFamily (kernel F₁)
  rw [(finite_support_pattern_realization F₀ h₀).2,
      (finite_support_pattern_realization F₁ h₁).2]
  intro he
  have present : ({e (0 : Fin 1)} : Set Formula) ∈
      {Y | ∃ A ∈ F₁, Y = (↑(A.image e) : Set Formula)} :=
    ⟨{0}, by simp [F₁], by simp⟩
  rw [← he] at present
  obtain ⟨A, hA, hEq⟩ := present
  have hA0 : A = ∅ := by simpa [F₀] using hA
  subst A
  simpa using congrArg (fun s : Set Formula => e (0 : Fin 1) ∈ s) hEq

def family : Registration arena (type_of% @finite_support_pattern_realization) where
  actual := realize signature actual.readout actual.anchor
  bridge := Iff.rfl
  variation := ⟨@finite_support_pattern_realization, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := actual_dependence

def registration : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@finite_support_pattern_realization) (Realization signature)
    Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.DependencyTopology.FiniteSupportPatternRealization.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.DependencyTopology.FiniteSupportPatternRealization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.DependencyTopology.FiniteSupportPatternRealization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end
end Reg.D5.S3.ConceptDynamics.DependencyTopology.FiniteSupportPatternRealization
