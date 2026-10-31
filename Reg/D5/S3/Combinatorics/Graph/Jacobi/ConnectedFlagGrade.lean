import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Jacobi.ConnectedFlagGrade
import Reg.Support.DependentFamily

/-! A full-source truth-readout attempt for the quotient-inclusion theorem.
All exact grades, including degenerate fibers, remain in the source. The
chosen injectivity-conclusion readout is true throughout this legal family,
so it lacks actual observational dependence. This excludes only this readout
and does not establish impossibility of a different encoding. No validated
registration is claimed; audit remains unfinished under #24489. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Jacobi.ConnectedFlagGrade

open _root_.D5.S3.Combinatorics.Graph.Jacobi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Source where
  grade : FlagGrade

abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ s => Function.Injective (gradeInclusion s.grade))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Source, R.readout () () s

def originalStatement : Prop :=
  ∀ k : FlagGrade, Function.Injective (gradeInclusion k)

theorem exact_source_bridge : originalStatement ↔ arena.Law actual := by
  constructor
  · intro h s
    exact h s.grade
  · intro h k
    exact h ⟨k⟩

theorem actual_law : arena.Law actual := by
  intro s
  exact gradeInclusion_injective s.grade

theorem selected_source_has_no_observational_dependence :
    ¬ ObservationalDependence signature actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  cases p
  apply hxy
  exact propext ⟨fun _ => actual_law y, fun _ => actual_law x⟩

theorem selected_source_has_no_registration :
    ¬ ∃ R : Registration arena originalStatement, R.actual = actual := by
  rintro ⟨R, he⟩
  exact selected_source_has_no_observational_dependence (he ▸ R.dependence)

end Reg.D5.S3.Combinatorics.Graph.Jacobi.ConnectedFlagGrade
