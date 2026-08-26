/- GID: D5/S3/ConceptDynamics/Interpretation/FixedPointMultiplicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interpretation/FixedPointMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Powerset maps exhibit every fixed-point multiplicity and an actuality gap. -/

import Mathlib.Data.Set.BooleanAlgebra

/- Library-search audit trail (2026-08-25):
   * Repository searches for fixed-point multiplicity, unique fixed points,
     actuality, and all-state fixed points found
     `FiniteMonotoneTermination.bool_identity_has_distinct_fixed_point_limits`,
     which covers only a two-point identity example, and no theorem covering
     all clauses of the source atom.
   * The private Boolean no-fixed-point lemma in
     `Computability.Diagonalization.BooleanStreamDiagonal` cannot be imported
     or receipt-bound; this theorem instead uses the pinned public complement
     lemma `compl_ne_self` on the source's powerset carrier.
   * Pinned Mathlib searches for `Function.IsFixedPt`, `compl_ne_self`, and
     unique fixed points found the fixed-point predicate and the exact
     complement separation lemma, but no theorem combining the four
     multiplicity regimes with the actuality countermodel.
   * Body-shape searches for complement, intersection-with-universal, and
     union-with-empty endomorphisms found no existing D5 primitive with the
     construction used below. No new definition or abbreviation is introduced.
   * The source's trailing selector list is qualitative guidance without
     in-scope definitions; the public theorem formalizes the named multiplicity
     and non-implication claims without inventing selector predicates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interpretation.FixedPointMultiplicity

/-- Concrete endomorphisms of powersets realize every fixed-point multiplicity
listed by the source. The multiple-fixed-point example also refutes uniqueness,
while a nonempty actuality predicate disjoint from a unique fixed point shows
that uniqueness alone does not select what is actual. -/
theorem fixed_point_multiplicity_and_actuality_gap :
    (¬ ∃ state : Set Unit,
      Function.IsFixedPt (fun current : Set Unit => currentᶜ) state) ∧
    (∃! state : Set Unit,
      Function.IsFixedPt (fun _current : Set Unit => (∅ : Set Unit)) state) ∧
    (∃ first second : Set Bool,
      first ≠ second ∧
      Function.IsFixedPt
        (fun current : Set Bool => current ∩ {false}) first ∧
      Function.IsFixedPt
        (fun current : Set Bool => current ∩ {false}) second) ∧
    (∀ state : Set Unit,
      Function.IsFixedPt (fun current : Set Unit => current ∪ ∅) state) ∧
    ((∃ state : Set Bool,
        Function.IsFixedPt
          (fun current : Set Bool => current ∩ {false}) state) ∧
      ¬ ∃! state : Set Bool,
        Function.IsFixedPt
          (fun current : Set Bool => current ∩ {false}) state) ∧
    (∃ actual : Set (Set Unit),
      actual.Nonempty ∧
      (∃! state : Set Unit,
        Function.IsFixedPt
          (fun _current : Set Unit => (∅ : Set Unit)) state) ∧
      ∀ state : Set Unit,
        Function.IsFixedPt
            (fun _current : Set Unit => (∅ : Set Unit)) state →
          state ∉ actual) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro fixed
    obtain ⟨state, hstate⟩ := fixed
    exact compl_ne_self hstate
  · refine ⟨∅, ?_, ?_⟩
    · rfl
    · intro state hstate
      exact hstate.symm
  · refine ⟨∅, {false}, Set.empty_ne_singleton false, ?_, ?_⟩ <;>
      simp [Function.IsFixedPt]
  · intro state
    simp [Function.IsFixedPt]
  · constructor
    · exact ⟨∅, by simp [Function.IsFixedPt]⟩
    · intro unique
      obtain ⟨state, _hstate, hunique⟩ := unique
      have hempty : Function.IsFixedPt
          (fun current : Set Bool => current ∩ {false}) ∅ := by
        simp [Function.IsFixedPt]
      have hsingleton : Function.IsFixedPt
          (fun current : Set Bool => current ∩ {false}) {false} := by
        simp [Function.IsFixedPt]
      exact Set.empty_ne_singleton false
        ((hunique ∅ hempty).trans (hunique {false} hsingleton).symm)
  · refine ⟨{Set.univ}, Set.singleton_nonempty Set.univ, ?_, ?_⟩
    · refine ⟨∅, ?_, ?_⟩
      · rfl
      · intro state hstate
        exact hstate.symm
    · intro state hfixed hactual
      change (∅ : Set Unit) = state at hfixed
      have hstate_univ : state = Set.univ := Set.mem_singleton_iff.mp hactual
      exact Set.empty_ne_univ (hfixed.trans hstate_univ)

#print axioms fixed_point_multiplicity_and_actuality_gap

end D5.S3.ConceptDynamics.Interpretation.FixedPointMultiplicity
