/- GID: D5/S3/ConceptDynamics/DagCompletion/DependencyAggregateRecursion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/DependencyAggregateRecursion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Global prerequisite meet and join aggregates satisfy exact local predecessor recursion laws. -/

import D5.S3.ConceptDynamics.DagSemantics.DependencyAggregate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.DependencyAggregateRecursion

open D5.S3.ConceptDynamics.DagSemantics.DependencyAggregate

/-- The prerequisite join equals the local label joined with all predecessor aggregates. -/
theorem prerequisiteJoin_recursion
    {V Label : Type*} [CompleteLattice Label]
    (edge : V → V → Prop) (label : V → Label) (node : V) :
    prerequisiteJoin edge label node =
      label node ⊔
        ⨆ predecessor, ⨆ (_ : edge predecessor node),
          prerequisiteJoin edge label predecessor := by
  apply le_antisymm
  · apply iSup_le
    intro ancestor
    apply iSup_le
    intro path
    rcases path.cases_tail with nodeEq | ⟨predecessor, initialPath, finalEdge⟩
    · subst ancestor
      exact le_sup_left
    · exact calc
        label ancestor ≤ prerequisiteJoin edge label predecessor :=
          le_iSup_of_le ancestor (le_iSup_of_le initialPath le_rfl)
        _ ≤ label node ⊔
              ⨆ predecessor, ⨆ (_ : edge predecessor node),
                prerequisiteJoin edge label predecessor :=
          le_sup_of_le_right
            (le_iSup_of_le predecessor
              (le_iSup_of_le finalEdge le_rfl))
  · apply sup_le
    · exact self_le_prerequisiteJoin edge label node
    · apply iSup_le
      intro predecessor
      apply iSup_le
      intro dependency
      exact prerequisiteJoin_mono
        (Relation.ReflTransGen.single dependency)

/-- The prerequisite meet equals the local label met with all predecessor aggregates. -/
theorem prerequisiteMeet_recursion
    {V Label : Type*} [CompleteLattice Label]
    (edge : V → V → Prop) (label : V → Label) (node : V) :
    prerequisiteMeet edge label node =
      label node ⊓
        ⨅ predecessor, ⨅ (_ : edge predecessor node),
          prerequisiteMeet edge label predecessor := by
  apply le_antisymm
  · apply le_inf
    · exact prerequisiteMeet_le_self edge label node
    · apply le_iInf
      intro predecessor
      apply le_iInf
      intro dependency
      exact prerequisiteMeet_antitone
        (Relation.ReflTransGen.single dependency)
  · apply le_iInf
    intro ancestor
    apply le_iInf
    intro path
    rcases path.cases_tail with nodeEq | ⟨predecessor, initialPath, finalEdge⟩
    · subst ancestor
      exact inf_le_left
    · exact calc
        label node ⊓
              (⨅ predecessor, ⨅ (_ : edge predecessor node),
                prerequisiteMeet edge label predecessor) ≤
            (⨅ predecessor, ⨅ (_ : edge predecessor node),
              prerequisiteMeet edge label predecessor) := inf_le_right
        _ ≤ prerequisiteMeet edge label predecessor :=
          iInf_le_of_le predecessor (iInf_le_of_le finalEdge le_rfl)
        _ ≤ label ancestor :=
          iInf_le_of_le ancestor (iInf_le_of_le initialPath le_rfl)

/-- Pointwise larger local labels produce larger prerequisite joins. -/
theorem prerequisiteJoin_mono_label
    {V Label : Type*} [CompleteLattice Label]
    {edge : V → V → Prop} {first second : V → Label}
    (pointwise : ∀ node, first node ≤ second node) (node : V) :
    prerequisiteJoin edge first node ≤ prerequisiteJoin edge second node := by
  apply iSup_le
  intro ancestor
  apply iSup_le
  intro path
  exact le_iSup_of_le ancestor (le_iSup_of_le path (pointwise ancestor))

/-- Pointwise larger local labels produce larger prerequisite meets. -/
theorem prerequisiteMeet_mono_label
    {V Label : Type*} [CompleteLattice Label]
    {edge : V → V → Prop} {first second : V → Label}
    (pointwise : ∀ node, first node ≤ second node) (node : V) :
    prerequisiteMeet edge first node ≤ prerequisiteMeet edge second node := by
  apply le_iInf
  intro ancestor
  apply le_iInf
  intro path
  exact le_trans
    (iInf_le_of_le ancestor (iInf_le_of_le path le_rfl))
    (pointwise ancestor)

#print axioms prerequisiteJoin_recursion
#print axioms prerequisiteMeet_recursion

end D5.S3.ConceptDynamics.DagCompletion.DependencyAggregateRecursion
