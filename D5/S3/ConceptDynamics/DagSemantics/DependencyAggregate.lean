/- GID: D5/S3/ConceptDynamics/DagSemantics/DependencyAggregate
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DependencyAggregate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Meet and join aggregates over prerequisite cones are antitone and monotone along dependency reachability. -/

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Relation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.DependencyAggregate

/-- The meet of labels over the full prerequisite cone of a node. -/
def prerequisiteMeet
    {V Label : Type*} [CompleteLattice Label]
    (edge : V → V → Prop) (label : V → Label) (node : V) : Label :=
  ⨅ prerequisite, ⨅ (_ : Relation.ReflTransGen edge prerequisite node),
    label prerequisite

/-- The join of labels over the full prerequisite cone of a node. -/
def prerequisiteJoin
    {V Label : Type*} [CompleteLattice Label]
    (edge : V → V → Prop) (label : V → Label) (node : V) : Label :=
  ⨆ prerequisite, ⨆ (_ : Relation.ReflTransGen edge prerequisite node),
    label prerequisite

/-- The meet aggregate is below the node's own label. -/
theorem prerequisiteMeet_le_self
    {V Label : Type*} [CompleteLattice Label]
    (edge : V → V → Prop) (label : V → Label) (node : V) :
    prerequisiteMeet edge label node ≤ label node := by
  exact iInf_le_of_le node
    (iInf_le_of_le Relation.ReflTransGen.refl le_rfl)

/-- The node's own label is below the join aggregate. -/
theorem self_le_prerequisiteJoin
    {V Label : Type*} [CompleteLattice Label]
    (edge : V → V → Prop) (label : V → Label) (node : V) :
    label node ≤ prerequisiteJoin edge label node := by
  exact le_iSup_of_le node
    (le_iSup_of_le Relation.ReflTransGen.refl le_rfl)

/-- Moving downstream enlarges the prerequisite cone, so its meet can only decrease. -/
theorem prerequisiteMeet_antitone
    {V Label : Type*} [CompleteLattice Label]
    {edge : V → V → Prop} {label : V → Label}
    {first second : V}
    (path : Relation.ReflTransGen edge first second) :
    prerequisiteMeet edge label second ≤ prerequisiteMeet edge label first := by
  apply le_iInf
  intro prerequisite
  apply le_iInf
  intro prerequisiteOfFirst
  exact iInf_le_of_le prerequisite
    (iInf_le_of_le (prerequisiteOfFirst.trans path) le_rfl)

/-- Moving downstream enlarges the prerequisite cone, so its join can only increase. -/
theorem prerequisiteJoin_mono
    {V Label : Type*} [CompleteLattice Label]
    {edge : V → V → Prop} {label : V → Label}
    {first second : V}
    (path : Relation.ReflTransGen edge first second) :
    prerequisiteJoin edge label first ≤ prerequisiteJoin edge label second := by
  apply iSup_le
  intro prerequisite
  apply iSup_le
  intro prerequisiteOfFirst
  exact le_iSup_of_le prerequisite
    (le_iSup_of_le (prerequisiteOfFirst.trans path) le_rfl)

/-- Set-valued dependency unions are a specialization of the join aggregate. -/
theorem prerequisiteJoin_set_mono
    {V Atom : Type*} {edge : V → V → Prop} {label : V → Set Atom}
    {first second : V}
    (path : Relation.ReflTransGen edge first second) :
    prerequisiteJoin edge label first ⊆ prerequisiteJoin edge label second :=
  prerequisiteJoin_mono path

#print axioms prerequisiteMeet_antitone
#print axioms prerequisiteJoin_mono

end D5.S3.ConceptDynamics.DagSemantics.DependencyAggregate
