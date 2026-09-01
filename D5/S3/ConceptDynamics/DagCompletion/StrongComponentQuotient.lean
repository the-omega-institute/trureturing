/- GID: D5/S3/ConceptDynamics/DagCompletion/StrongComponentQuotient
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/StrongComponentQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quotienting a directed relation by mutual reachability yields a partial order of strong components. -/

import D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure
import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.ConceptDynamics.DagCompletion.StrongComponentQuotient

open D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

/-- Two vertices lie in the same strong component when each reaches the other. -/
def MutuallyReachable {V : Type u}
    (edge : V → V → Prop) (first second : V) : Prop :=
  Reachable edge first second ∧ Reachable edge second first

/-- Mutual reachability is an equivalence relation. -/
theorem mutuallyReachable_equivalence
    {V : Type u} (edge : V → V → Prop) :
    Equivalence (MutuallyReachable edge) := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex
    exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  · intro first second sameComponent
    exact ⟨sameComponent.2, sameComponent.1⟩
  · intro first second third firstSecond secondThird
    exact ⟨firstSecond.1.trans secondThird.1,
      secondThird.2.trans firstSecond.2⟩

/-- The setoid of strong components. -/
def strongComponentSetoid {V : Type u}
    (edge : V → V → Prop) : Setoid V where
  r := MutuallyReachable edge
  iseqv := mutuallyReachable_equivalence edge

/-- Vertices modulo mutual reachability. -/
def StrongComponent {V : Type u} (edge : V → V → Prop) : Type u :=
  Quotient (strongComponentSetoid edge)

/-- Reachability descends to strong components. -/
def componentReachable {V : Type u} (edge : V → V → Prop) :
    StrongComponent edge → StrongComponent edge → Prop :=
  Quotient.lift₂
    (fun first second => Reachable edge first second)
    (by
      intro first second first' second' sameFirst sameSecond
      apply propext
      constructor
      · intro path
        exact sameFirst.2.trans (path.trans sameSecond.1)
      · intro path
        exact sameFirst.1.trans (path.trans sameSecond.2))

/-- Component reachability is reflexive. -/
theorem componentReachable_refl
    {V : Type u} (edge : V → V → Prop)
    (component : StrongComponent edge) :
    componentReachable edge component component := by
  refine Quotient.inductionOn component ?_
  intro vertex
  exact Relation.ReflTransGen.refl

/-- Component reachability is transitive. -/
theorem componentReachable_trans
    {V : Type u} (edge : V → V → Prop)
    {first second third : StrongComponent edge}
    (firstSecond : componentReachable edge first second)
    (secondThird : componentReachable edge second third) :
    componentReachable edge first third := by
  revert firstSecond secondThird
  refine Quotient.inductionOn₃ first second third ?_
  intro firstVertex secondVertex thirdVertex firstSecond secondThird
  exact firstSecond.trans secondThird

/-- Component reachability is antisymmetric. -/
theorem componentReachable_antisymm
    {V : Type u} (edge : V → V → Prop)
    {first second : StrongComponent edge}
    (firstSecond : componentReachable edge first second)
    (secondFirst : componentReachable edge second first) :
    first = second := by
  revert firstSecond secondFirst
  refine Quotient.inductionOn₂ first second ?_
  intro firstVertex secondVertex firstSecond secondFirst
  exact Quotient.sound ⟨firstSecond, secondFirst⟩

instance strongComponentLE {V : Type u} {edge : V → V → Prop} :
    LE (StrongComponent edge) :=
  ⟨componentReachable edge⟩

instance strongComponentPartialOrder {V : Type u} {edge : V → V → Prop} :
    PartialOrder (StrongComponent edge) where
  le_refl := componentReachable_refl edge
  le_trans := by
    intro first second third
    exact componentReachable_trans edge
  le_antisymm := by
    intro first second
    exact componentReachable_antisymm edge

/-- The quotient map is monotone for reachability. -/
theorem quotient_mono
    {V : Type u} (edge : V → V → Prop)
    {first second : V} (path : Reachable edge first second) :
    componentReachable edge
      (Quotient.mk _ first) (Quotient.mk _ second) :=
  path

/-- Strict component reachability is acyclic. -/
theorem no_strict_component_cycle
    {V : Type u} (edge : V → V → Prop)
    (component : StrongComponent edge) :
    ¬ Relation.TransGen
        (fun first second : StrongComponent edge =>
          componentReachable edge first second ∧
            ¬ componentReachable edge second first)
        component component := by
  intro cycle
  let strictReach := fun first second : StrongComponent edge =>
    componentReachable edge first second ∧
      ¬ componentReachable edge second first
  letI : IsTrans (StrongComponent edge) strictReach :=
    ⟨fun first second third firstSecond secondThird =>
      ⟨componentReachable_trans edge firstSecond.1 secondThird.1,
        fun thirdFirst => firstSecond.2
          (componentReachable_trans edge secondThird.1 thirdFirst)⟩⟩
  have selfStrict : strictReach component component :=
    Relation.transGen_minimal (r := strictReach) (r' := strictReach)
      (fun _ _ step => step) component component cycle
  exact selfStrict.2 selfStrict.1

#print axioms componentReachable_antisymm
#print axioms no_strict_component_cycle

end D5.S3.ConceptDynamics.DagCompletion.StrongComponentQuotient
