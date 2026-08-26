/- GID: D5/S3/ConceptDynamics/DependencyTopology/AlexandrovInseparability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/AlexandrovInseparability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Upper-Alexandrov inseparability is mutual reachability and antisymmetry. -/

import D5.S3.ConceptDynamics.DependencyTopology.AlexandrovDependencyTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.AlexandrovInseparability

open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
open D5.S3.ConceptDynamics.DependencyTopology.AlexandrovDependencyTopology

/-- Two points of an upper Alexandrov space are topologically inseparable
exactly when they are mutually related. -/
theorem upper_inseparable_iff_mutual
    {V : Type*} (relation : V → V → Prop)
    [Std.Refl relation] [IsTrans V relation] (x y : V) :
    @Inseparable V (upperSetTopology relation) x y ↔
      relation x y ∧ relation y x := by
  letI : TopologicalSpace V := upperSetTopology relation
  constructor
  · intro inseparable
    have xInUpsetX : x ∈ upset relation x := Std.Refl.refl x
    have yInUpsetY : y ∈ upset relation y := Std.Refl.refl y
    have yInUpsetX : y ∈ upset relation x :=
      (inseparable.mem_open_iff (upset_isOpen relation x)).mp xInUpsetX
    have xInUpsetY : x ∈ upset relation y :=
      (inseparable.mem_open_iff (upset_isOpen relation y)).mpr yInUpsetY
    exact ⟨yInUpsetX, xInUpsetY⟩
  · rintro ⟨hxy, hyx⟩
    rw [inseparable_iff_forall_isOpen]
    intro set setOpen
    constructor
    · intro xInSet
      exact setOpen xInSet hxy
    · intro yInSet
      exact setOpen yInSet hyx

/-- Antisymmetry is exactly the statement that upper-Alexandrov
inseparability collapses to equality. -/
theorem antisymmetric_iff_inseparable_eq
    {V : Type*} (relation : V → V → Prop)
    [Std.Refl relation] [IsTrans V relation] :
    (∀ ⦃x y⦄, relation x y → relation y x → x = y) ↔
      ∀ x y, @Inseparable V (upperSetTopology relation) x y → x = y := by
  constructor
  · intro antisymmetric x y inseparable
    exact antisymmetric
      ((upper_inseparable_iff_mutual relation x y).1 inseparable).1
      ((upper_inseparable_iff_mutual relation x y).1 inseparable).2
  · intro inseparableEq x y hxy hyx
    apply inseparableEq x y
    exact (upper_inseparable_iff_mutual relation x y).2 ⟨hxy, hyx⟩

/-- Acyclic dependency reachability is point-separating in its upper
Alexandrov topology. -/
theorem dependency_inseparable_implies_eq_of_acyclic
    {V : Type*} {edge : V → V → Prop} (acyclic : AcyclicEdge edge)
    (x y : V)
    (inseparable : @Inseparable V (dependencyTopology edge) x y) :
    x = y := by
  apply reachable_antisymm_of_acyclic acyclic
  · exact ((upper_inseparable_iff_mutual (Reachable edge) x y).1
      inseparable).1
  · exact ((upper_inseparable_iff_mutual (Reachable edge) x y).1
      inseparable).2

#print axioms upper_inseparable_iff_mutual
#print axioms dependency_inseparable_implies_eq_of_acyclic

end D5.S3.ConceptDynamics.DependencyTopology.AlexandrovInseparability
