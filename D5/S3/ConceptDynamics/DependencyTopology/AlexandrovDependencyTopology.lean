/- GID: D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Upper sets form the dependency Alexandrov topology with principal opens and downset closures. -/

import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
import Mathlib.Topology.Inseparable

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib provides specialization and closure characterizations but no
     repository-specific upper-set topology for dependency reachability.
   * Repository searches found no accepted principal-open, singleton-closure,
     ideal, and filter package for an arbitrary preorder. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.AlexandrovDependencyTopology
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

def upperSetTopology {V : Type*} (relation : V -> V -> Prop)
    [Std.Refl relation] [IsTrans V relation] : TopologicalSpace V where
  IsOpen set := forall ⦃x y⦄, x ∈ set -> relation x y -> y ∈ set
  isOpen_univ := by intro x y _ _; exact Set.mem_univ y
  isOpen_inter := by
    intro first second firstOpen secondOpen x y hx hxy
    exact ⟨firstOpen hx.1 hxy, secondOpen hx.2 hxy⟩
  isOpen_sUnion := by
    intro family familyOpen x y hx hxy
    rcases Set.mem_sUnion.mp hx with ⟨member, memberInFamily, xInMember⟩
    exact Set.mem_sUnion_of_mem (familyOpen member memberInFamily xInMember hxy)
      memberInFamily

def upset {V : Type*} (relation : V -> V -> Prop) (x : V) : Set V :=
  {y | relation x y}

def downset {V : Type*} (relation : V -> V -> Prop) (x : V) : Set V :=
  {y | relation y x}

theorem upset_isOpen
    {V : Type*} (relation : V -> V -> Prop)
    [Std.Refl relation] [IsTrans V relation] (x : V) :
    @IsOpen V (upperSetTopology relation) (upset relation x) := by
  intro y z hy hyz
  exact IsTrans.trans x y z hy hyz

theorem upset_minimal_open
    {V : Type*} (relation : V -> V -> Prop)
    [Std.Refl relation] [IsTrans V relation] {x : V} {set : Set V}
    (setOpen : @IsOpen V (upperSetTopology relation) set) (xInSet : x ∈ set) :
    upset relation x ⊆ set := by
  intro y hxy
  exact setOpen xInSet hxy

theorem specializes_iff_reverse
    {V : Type*} (relation : V -> V -> Prop)
    [Std.Refl relation] [IsTrans V relation] (x y : V) :
    @Specializes V (upperSetTopology relation) x y <-> relation y x := by
  letI : TopologicalSpace V := upperSetTopology relation
  rw [specializes_iff_forall_open]
  constructor
  · intro specializes
    have yInUpset : y ∈ upset relation y := by exact refl y
    exact specializes (upset relation y) (upset_isOpen relation y) yInUpset
  · intro hyx set setOpen yInSet
    exact setOpen yInSet hyx

theorem closure_singleton_eq_downset
    {V : Type*} (relation : V -> V -> Prop)
    [Std.Refl relation] [IsTrans V relation] (x : V) :
    @closure V (upperSetTopology relation) {x} = downset relation x := by
  letI : TopologicalSpace V := upperSetTopology relation
  ext y
  change (y ∈ closure ({x} : Set V)) <-> relation y x
  rw [← specializes_iff_mem_closure]
  exact specializes_iff_reverse relation x y

theorem downset_mono
    {V : Type*} {relation : V -> V -> Prop}
    [Std.Refl relation] [IsTrans V relation] {x y : V} (hxy : relation x y) :
    downset relation x ⊆ downset relation y := by
  intro z hzx
  exact IsTrans.trans z x y hzx hxy

theorem upset_antitone
    {V : Type*} {relation : V -> V -> Prop}
    [Std.Refl relation] [IsTrans V relation] {x y : V} (hxy : relation x y) :
    upset relation y ⊆ upset relation x := by
  intro z hyz
  exact IsTrans.trans x y z hxy hyz

def dependencyTopology {V : Type*} (edge : V -> V -> Prop) : TopologicalSpace V :=
  upperSetTopology (Reachable edge)

#print axioms closure_singleton_eq_downset
#print axioms downset_mono
end D5.S3.ConceptDynamics.DependencyTopology.AlexandrovDependencyTopology
