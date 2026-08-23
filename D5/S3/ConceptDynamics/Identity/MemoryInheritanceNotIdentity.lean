/- GID: D5/S3/ConceptDynamics/Identity/MemoryInheritanceNotIdentity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identity/MemoryInheritanceNotIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Branching memory inheritance cannot coincide with numerical equality. -/

import Mathlib.Logic.Relator

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'branching_memory_is_not_equality' D5 Golden/Frozen/accepted`
     returned no matches.
   * Repository searches for branching, equality, `AllowsBranching`, and
     `Relator.RightUnique` found no theorem with this claim. The nearby
     `ConceptRelativeIdentity` module treats kernels `q x = q y`; such relations are
     equivalences and cannot express the one-to-many mechanism used here.
   * Pinned Mathlib defines `Relator.RightUnique` in `Mathlib.Logic.Relator`. It is
     reused below as the standard notion contradicted by an explicit branch. No
     upstream theorem directly turns that contradiction into inequality with `Eq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identity.MemoryInheritanceNotIdentity

universe u

/-- A memory relation branches when one predecessor has two distinct successors. -/
def AllowsBranching {Person : Type u} (M : Person -> Person -> Prop) : Prop :=
  exists x y z, M x y /\ M x z /\ Not (y = z)

/-- An explicit memory relation on three people: zero precedes both one and two,
while every person also inherits their own memory. -/
def branchingMemory (a b : Fin 3) : Prop :=
  (a = 0 /\ (b = 1 \/ b = 2)) \/ a = b

/-- An explicit branch contradicts right uniqueness of the memory relation. -/
theorem branching_not_right_unique {Person : Type u} {M : Person -> Person -> Prop}
    (hbranch : AllowsBranching M) : Not (Relator.RightUnique M) := by
  rcases hbranch with ⟨x, y, z, hxy, hxz, hyz⟩
  intro hrightUnique
  exact hyz (hrightUnique hxy hxz)

/-- If memory inheritance permits branching, it cannot coincide with numerical equality. -/
theorem branching_memory_is_not_equality {Person : Type u}
    (M : Person -> Person -> Prop) (hbranch : AllowsBranching M) :
    Not (forall a b, M a b <-> a = b) := by
  intro hequality
  apply branching_not_right_unique hbranch
  intro a b c hab hac
  exact ((hequality a b).mp hab).symm.trans ((hequality a c).mp hac)

example :
    branchingMemory 0 1 /\ branchingMemory 0 2 /\ Not ((1 : Fin 3) = 2) := by
  simp [branchingMemory]

example : Not (forall a b, branchingMemory a b <-> a = b) := by
  apply branching_memory_is_not_equality branchingMemory
  exact ⟨0, 1, 2, by simp [branchingMemory], by simp [branchingMemory], by decide⟩

#print axioms branching_memory_is_not_equality

end D5.S3.ConceptDynamics.Identity.MemoryInheritanceNotIdentity
