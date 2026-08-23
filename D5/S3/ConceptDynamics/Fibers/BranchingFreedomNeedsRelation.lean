/- GID: D5/S3/ConceptDynamics/Fibers/BranchingFreedomNeedsRelation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/BranchingFreedomNeedsRelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A process with two distinct futures cannot be represented by a function. -/

import Mathlib.Data.Set.Insert

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'branching_process_is_not_functional' D5 Golden/Frozen/accepted`
     returned no matches.
   * Repository searches for `RightUnique`, `AllowsBranching`, `singleton`, and
     `functional` found `Identity.MemoryInheritanceNotIdentity.branching_not_right_unique`
     and `branching_memory_is_not_equality`. They rule out right uniqueness and the
     identity relation, respectively; neither rules out representation by an arbitrary
     function or supplies the Boolean set-valued witnesses required here.
   * Pinned Mathlib defines `Set.mem_singleton_iff` in `Mathlib.Data.Set.Insert`; it is
     reused to collapse two alleged futures of a functional process. No direct theorem
     combining an explicit branch with arbitrary functional representation was found.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.BranchingFreedomNeedsRelation

universe u v

/-- A set-valued process branches when one state has two distinct possible futures. -/
def BranchingFree {X : Type u} (F : X -> Set X) : Prop :=
  exists a b c, b ∈ F a /\ c ∈ F a /\ b ≠ c

/-- A process family is autonomous when two distinct external inputs induce the same
state transition relation. -/
def AutonomousFree {External : Type v} {X : Type u}
    (P : External -> X -> Set X) : Prop :=
  exists e₁ e₂, e₁ ≠ e₂ /\ P e₁ = P e₂

/-- Branching freedom strengthens autonomy by requiring an externally insensitive
process family to admit two distinct futures under some external input. -/
def BranchingAutonomousFree {External : Type v} {X : Type u}
    (P : External -> X -> Set X) : Prop :=
  AutonomousFree P /\ exists e, BranchingFree (P e)

/-- A process with two distinct futures cannot be represented by any deterministic
state-transition function. Unlike the earlier memory result, this excludes every
function graph, not only the identity relation. -/
theorem branching_process_is_not_functional {X : Type u} (F : X -> Set X)
    (hBranch : BranchingFree F) :
    Not (exists f : X -> X, forall a, F a = {f a}) := by
  rcases hBranch with ⟨a, b, c, hb, hc, hne⟩
  rintro ⟨f, hFunction⟩
  rw [hFunction a] at hb hc
  apply hne
  exact (Set.mem_singleton_iff.mp hb).trans (Set.mem_singleton_iff.mp hc).symm

/-- The singleton-valued process induced by any function has no branch. -/
theorem functional_process_is_not_branching {X : Type u} (f : X -> X) :
    Not (BranchingFree (fun a => ({f a} : Set X))) := by
  intro hBranch
  exact branching_process_is_not_functional _ hBranch ⟨f, fun _ => rfl⟩

/-- Branching autonomy strictly strengthens autonomy: it implies external
insensitivity, while the deterministic identity process is autonomous without
branching. -/
theorem branching_freedom_strictly_stronger_than_autonomy :
    (forall {External : Type v} {X : Type u} (P : External -> X -> Set X),
      BranchingAutonomousFree P -> AutonomousFree P) /\
    (exists P : Bool -> Bool -> Set Bool,
      AutonomousFree P /\ Not (BranchingAutonomousFree P)) := by
  constructor
  · intro External X P hBranching
    exact hBranching.1
  · refine ⟨fun _ state => {state}, ?_, ?_⟩
    · exact ⟨false, true, Bool.false_ne_true, rfl⟩
    · rintro ⟨_, external, hBranch⟩
      exact functional_process_is_not_branching (fun state : Bool => state) hBranch

example :
    BranchingFree (fun _ : Bool => (Set.univ : Set Bool)) /\
      Not (exists f : Bool -> Bool, forall a, Set.univ = ({f a} : Set Bool)) := by
  have hBranch : BranchingFree (fun _ : Bool => (Set.univ : Set Bool)) :=
    ⟨false, false, true, Set.mem_univ false, Set.mem_univ true, Bool.false_ne_true⟩
  exact ⟨hBranch, branching_process_is_not_functional _ hBranch⟩

example (f : Bool -> Bool) :
    Not (BranchingFree (fun a => ({f a} : Set Bool))) := by
  exact functional_process_is_not_branching f

#print axioms branching_process_is_not_functional

end D5.S3.ConceptDynamics.Fibers.BranchingFreedomNeedsRelation
