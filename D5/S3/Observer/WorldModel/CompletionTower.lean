/- GID: D5/S3/Observer/WorldModel/CompletionTower
   generality: G
   mirror-B: D5/B/S3/Observer/WorldModel/CompletionTower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coherent fixed threads define truth in a typed completion tower. -/

import D5.S3.Observer.Bridges.WormholeCategory

/-!
A completion tower separates three structures that should not be conflated:

* one state type and one update at each finite level;
* one adjacent semiconjugate bonding map;
* one coherent thread choosing a compatible state at every level.

A truth thread is defined as a thread that is both coherent and fixed at every
level.  The theorem below constructs such a thread from any fixed base state.
This is the precise finite-layer content of the “spiral tower” metaphor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.WorldModel.CompletionTower

open D5.S3.Observer.Bridges.WormholeCategory
open D5.S3.Observer.Bridges.WormholeCategory.Wormhole

universe u

/-- A natural-number-indexed tower of typed dynamical worlds. -/
structure CompletionTower where
  State : ℕ → Type u
  dynamics : ∀ level, State level → State level
  bond : ∀ level, State level → State (level + 1)
  bond_semiconj : ∀ level,
    Function.Semiconj (bond level)
      (dynamics level) (dynamics (level + 1))

namespace CompletionTower

variable (tower : CompletionTower.{u})

/-- One state chosen at every completion level. -/
abbrev Thread := ∀ level, tower.State level

/-- Adjacent choices agree under every bonding map. -/
def IsCoherentThread (thread : tower.Thread) : Prop :=
  ∀ level, tower.bond level (thread level) = thread (level + 1)

/-- Every coordinate is fixed by its local dynamics. -/
def IsFixedThread (thread : tower.Thread) : Prop :=
  ∀ level, Function.IsFixedPt (tower.dynamics level) (thread level)

/-- A cross-layer truth thread is both coherent and locally fixed. -/
def IsTruthThread (thread : tower.Thread) : Prop :=
  tower.IsCoherentThread thread ∧ tower.IsFixedThread thread

/-- Recursively transport one base state through all adjacent bonds. -/
def transportFromBase (base : tower.State 0) : tower.Thread
  | 0 => base
  | level + 1 => tower.bond level (tower.transportFromBase base level)

@[simp] theorem transportFromBase_zero (base : tower.State 0) :
    tower.transportFromBase base 0 = base :=
  rfl

@[simp] theorem transportFromBase_succ
    (base : tower.State 0) (level : ℕ) :
    tower.transportFromBase base (level + 1) =
      tower.bond level (tower.transportFromBase base level) :=
  rfl

/-- The recursively transported thread is coherent by construction. -/
theorem transport_from_base_coherent (base : tower.State 0) :
    tower.IsCoherentThread (tower.transportFromBase base) := by
  intro level
  rfl

/-- Fixedness of one base state propagates to every completion level. -/
theorem transport_from_fixed_base_is_fixed
    {base : tower.State 0}
    (baseFixed :
      Function.IsFixedPt (tower.dynamics 0) base) :
    tower.IsFixedThread (tower.transportFromBase base) := by
  intro level
  induction level with
  | zero =>
      exact baseFixed
  | succ level inductionHypothesis =>
      simpa only [transportFromBase_succ] using
        fixed_point_maps (tower.bond_semiconj level)
          inductionHypothesis

/-- A fixed base state canonically generates a truth thread. -/
theorem transport_from_fixed_base_is_truth
    {base : tower.State 0}
    (baseFixed :
      Function.IsFixedPt (tower.dynamics 0) base) :
    tower.IsTruthThread (tower.transportFromBase base) :=
  ⟨tower.transport_from_base_coherent base,
    tower.transport_from_fixed_base_is_fixed baseFixed⟩

/-- Every coherent thread is determined by its base coordinate. -/
theorem coherent_thread_eq_transport_from_base
    (thread : tower.Thread)
    (coherent : tower.IsCoherentThread thread) :
    thread = tower.transportFromBase (thread 0) := by
  funext level
  induction level with
  | zero =>
      rfl
  | succ level inductionHypothesis =>
      calc
        thread (level + 1) =
            tower.bond level (thread level) :=
          (coherent level).symm
        _ = tower.bond level
            (tower.transportFromBase (thread 0) level) :=
          congrArg (tower.bond level) inductionHypothesis
        _ = tower.transportFromBase (thread 0) (level + 1) :=
          rfl

/-- Two coherent threads with the same base state are equal. -/
theorem coherent_threads_ext
    {first second : tower.Thread}
    (firstCoherent : tower.IsCoherentThread first)
    (secondCoherent : tower.IsCoherentThread second)
    (sameBase : first 0 = second 0) :
    first = second := by
  rw [tower.coherent_thread_eq_transport_from_base first firstCoherent,
    tower.coherent_thread_eq_transport_from_base second secondCoherent,
    sameBase]

#print axioms transport_from_base_coherent
#print axioms transport_from_fixed_base_is_fixed
#print axioms transport_from_fixed_base_is_truth
#print axioms coherent_thread_eq_transport_from_base
#print axioms coherent_threads_ext

end CompletionTower

end D5.S3.Observer.WorldModel.CompletionTower
