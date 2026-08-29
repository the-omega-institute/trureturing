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

open D5.S3.Observer.Bridges.FixedPointSemiconjugacy

universe u

/-- A natural-number-indexed tower of typed dynamical worlds. -/
structure Tower where
  State : ℕ → Type u
  dynamics : ∀ level, State level → State level
  bond : ∀ level, State level → State (level + 1)
  bond_semiconj : ∀ level,
    Function.Semiconj (bond level)
      (dynamics level) (dynamics (level + 1))

/-- One state chosen at every completion level. -/
abbrev Thread (tower : Tower.{u}) :=
  ∀ level, tower.State level

/-- Adjacent choices agree under every bonding map. -/
def IsCoherentThread (tower : Tower.{u})
    (thread : Thread tower) : Prop :=
  ∀ level, tower.bond level (thread level) = thread (level + 1)

/-- Every coordinate is fixed by its local dynamics. -/
def IsFixedThread (tower : Tower.{u})
    (thread : Thread tower) : Prop :=
  ∀ level, Function.IsFixedPt (tower.dynamics level) (thread level)

/-- A cross-layer truth thread is both coherent and locally fixed. -/
def IsTruthThread (tower : Tower.{u})
    (thread : Thread tower) : Prop :=
  IsCoherentThread tower thread ∧ IsFixedThread tower thread

/-- Recursively transport one base state through all adjacent bonds. -/
def transportFromBase (tower : Tower.{u})
    (base : tower.State 0) : Thread tower :=
  fun level =>
    Nat.rec (motive := fun index => tower.State index)
      base (fun index state => tower.bond index state) level

@[simp] theorem transportFromBase_zero
    (tower : Tower.{u}) (base : tower.State 0) :
    transportFromBase tower base 0 = base :=
  rfl

@[simp] theorem transportFromBase_succ
    (tower : Tower.{u}) (base : tower.State 0) (level : ℕ) :
    transportFromBase tower base (level + 1) =
      tower.bond level (transportFromBase tower base level) := by
  rfl

/-- The recursively transported thread is coherent by construction. -/
theorem transport_from_base_coherent
    (tower : Tower.{u}) (base : tower.State 0) :
    IsCoherentThread tower (transportFromBase tower base) := by
  intro level
  exact (transportFromBase_succ tower base level).symm

/-- Fixedness of one base state propagates to every completion level. -/
theorem transport_from_fixed_base_is_fixed
    (tower : Tower.{u}) {base : tower.State 0}
    (baseFixed : Function.IsFixedPt (tower.dynamics 0) base) :
    IsFixedThread tower (transportFromBase tower base) := by
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
    (tower : Tower.{u}) {base : tower.State 0}
    (baseFixed : Function.IsFixedPt (tower.dynamics 0) base) :
    IsTruthThread tower (transportFromBase tower base) :=
  ⟨transport_from_base_coherent tower base,
    transport_from_fixed_base_is_fixed tower baseFixed⟩

/-- Every coherent thread is determined by its base coordinate. -/
theorem coherent_thread_eq_transport_from_base
    (tower : Tower.{u}) (thread : Thread tower)
    (coherent : IsCoherentThread tower thread) :
    thread = transportFromBase tower (thread 0) := by
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
            (transportFromBase tower (thread 0) level) :=
          congrArg (tower.bond level) inductionHypothesis
        _ = transportFromBase tower (thread 0) (level + 1) :=
          (transportFromBase_succ tower (thread 0) level).symm

/-- Two coherent threads with the same base state are equal. -/
theorem coherent_threads_ext
    (tower : Tower.{u}) {first second : Thread tower}
    (firstCoherent : IsCoherentThread tower first)
    (secondCoherent : IsCoherentThread tower second)
    (sameBase : first 0 = second 0) :
    first = second := by
  rw [coherent_thread_eq_transport_from_base tower first firstCoherent,
    coherent_thread_eq_transport_from_base tower second secondCoherent,
    sameBase]

#print axioms transport_from_base_coherent
#print axioms transport_from_fixed_base_is_fixed
#print axioms transport_from_fixed_base_is_truth
#print axioms coherent_thread_eq_transport_from_base
#print axioms coherent_threads_ext

end D5.S3.Observer.WorldModel.CompletionTower
