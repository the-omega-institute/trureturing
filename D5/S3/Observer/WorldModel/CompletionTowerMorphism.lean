/- GID: D5/S3/Observer/WorldModel/CompletionTowerMorphism
   generality: G
   mirror-B: D5/B/S3/Observer/WorldModel/CompletionTowerMorphism
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Natural wormholes transport fixed threads between completion towers. -/

import D5.S3.Observer.WorldModel.CompletionTower

/-!
A tower morphism is a levelwise family of semiconjugate observer bridges that
also commutes with adjacent completion bonds.  The naturality square is the
typed version of a horizontal “wormhole” crossing a vertical completion tower.

Such a morphism transports coherent threads, fixed threads, and therefore
truth threads.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.WorldModel.CompletionTowerMorphism

open D5.S3.Observer.Bridges.FixedPointSemiconjugacy
open D5.S3.Observer.WorldModel.CompletionTower

universe u v w

/-- A natural family of levelwise wormholes between two completion towers. -/
structure TowerMorphism
    (source : Tower.{u}) (target : Tower.{v}) where
  map : ∀ level, source.State level → target.State level
  map_semiconj : ∀ level,
    Function.Semiconj (map level)
      (source.dynamics level) (target.dynamics level)
  naturality : ∀ level state,
    map (level + 1) (source.bond level state) =
      target.bond level (map level state)

namespace TowerMorphism

variable {source : Tower.{u}}
variable {middle : Tower.{v}}
variable {target : Tower.{w}}

/-- Apply a tower morphism coordinatewise to a thread. -/
def mapThread
    (morphism : TowerMorphism source target)
    (thread : Thread source) : Thread target :=
  fun level => morphism.map level (thread level)

/-- Naturality transports coherent threads. -/
theorem map_thread_coherent
    (morphism : TowerMorphism source target)
    {thread : Thread source}
    (coherent : IsCoherentThread source thread) :
    IsCoherentThread target (morphism.mapThread thread) := by
  intro level
  change target.bond level (morphism.map level (thread level)) =
    morphism.map (level + 1) (thread (level + 1))
  rw [← morphism.naturality level (thread level), coherent level]

/-- Levelwise semiconjugacy transports fixed threads. -/
theorem map_thread_fixed
    (morphism : TowerMorphism source target)
    {thread : Thread source}
    (fixed : IsFixedThread source thread) :
    IsFixedThread target (morphism.mapThread thread) := by
  intro level
  exact fixed_point_maps (morphism.map_semiconj level) (fixed level)

/-- Every tower morphism transports truth threads. -/
theorem map_truth_thread
    (morphism : TowerMorphism source target)
    {thread : Thread source}
    (truth : IsTruthThread source thread) :
    IsTruthThread target (morphism.mapThread thread) :=
  ⟨morphism.map_thread_coherent truth.1,
    morphism.map_thread_fixed truth.2⟩

/-- Identity tower morphism. -/
def identity (tower : Tower.{u}) : TowerMorphism tower tower where
  map := fun _ => id
  map_semiconj := by
    intro level state
    rfl
  naturality := by
    intro level state
    rfl

/-- Composition of tower morphisms. -/
def compose
    (second : TowerMorphism middle target)
    (first : TowerMorphism source middle) :
    TowerMorphism source target where
  map := fun level => second.map level ∘ first.map level
  map_semiconj := by
    intro level
    exact (first.map_semiconj level).trans
      (second.map_semiconj level)
  naturality := by
    intro level state
    change second.map (level + 1)
        (first.map (level + 1) (source.bond level state)) =
      target.bond level
        (second.map level (first.map level state))
    rw [first.naturality level state,
      second.naturality level (first.map level state)]

/-- Coordinatewise transport respects composition. -/
theorem mapThread_compose
    (second : TowerMorphism middle target)
    (first : TowerMorphism source middle)
    (thread : Thread source) :
    (compose second first).mapThread thread =
      second.mapThread (first.mapThread thread) :=
  rfl

#print axioms map_thread_coherent
#print axioms map_thread_fixed
#print axioms map_truth_thread
#print axioms mapThread_compose

end TowerMorphism

end D5.S3.Observer.WorldModel.CompletionTowerMorphism
