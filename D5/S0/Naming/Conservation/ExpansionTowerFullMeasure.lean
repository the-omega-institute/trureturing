/- GID: D5/S0/Naming/Conservation/ExpansionTowerFullMeasure
   generality: G
   mirror-B: D5/B/S0/Naming/Conservation/ExpansionTowerFullMeasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Atomless probability naming towers leave a full-measure anonymous limit. -/

import D5.S0.Naming.Conservation.NamingTowerConservation
import Mathlib.Probability.Distributions.Gaussian.Real

namespace D5.S0.Naming.Conservation.ExpansionTowerFullMeasure

open MeasureTheory
open D5.S0.Naming.Conservation.NamingTowerConservation

universe u v

/-- The points outside the partial assignment of a naming system. -/
def anonymous {X : Type u} [MeasureSpace X] (system : NamingSystem X) : Set X :=
  system.namedᶜ

/-- A countable expansion tower. Successor embeddings represent inclusion of name sets, and
assignment compatibility says that every successor assignment extends its predecessor. -/
structure ExpansionTower (X : Type u) [MeasureSpace X] where
  systems : ℕ → NamingSystem.{u, v} X
  inclusion : ∀ k, (systems k).Name ↪ (systems (k + 1)).Name
  assignment_compatible : ∀ k n,
    (systems (k + 1)).assignment (inclusion k n) = (systems k).assignment n

namespace ExpansionTower

/-- The named points of the limit are the union of all points named at finite stages. -/
def limitNamed {X : Type u} [MeasureSpace X] (tower : ExpansionTower X) : Set X :=
  ⋃ k, (tower.systems k).named

/-- The anonymous set of the limit system. -/
def limitAnonymous {X : Type u} [MeasureSpace X] (tower : ExpansionTower X) : Set X :=
  tower.limitNamedᶜ

/-- Compatible successor inclusion makes the named sets increase along the tower. -/
theorem named_mono {X : Type u} [MeasureSpace X] (tower : ExpansionTower X) (k : ℕ) :
    (tower.systems k).named ⊆ (tower.systems (k + 1)).named := by
  intro x hx
  change ∃ n, (tower.systems k).assignment n = some x at hx
  change ∃ n, (tower.systems (k + 1)).assignment n = some x
  obtain ⟨n, hn⟩ := hx
  refine ⟨tower.inclusion k n, ?_⟩
  rw [tower.assignment_compatible]
  exact hn

end ExpansionTower

set_option checkBinderAnnotations false in
/-- Every naming system over an atomless probability space has full-measure anonymous set, and
the same remains true for the limit of every countable compatible expansion tower. -/
theorem naming_expansion_full_measure
    {X : Type u} [MeasureSpace X] [Uncountable X]
    [NoAtoms (volume : Measure X)] [IsProbabilityMeasure (volume : Measure X)] :
    (∀ system : NamingSystem X, volume (anonymous system) = 1) ∧
      ∀ tower : ExpansionTower X, volume tower.limitAnonymous = 1 := by
  constructor
  · intro system
    have h := @countable_tower_anonymous_full_measure X _ _ (by assumption)
      (by infer_instance) Unit (by infer_instance) (fun _ : Unit => system)
    have hunion : (⋃ _ : Unit, system.named) = system.named := by
      ext x
      simp
    have hfull := h.2.2
    rw [hunion, IsProbabilityMeasure.measure_univ] at hfull
    simpa [anonymous] using hfull
  · intro tower
    have h := @countable_tower_anonymous_full_measure X _ _ (by assumption)
      (by infer_instance) Nat (by infer_instance) tower.systems
    have hfull := h.2.2
    rw [IsProbabilityMeasure.measure_univ] at hfull
    simpa [ExpansionTower.limitAnonymous, ExpansionTower.limitNamed] using hfull

/-- A constant empty-assignment tower inhabits both quantified domains. -/
example : Nonempty (NamingSystem.{0, 0} Real × ExpansionTower.{0, 0} Real) := by
  let system : NamingSystem.{0, 0} Real :=
    { Name := Fin 1
      assignment := fun _ => none
      height := fun _ => 0
      finite_layer := fun _ => Set.toFinite _ }
  let tower : ExpansionTower.{0, 0} Real :=
    { systems := fun _ => system
      inclusion := fun _ => Function.Embedding.refl _
      assignment_compatible := by intros; rfl }
  exact ⟨(system, tower)⟩

/-- A nondegenerate Gaussian measure witnesses the atomless probability hypotheses. -/
noncomputable example :
    ∃ μ : Measure Real, NoAtoms μ ∧ IsProbabilityMeasure μ := by
  refine ⟨ProbabilityTheory.gaussianReal 0 1, ?_, inferInstance⟩
  exact ProbabilityTheory.noAtoms_gaussianReal one_ne_zero

end D5.S0.Naming.Conservation.ExpansionTowerFullMeasure
