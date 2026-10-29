/- GID: D5/S3/Observer/Tomography/InformationallyCompletePairForest
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/InformationallyCompletePairForest
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: IC pairs are exactly injective pairs with acyclic fiber graphs. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace D5.S3.Observer.Tomography.InformationallyCompletePairForest

def IsProbability {X : Type*} [Fintype X] (μ : X → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

def distribution {X : Type*} [Fintype X] (f : X → ℝ) (μ : X → ℝ) (Δ : Set ℝ) : ℝ :=
  by
    classical
    exact ∑ x ∈ Finset.univ.filter (fun x => f x ∈ Δ), μ x

def IsICPair {X : Type*} [Fintype X] (f g : X → ℝ) : Prop :=
  ∀ μ ν, IsProbability μ → IsProbability ν →
    distribution f μ = distribution f ν → distribution g μ = distribution g ν → μ = ν

def fiberGraph {X : Type*} [Fintype X] (f g : X → ℝ) : SimpleGraph (ℝ ⊕ ℝ) :=
  SimpleGraph.fromRel (fun v w =>
    match v, w with
    | Sum.inl a, Sum.inr b => ∃ x, f x = a ∧ g x = b
    | _, _ => False)

private lemma distribution_eq_iff_fiber_sums {X : Type*} [Fintype X]
    (f : X → ℝ) (μ ν : X → ℝ) :
    distribution f μ = distribution f ν ↔
      ∀ a, (∑ x ∈ Finset.univ.filter (fun x => f x = a), μ x) =
        ∑ x ∈ Finset.univ.filter (fun x => f x = a), ν x := by
  sorry

private lemma not_injective_not_ic {X : Type*} [Fintype X] {f g : X → ℝ}
    (h : ¬ Function.Injective (fun x => (f x, g x))) : ¬ IsICPair f g := by
  sorry

private lemma cycle_not_ic {X : Type*} [Fintype X] {f g : X → ℝ}
    (hinj : Function.Injective (fun x => (f x, g x)))
    (hcycle : ¬ (fiberGraph f g).IsAcyclic) : ¬ IsICPair f g := by
  sorry

private lemma ic_injective {X : Type*} [Fintype X] {f g : X → ℝ}
    (hic : IsICPair f g) : Function.Injective (fun x => (f x, g x)) := by
  sorry

private lemma ic_acyclic {X : Type*} [Fintype X] {f g : X → ℝ}
    (hic : IsICPair f g) (hinj : Function.Injective (fun x => (f x, g x))) :
    (fiberGraph f g).IsAcyclic := by
  sorry

private lemma injective_acyclic_ic {X : Type*} [Fintype X] {f g : X → ℝ}
    (hinj : Function.Injective (fun x => (f x, g x)))
    (hacyc : (fiberGraph f g).IsAcyclic) : IsICPair f g := by
  sorry

theorem result {X : Type*} [Fintype X] (f g : X → ℝ) :
    IsICPair f g ↔
      Function.Injective (fun x => (f x, g x)) ∧ (fiberGraph f g).IsAcyclic := by
  constructor
  · intro hic
    exact ⟨ic_injective hic, ic_acyclic hic (ic_injective hic)⟩
  · rintro ⟨hinj, hacyc⟩
    exact injective_acyclic_ic hinj hacyc

end D5.S3.Observer.Tomography.InformationallyCompletePairForest
