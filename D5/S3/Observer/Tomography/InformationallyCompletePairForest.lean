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

def IsProbability {X : Type*} [Fintype X] [DecidableEq X] (μ : X → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

def distribution {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → ℝ) (μ : X → ℝ) (Δ : Set ℝ) : ℝ :=
  by
    classical
    exact ∑ x ∈ Finset.univ.filter (fun x => f x ∈ Δ), μ x

def IsICPair {X : Type*} [Fintype X] [DecidableEq X] (f g : X → ℝ) : Prop :=
  ∀ μ ν, IsProbability μ → IsProbability ν →
    distribution f μ = distribution f ν → distribution g μ = distribution g ν → μ = ν

def fiberGraph {X : Type*} [Fintype X] [DecidableEq X] (f g : X → ℝ) : SimpleGraph (ℝ ⊕ ℝ) :=
  SimpleGraph.fromRel (fun v w =>
    match v, w with
    | Sum.inl a, Sum.inr b => ∃ x, f x = a ∧ g x = b
    | _, _ => False)

private lemma distribution_eq_iff_fiber_sums {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → ℝ) (μ ν : X → ℝ) :
    distribution f μ = distribution f ν ↔
      ∀ a, (∑ x ∈ Finset.univ.filter (fun x => f x = a), μ x) =
        ∑ x ∈ Finset.univ.filter (fun x => f x = a), ν x := by
  classical
  constructor
  · intro h a
    have ha := congrFun h ({a} : Set ℝ)
    have hμ : distribution f μ ({a} : Set ℝ) =
        ∑ x ∈ Finset.univ.filter (fun x => f x = a), μ x := by
      simp [distribution, Finset.sum_filter]
    have hν : distribution f ν ({a} : Set ℝ) =
        ∑ x ∈ Finset.univ.filter (fun x => f x = a), ν x := by
      simp [distribution, Finset.sum_filter]
    rw [hμ, hν] at ha
    exact ha
  · intro h
    funext Δ
    let s : Finset X := Finset.univ.filter (fun x => f x ∈ Δ)
    let t : Finset ℝ := s.image f
    have hmap : ∀ x ∈ s, f x ∈ t := by
      intro x hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hμ := Finset.sum_fiberwise_of_maps_to hmap μ
    have hν := Finset.sum_fiberwise_of_maps_to hmap ν
    have hfiber (a : ℝ) (ha : a ∈ t) (q : X → ℝ) :
        (∑ x ∈ s with f x = a, q x) =
          ∑ x ∈ Finset.univ.filter (fun x => f x = a), q x := by
      obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp ha
      have hΔa : f x ∈ Δ := by simpa [s] using hx
      have hΔa' : a ∈ Δ := by simpa [hxa] using hΔa
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, s]
        constructor
        · rintro ⟨hfd, hfa⟩
          exact hfa
        · intro hfa
          exact ⟨by simpa [hfa] using hΔa', hfa⟩
      · intro y hy
        rfl
    calc
      distribution f μ Δ = ∑ x ∈ s, μ x := rfl
      _ = ∑ a ∈ t, ∑ x ∈ s with f x = a, μ x := hμ.symm
      _ = ∑ a ∈ t, ∑ x ∈ s with f x = a, ν x := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfiber a ha μ, hfiber a ha ν, h a]
      _ = ∑ x ∈ s, ν x := hν
      _ = distribution f ν Δ := rfl

private lemma not_injective_not_ic {X : Type*} [Fintype X] [DecidableEq X] {f g : X → ℝ}
    (h : ¬ Function.Injective (fun x => (f x, g x))) : ¬ IsICPair f g := by
  classical
  obtain ⟨x, y, hpair, hxy⟩ := Function.not_injective_iff.mp h
  have hfx : f x = f y := congrArg Prod.fst hpair
  have hgx : g x = g y := congrArg Prod.snd hpair
  intro hic
  have hprob (z : X) : IsProbability (Pi.single z (1 : ℝ)) := by
    refine ⟨?_, ?_⟩
    · intro u
      by_cases huz : u = z <;> simp [huz]
    · simp
  have hf : distribution f (Pi.single x (1 : ℝ)) =
      distribution f (Pi.single y (1 : ℝ)) := by
    funext Δ
    by_cases hΔx : f x ∈ Δ <;> by_cases hΔy : f y ∈ Δ <;>
      simp [distribution, hΔx, hΔy, hfx]
  have hg : distribution g (Pi.single x (1 : ℝ)) =
      distribution g (Pi.single y (1 : ℝ)) := by
    funext Δ
    by_cases hΔx : g x ∈ Δ <;> by_cases hΔy : g y ∈ Δ <;>
      simp [distribution, hΔx, hΔy, hgx]
  have heq := hic _ _ (hprob x) (hprob y) hf hg
  have hneq : (Pi.single x (1 : ℝ) : X → ℝ) ≠ Pi.single y (1 : ℝ) := by
    intro hsingle
    have hvalue := congrFun hsingle x
    simp [hxy] at hvalue
  exact hneq heq

private lemma cycle_not_ic {X : Type*} [Fintype X] [DecidableEq X] {f g : X → ℝ}
    (hinj : Function.Injective (fun x => (f x, g x)))
    (hcycle : ¬ (fiberGraph f g).IsAcyclic) : ¬ IsICPair f g := by
  sorry

private lemma ic_injective {X : Type*} [Fintype X] [DecidableEq X] {f g : X → ℝ}
    (hic : IsICPair f g) : Function.Injective (fun x => (f x, g x)) := by
  by_contra h
  exact not_injective_not_ic h hic

private lemma ic_acyclic {X : Type*} [Fintype X] [DecidableEq X] {f g : X → ℝ}
    (hic : IsICPair f g) (hinj : Function.Injective (fun x => (f x, g x))) :
    (fiberGraph f g).IsAcyclic := by
  sorry

private lemma injective_acyclic_ic {X : Type*} [Fintype X] [DecidableEq X] {f g : X → ℝ}
    (hinj : Function.Injective (fun x => (f x, g x)))
    (hacyc : (fiberGraph f g).IsAcyclic) : IsICPair f g := by
  sorry

theorem result {X : Type*} [Fintype X] [DecidableEq X] (f g : X → ℝ) :
    IsICPair f g ↔
      Function.Injective (fun x => (f x, g x)) ∧ (fiberGraph f g).IsAcyclic := by
  constructor
  · intro hic
    exact ⟨ic_injective hic, ic_acyclic hic (ic_injective hic)⟩
  · rintro ⟨hinj, hacyc⟩
    exact injective_acyclic_ic hinj hacyc

end D5.S3.Observer.Tomography.InformationallyCompletePairForest
