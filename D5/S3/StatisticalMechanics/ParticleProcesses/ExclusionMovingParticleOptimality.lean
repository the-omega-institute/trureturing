/- GID: D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Effective resistance is the optimal finite-graph moving particle constant. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The finite-graph optimality assertion in J. P. Chen, arXiv:1606.01577v4,
    with each undirected edge counted once and density strictly between zero and one. -/

set_option autoImplicit false

noncomputable section

open Finset

namespace D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality

/-- Nonnegative symmetric conductances, with zero denoting a non-edge. -/
def IsConductance {v : Type} (c : v → v → ℝ) : Prop :=
  (∀ u w, 0 ≤ c u w) ∧ ∀ u w, c u w = c w u

/-- Exchange the occupations at two vertices. -/
def swap {v : Type} [DecidableEq v] (x y : v) (ζ : v → Fin 2) : v → Fin 2 :=
  ζ ∘ Equiv.swap x y

/-- The exclusion-process swap gradient. -/
def grad {v : Type} [DecidableEq v] (x y : v) (f : (v → Fin 2) → ℝ)
    (ζ : v → Fin 2) : ℝ := f (swap x y ζ) - f ζ

/-- Constant-density product Bernoulli mass of a configuration. -/
def bernoulli {v : Type} [Fintype v] (α : ℝ) (ζ : v → Fin 2) : ℝ :=
  ∏ z, if ζ z = 1 then α else 1 - α

/-- Expectation against the product Bernoulli mass. -/
def expect {v : Type} [Fintype v] (α : ℝ) (f : (v → Fin 2) → ℝ) : ℝ :=
  ∑ ζ, bernoulli α ζ * f ζ

/-- Exclusion Dirichlet energy; the inner half removes ordered-pair double counting. -/
def exclusionEnergy {v : Type} [Fintype v] [DecidableEq v]
    (c : v → v → ℝ) (α : ℝ) (f : (v → Fin 2) → ℝ) : ℝ :=
  (1 / 2) * ((1 / 2) * ∑ u, ∑ w, c u w * expect α (fun ζ => grad u w f ζ ^ 2))

/-- Electrical Dirichlet energy with each undirected edge counted once. -/
def electricEnergy {v : Type} [Fintype v] (c : v → v → ℝ) (h : v → ℝ) : ℝ :=
  (1 / 2) * ∑ u, ∑ w, c u w * (h u - h w) ^ 2

/-- Reciprocal effective resistance as the infimum over unit-voltage potentials. -/
def effectiveConductance {v : Type} [Fintype v] (c : v → v → ℝ) (x y : v) : ℝ :=
  sInf {e | ∃ h : v → ℝ, h x = 1 ∧ h y = 0 ∧ e = electricEnergy c h}

/-- Every admissible moving-particle constant dominates effective resistance. -/
def claim : Prop :=
  ∀ (v : Type) [Fintype v] [DecidableEq v] (c : v → v → ℝ), IsConductance c →
    ∀ x y : v, x ≠ y → ∀ α : ℝ, 0 < α → α < 1 → ∀ k : ℝ,
      (∀ f : (v → Fin 2) → ℝ,
        (1 / 2) * expect α (fun ζ => grad x y f ζ ^ 2) ≤ k * exclusionEnergy c α f) →
      1 ≤ k * effectiveConductance c x y

private def linearObservable {v : Type} [Fintype v] (h : v → ℝ) (ζ : v → Fin 2) : ℝ :=
  ∑ z, h z * (ζ z : ℝ)

private lemma linear_gradient {v : Type} [Fintype v] [DecidableEq v]
    (h : v → ℝ) (u w : v) (huw : u ≠ w) (ζ : v → Fin 2) :
    grad u w (linearObservable h) ζ = (h u - h w) * ((ζ w : ℝ) - ζ u) := by
  sorry

private lemma bernoulli_second_moment {v : Type} [Fintype v] [DecidableEq v]
    (α : ℝ) (u w : v) (huw : u ≠ w) :
    expect α (fun ζ : v → Fin 2 => ((ζ w : ℝ) - ζ u) ^ 2) = 2 * α * (1 - α) := by
  sorry

private lemma linear_gradient_moment {v : Type} [Fintype v] [DecidableEq v]
    (α : ℝ) (h : v → ℝ) (u w : v) :
    expect α (fun ζ => grad u w (linearObservable h) ζ ^ 2) =
      2 * α * (1 - α) * (h u - h w) ^ 2 := by
  sorry

private lemma linear_energy {v : Type} [Fintype v] [DecidableEq v]
    (c : v → v → ℝ) (α : ℝ) (h : v → ℝ) :
    exclusionEnergy c α (linearObservable h) = α * (1 - α) * electricEnergy c h := by
  sorry

private lemma boundary_energy {v : Type} [Fintype v] [DecidableEq v]
    (α : ℝ) (h : v → ℝ) (x y : v) (hx : h x = 1) (hy : h y = 0) :
    (1 / 2) * expect α (fun ζ => grad x y (linearObservable h) ζ ^ 2) = α * (1 - α) := by
  sorry

private lemma electric_energy_nonneg {v : Type} [Fintype v]
    (c : v → v → ℝ) (hc : IsConductance c) (h : v → ℝ) :
    0 ≤ electricEnergy c h := by
  sorry

private lemma feasible_nonempty {v : Type} [Fintype v] [DecidableEq v]
    (c : v → v → ℝ) (x y : v) (hxy : x ≠ y) :
    {e | ∃ h : v → ℝ, h x = 1 ∧ h y = 0 ∧ e = electricEnergy c h}.Nonempty := by
  sorry

private lemma infimum_bound {v : Type} [Fintype v] [DecidableEq v]
    (c : v → v → ℝ) (hc : IsConductance c) (x y : v) (hxy : x ≠ y) (k : ℝ)
    (hk : ∀ h : v → ℝ, h x = 1 → h y = 0 → 1 ≤ k * electricEnergy c h) :
    1 ≤ k * effectiveConductance c x y := by
  sorry

theorem result : claim := by
  intro v _ _ c hc x y hxy α hα hα1 k hk
  apply infimum_bound c hc x y hxy k
  intro h hx hy
  have htest := hk (linearObservable h)
  rw [linear_energy, boundary_energy α h x y hx hy] at htest
  have hpos : 0 < α * (1 - α) := mul_pos hα (sub_pos.mpr hα1)
  nlinarith

end D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality
