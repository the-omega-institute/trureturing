/- GID: D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Effective resistance is the optimal finite-graph moving particle constant. -/

import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FinCases

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
def expect {v : Type} [Fintype v] (α : ℝ) (f : (v → Fin 2) → ℝ) : ℝ := by
  classical
  exact dotProduct (bernoulli α) f

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
  dotProduct h (fun z => (ζ z : ℝ))

private lemma linear_gradient {v : Type} [Fintype v] [DecidableEq v]
    (h : v → ℝ) (u w : v) (huw : u ≠ w) (ζ : v → Fin 2) :
    grad u w (linearObservable h) ζ = (h u - h w) * ((ζ w : ℝ) - ζ u) := by
  change (∑ z, h z * (ζ (Equiv.swap u w z) : ℝ)) - ∑ z, h z * (ζ z : ℝ) = _
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_add_of_mem u w (mem_univ _) (mem_univ _) huw]
  · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  · intro z _ hz
    rw [Equiv.swap_apply_of_ne_of_ne hz.1 hz.2, sub_self]

private lemma expect_product {v : Type} [Fintype v]
    (α : ℝ) (g : v → Fin 2 → ℝ) :
    expect α (fun ζ => ∏ z, g z (ζ z)) =
      ∏ z, ((1 - α) * g z 0 + α * g z 1) := by
  classical
  change (∑ ζ : v → Fin 2,
    (∏ z, if ζ z = 1 then α else 1 - α) * ∏ z, g z (ζ z)) = _
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun z (t : Fin 2) =>
    (if t = 1 then α else 1 - α) * g z t)]
  apply Finset.prod_congr rfl
  intro z _
  simp only [Fin.sum_univ_two, Fin.isValue, Fin.reduceEq, ite_false,
    ite_true]

private lemma expect_coordinate {v : Type} [Fintype v]
    (α : ℝ) (u : v) : expect α (fun ζ : v → Fin 2 => (ζ u : ℝ)) = α := by
  classical
  have hp := expect_product α (fun z t => if z = u then (t : ℝ) else 1)
  have hl : (fun ζ : v → Fin 2 => ∏ z, if z = u then (ζ z : ℝ) else 1) =
      (fun ζ => (ζ u : ℝ)) := by
    funext ζ
    exact Fintype.prod_ite_eq' u (fun z => (ζ z : ℝ))
  rw [hl] at hp
  rw [hp]
  have hr : (fun z => (1 - α) * (if z = u then ((0 : Fin 2) : ℝ) else 1) +
      α * (if z = u then ((1 : Fin 2) : ℝ) else 1)) =
      (fun z => if z = u then α else 1) := by
    funext z
    by_cases hz : z = u <;> simp only [hz, ↓reduceIte, Fin.isValue, Fin.val_zero,
      Fin.val_one, Nat.cast_zero, Nat.cast_one] <;> ring
  rw [hr]
  exact Fintype.prod_ite_eq' u (fun _ => α)

private lemma expect_pair_product {v : Type} [Fintype v]
    (α : ℝ) (u w : v) (huw : u ≠ w) :
    expect α (fun ζ : v → Fin 2 => (ζ u : ℝ) * ζ w) = α * α := by
  classical
  have hp := expect_product α
    (fun z t => (if z = u then (t : ℝ) else 1) *
      (if z = w then (t : ℝ) else 1))
  have hl : (fun ζ : v → Fin 2 => ∏ z,
      (if z = u then (ζ z : ℝ) else 1) * (if z = w then (ζ z : ℝ) else 1)) =
      (fun ζ => (ζ u : ℝ) * ζ w) := by
    funext ζ
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  rw [hl] at hp
  rw [hp]
  rw [Finset.prod_eq_mul_of_mem u w (mem_univ _) (mem_univ _) huw]
  · simp only [huw, Ne.symm huw, ↓reduceIte, Fin.isValue, Fin.val_zero, Fin.val_one,
      Nat.cast_zero, Nat.cast_one]
    ring
  · intro z _ hz
    simp only [hz.1, hz.2, ↓reduceIte]
    ring

private lemma bernoulli_second_moment {v : Type} [Fintype v]
    (α : ℝ) (u w : v) (huw : u ≠ w) :
    expect α (fun ζ : v → Fin 2 => ((ζ w : ℝ) - ζ u) ^ 2) = 2 * α * (1 - α) := by
  classical
  have hb : ∀ t : Fin 2, (t : ℝ) ^ 2 = (t : ℝ) := by
    intro t
    fin_cases t <;> norm_num
  calc
    expect α (fun ζ : v → Fin 2 => ((ζ w : ℝ) - ζ u) ^ 2) =
        expect α (fun ζ : v → Fin 2 => (ζ w : ℝ)) +
        expect α (fun ζ : v → Fin 2 => (ζ u : ℝ)) -
        2 * expect α (fun ζ : v → Fin 2 => (ζ u : ℝ) * ζ w) := by
      change (∑ ζ : v → Fin 2, bernoulli α ζ * ((ζ w : ℝ) - ζ u) ^ 2) =
        (∑ ζ : v → Fin 2, bernoulli α ζ * (ζ w : ℝ)) +
        (∑ ζ : v → Fin 2, bernoulli α ζ * (ζ u : ℝ)) -
        2 * ∑ ζ : v → Fin 2, bernoulli α ζ * ((ζ u : ℝ) * ζ w)
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ζ _
      have hu := hb (ζ u)
      have hw := hb (ζ w)
      have hid : ((ζ w : ℝ) - ζ u) ^ 2 =
          (ζ w : ℝ) + ζ u - 2 * ((ζ u : ℝ) * ζ w) := by nlinarith
      rw [hid]
      ring
    _ = 2 * α * (1 - α) := by
      rw [expect_coordinate, expect_coordinate, expect_pair_product α u w huw]
      ring

private lemma expect_zero {v : Type} [Fintype v] (α : ℝ) :
    expect α (fun _ : v → Fin 2 => 0) = 0 := by
  classical
  exact dotProduct_zero' (bernoulli α)

private lemma expect_mul {v : Type} [Fintype v] (α a : ℝ) (f : (v → Fin 2) → ℝ) :
    expect α (fun ζ => a * f ζ) = a * expect α f := by
  classical
  exact dotProduct_smul a (bernoulli α) f

private lemma linear_gradient_moment {v : Type} [Fintype v] [DecidableEq v]
    (α : ℝ) (h : v → ℝ) (u w : v) :
    expect α (fun ζ => grad u w (linearObservable h) ζ ^ 2) =
      2 * α * (1 - α) * (h u - h w) ^ 2 := by
  by_cases huw : u = w
  · subst w
    have hg : (fun ζ => grad u u (linearObservable h) ζ ^ 2) =
        (fun _ : v → Fin 2 => (0 : ℝ)) := by
      funext ζ
      change (linearObservable h (ζ ∘ Equiv.swap u u) - linearObservable h ζ) ^ 2 = 0
      simp only [Equiv.swap_self, Equiv.coe_refl, Function.comp_id, sub_self,
        zero_pow (by decide : 2 ≠ 0)]
    rw [hg, expect_zero]
    ring
  · have hg : (fun ζ => grad u w (linearObservable h) ζ ^ 2) =
        (fun ζ => (h u - h w) ^ 2 * ((ζ w : ℝ) - ζ u) ^ 2) := by
      funext ζ
      rw [linear_gradient h u w huw, mul_pow]
    rw [hg, expect_mul, bernoulli_second_moment α u w huw]
    ring

private lemma linear_energy {v : Type} [Fintype v] [DecidableEq v]
    (c : v → v → ℝ) (α : ℝ) (h : v → ℝ) :
    exclusionEnergy c α (linearObservable h) = α * (1 - α) * electricEnergy c h := by
  change (1 / 2 : ℝ) * ((1 / 2) *
    ∑ u, ∑ w, c u w * expect α (fun ζ => grad u w (linearObservable h) ζ ^ 2)) = _
  have hm : (∑ u, ∑ w, c u w * expect α (fun ζ => grad u w (linearObservable h) ζ ^ 2)) =
      ∑ u, ∑ w, c u w * (2 * α * (1 - α) * (h u - h w) ^ 2) := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro w _
    rw [linear_gradient_moment]
  rw [hm]
  change _ = α * (1 - α) * ((1 / 2) * ∑ u, ∑ w, c u w * (h u - h w) ^ 2)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro w _
  ring

private lemma boundary_energy {v : Type} [Fintype v] [DecidableEq v]
    (α : ℝ) (h : v → ℝ) (x y : v) (hx : h x = 1) (hy : h y = 0) :
    (1 / 2) * expect α (fun ζ => grad x y (linearObservable h) ζ ^ 2) = α * (1 - α) := by
  rw [linear_gradient_moment, hx, hy]
  ring

private lemma electric_energy_nonneg {v : Type} [Fintype v]
    (c : v → v → ℝ) (hc : IsConductance c) (h : v → ℝ) :
    0 ≤ electricEnergy c h := by
  change 0 ≤ (1 / 2 : ℝ) * ∑ u, ∑ w, c u w * (h u - h w) ^ 2
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ =>
    Finset.sum_nonneg fun w _ => mul_nonneg (hc.1 u w) (sq_nonneg _))

private lemma feasible_nonempty {v : Type} [Fintype v]
    (c : v → v → ℝ) (x y : v) (hxy : x ≠ y) :
    {e | ∃ h : v → ℝ, h x = 1 ∧ h y = 0 ∧ e = electricEnergy c h}.Nonempty := by
  classical
  let h : v → ℝ := fun z => if z = x then 1 else 0
  refine ⟨electricEnergy c h, h, ?_, ?_, rfl⟩
  · exact ite_eq_left rfl
  · exact ite_eq_right (Ne.symm hxy)

private lemma infimum_bound {v : Type} [Fintype v]
    (c : v → v → ℝ) (hc : IsConductance c) (x y : v) (hxy : x ≠ y) (k : ℝ)
    (hk : ∀ h : v → ℝ, h x = 1 → h y = 0 → 1 ≤ k * electricEnergy c h) :
    1 ≤ k * effectiveConductance c x y := by
  obtain ⟨e, h, hx, hy, rfl⟩ := feasible_nonempty c x y hxy
  have he := electric_energy_nonneg c hc h
  have htest := hk h hx hy
  have hkp : 0 < k := by
    by_contra hn
    have hkn : k ≤ 0 := le_of_not_gt hn
    have := mul_nonpos_of_nonpos_of_nonneg hkn he
    linarith
  have hinf : 1 / k ≤ effectiveConductance c x y := by
    apply le_csInf (feasible_nonempty c x y hxy)
    rintro e ⟨g, gx, gy, rfl⟩
    exact (div_le_iff₀ hkp).mpr (by simpa only [mul_comm] using hk g gx gy)
  exact (div_le_iff₀ hkp).mp hinf |>.trans_eq (mul_comm _ _)

theorem result : claim := by
  intro v _ _ c hc x y hxy α hα hα1 k hk
  apply infimum_bound c hc x y hxy k
  intro h hx hy
  have htest := hk (linearObservable h)
  rw [linear_energy, boundary_energy α h x y hx hy] at htest
  have hpos : 0 < α * (1 - α) := mul_pos hα (sub_pos.mpr hα1)
  nlinarith

end D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality
