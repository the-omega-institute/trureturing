/- GID: D5/S3/Arith/DiophantineApproximation/WeightedOrder
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/WeightedOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted order is additive under multiplication over a domain. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Data.ENNReal.BigOperators

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Finsupp

end Finsupp

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {w : σ → ℝ≥0∞} {μ : σ →₀ ℕ} {P Q : MvPolynomial σ R}

/-- **The weighted order** of `P`: the least weight `∑ j, μ j * w j` of a monomial `X^μ`
occurring in `P`, and `⊤` for `P = 0`. -/
def weightedOrder (w : σ → ℝ≥0∞) (P : MvPolynomial σ R) : ℝ≥0∞ :=
  P.support.inf (Finsupp.weight w)

/-- **The ultrametric inequality.** No hypothesis: at `P + Q = 0` the left side is at most `⊤`. -/
theorem le_weightedOrder_add (w : σ → ℝ≥0∞) (P Q : MvPolynomial σ R) :
    min (weightedOrder w P) (weightedOrder w Q) ≤ weightedOrder w (P + Q) := by
  refine (fun {w : _ → ENNReal} {P : MvPolynomial _ _} {c : ENNReal}
      (h : ∀ μ, P.coeff μ ≠ 0 → c ≤ Finsupp.weight w μ) ↦
      (show c ≤ MvPolynomial.weightedOrder w P from
        Finset.le_inf fun _ hμ ↦ h _ (MvPolynomial.mem_support_iff.mp hμ))) fun μ hμ ↦ ?_
  have hor : P.coeff μ ≠ 0 ∨ Q.coeff μ ≠ 0 := by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact hμ (by simp [hc.1, hc.2])
  rcases hor with h | h
  · exact le_trans (min_le_left _ _) ((fun {w : _ → ENNReal} {P : MvPolynomial _ _} {μ} (h : P.coeff μ ≠ 0) ↦
      (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w μ from
        Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) h)
  · exact le_trans (min_le_right _ _) ((fun {w : _ → ENNReal} {P : MvPolynomial _ _} {μ} (h : P.coeff μ ≠ 0) ↦
      (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w μ from
        Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) h)

/-- **Half of multiplicativity**, and the half that needs nothing: every monomial of a product is
a sum of a monomial of each factor. -/
theorem add_le_weightedOrder_mul (w : σ → ℝ≥0∞) (P Q : MvPolynomial σ R) :
    weightedOrder w P + weightedOrder w Q ≤ weightedOrder w (P * Q) := by
  classical
  refine (fun {w : _ → ENNReal} {P : MvPolynomial _ _} {c : ENNReal}
      (h : ∀ μ, P.coeff μ ≠ 0 → c ≤ Finsupp.weight w μ) ↦
      (show c ≤ MvPolynomial.weightedOrder w P from
        Finset.le_inf fun _ hμ ↦ h _ (MvPolynomial.mem_support_iff.mp hμ))) fun μ hμ ↦ ?_
  rw [coeff_mul] at hμ
  obtain ⟨⟨a, b⟩, hab, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
  rw [Finset.mem_antidiagonal] at hab
  calc weightedOrder w P + weightedOrder w Q
      ≤ Finsupp.weight w a + Finsupp.weight w b :=
        add_le_add ((fun {w : _ → ENNReal} {P : MvPolynomial _ _} {μ} (h : P.coeff μ ≠ 0) ↦
      (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w μ from
        Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) (left_ne_zero_of_mul H))
          ((fun {w : _ → ENNReal} {P : MvPolynomial _ _} {μ} (h : P.coeff μ ≠ 0) ↦
      (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w μ from
        Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) (right_ne_zero_of_mul H))
    _ = Finsupp.weight w μ := by rw [← map_add, hab]

/-- **The weighted order is additive on products.** The hypothesis on the ring is used once, to
know that the product of the two lowest weighted homogeneous parts is not zero. -/
theorem weightedOrder_mul [NoZeroDivisors R] (hw : ∀ j, w j ≠ ⊤) (P Q : MvPolynomial σ R) :
    weightedOrder w (P * Q) = weightedOrder w P + weightedOrder w Q := by
  classical
  rcases eq_or_ne P 0 with rfl | hP
  · rw [zero_mul, show MvPolynomial.weightedOrder _ (0 : MvPolynomial _ _) = ⊤ from by
      rw [MvPolynomial.weightedOrder, MvPolynomial.support_zero, Finset.inf_empty], top_add]
  rcases eq_or_ne Q 0 with rfl | hQ
  · rw [mul_zero, show MvPolynomial.weightedOrder _ (0 : MvPolynomial _ _) = ⊤ from by
      rw [MvPolynomial.weightedOrder, MvPolynomial.support_zero, Finset.inf_empty], add_top]
  refine le_antisymm ?_ (add_le_weightedOrder_mul w P Q)
  obtain ⟨ν, hν, hmν⟩ := (show ∃ μ, P.coeff μ ≠ 0 ∧ weightedOrder w P = Finsupp.weight w μ from by
    obtain ⟨μ, hμ, hmin⟩ :=
      Finset.exists_mem_eq_inf P.support (support_nonempty.mpr hP) (Finsupp.weight w)
    exact ⟨μ, mem_support_iff.mp hμ, hmin⟩)
  obtain ⟨ρ, hρ, hmρ⟩ := (show ∃ μ, Q.coeff μ ≠ 0 ∧ weightedOrder w Q = Finsupp.weight w μ from by
    obtain ⟨μ, hμ, hmin⟩ :=
      Finset.exists_mem_eq_inf Q.support (support_nonempty.mpr hQ) (Finsupp.weight w)
    exact ⟨μ, mem_support_iff.mp hμ, hmin⟩)
  set m := weightedOrder w P with hm
  set n := weightedOrder w Q with hn
  have hmtop : m ≠ ⊤ := hmν ▸ (show Finsupp.weight w ν ≠ ⊤ from by
    rw [Finsupp.weight_apply, Finsupp.sum, ← lt_top_iff_ne_top, ENNReal.sum_lt_top]
    exact fun j _ ↦ lt_top_iff_ne_top.mpr (by
      rw [nsmul_eq_mul]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hw j)))
  have hntop : n ≠ ⊤ := hmρ ▸ (show Finsupp.weight w ρ ≠ ⊤ from by
    rw [Finsupp.weight_apply, Finsupp.sum, ← lt_top_iff_ne_top, ENNReal.sum_lt_top]
    exact fun j _ ↦ lt_top_iff_ne_top.mpr (by
      rw [nsmul_eq_mul]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hw j)))
  have hP₀ : weightedHomogeneousComponent w m P ≠ 0 := fun h ↦ hν <| by
    have h2 := coeff_weightedHomogeneousComponent (w := w) m P ν
    rw [h, if_pos hmν.symm] at h2
    simpa using h2.symm
  have hQ₀ : weightedHomogeneousComponent w n Q ≠ 0 := fun h ↦ hρ <| by
    have h2 := coeff_weightedHomogeneousComponent (w := w) n Q ρ
    rw [h, if_pos hmρ.symm] at h2
    simpa using h2.symm
  obtain ⟨μ, hμ⟩ := ne_zero_iff.mp (mul_ne_zero hP₀ hQ₀)
  have hdeg : Finsupp.weight w μ = m + n :=
    IsWeightedHomogeneous.mul (weightedHomogeneousComponent_isWeightedHomogeneous m P)
      (weightedHomogeneousComponent_isWeightedHomogeneous n Q) hμ
  have key : ∀ p : (σ →₀ ℕ) × (σ →₀ ℕ), p.1 + p.2 = μ → P.coeff p.1 ≠ 0 → Q.coeff p.2 ≠ 0 →
      Finsupp.weight w p.1 = m ∧ Finsupp.weight w p.2 = n := by
    intro p hp h1 h2
    have e1 : m ≤ Finsupp.weight w p.1 := (fun {w : _ → ENNReal} {P : MvPolynomial _ _} {μ} (h : P.coeff μ ≠ 0) ↦
      (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w μ from
        Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) h1
    have e2 : n ≤ Finsupp.weight w p.2 := (fun {w : _ → ENNReal} {P : MvPolynomial _ _} {μ} (h : P.coeff μ ≠ 0) ↦
      (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w μ from
        Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) h2
    have esum : Finsupp.weight w p.1 + Finsupp.weight w p.2 = m + n := by
      rw [← map_add, hp, hdeg]
    exact ⟨(ENNReal.add_left_inj hntop).mp (le_antisymm
        (le_trans (add_le_add le_rfl e2) (le_of_eq esum)) (add_le_add e1 le_rfl)),
      (ENNReal.add_right_inj hmtop).mp (le_antisymm
        (le_trans (add_le_add e1 le_rfl) (le_of_eq esum)) (add_le_add le_rfl e2))⟩
  have hcoeff : (P * Q).coeff μ = (weightedHomogeneousComponent w m P *
      weightedHomogeneousComponent w n Q).coeff μ := by
    rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
    by_cases h1 : P.coeff p.1 = 0
    · rw [h1]; simp
    by_cases h2 : Q.coeff p.2 = 0
    · rw [h2]; simp
    obtain ⟨e1, e2⟩ := key p hp h1 h2
    rw [if_pos e1, if_pos e2]
  calc weightedOrder w (P * Q)
      ≤ Finsupp.weight w μ := (fun {w : _ → ENNReal} {P : MvPolynomial _ _} {μ} (h : P.coeff μ ≠ 0) ↦
      (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w μ from
        Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) (hcoeff ▸ hμ)
    _ = m + n := hdeg

/-- **Homogeneity in the weights.** The hypothesis is needed only at `P = 0`, where the right
side is `c * ⊤`. -/
theorem weightedOrder_const_mul {c : ℝ≥0∞} (hc : c ≠ 0) (w : σ → ℝ≥0∞) (P : MvPolynomial σ R) :
    weightedOrder (fun j ↦ c * w j) P = c * weightedOrder w P := by
  have hweight : ∀ μ : σ →₀ ℕ,
      Finsupp.weight (fun j ↦ c * w j) μ = c * Finsupp.weight w μ := by
    intro μ
    rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [nsmul_eq_mul, nsmul_eq_mul, mul_left_comm]
  rcases eq_or_ne P 0 with rfl | hP
  · rw [show MvPolynomial.weightedOrder _ (0 : MvPolynomial _ _) = ⊤ from by
      rw [MvPolynomial.weightedOrder, MvPolynomial.support_zero, Finset.inf_empty], show MvPolynomial.weightedOrder _ (0 : MvPolynomial _ _) = ⊤ from by
      rw [MvPolynomial.weightedOrder, MvPolynomial.support_zero, Finset.inf_empty], ENNReal.mul_top hc]
  obtain ⟨μ, hμ, hval⟩ := (show ∃ μ, P.coeff μ ≠ 0 ∧ weightedOrder w P = Finsupp.weight w μ from by
    obtain ⟨μ, hμ, hmin⟩ :=
      Finset.exists_mem_eq_inf P.support (support_nonempty.mpr hP) (Finsupp.weight w)
    exact ⟨μ, mem_support_iff.mp hμ, hmin⟩)
  refine le_antisymm ?_ ((fun {w : _ → ENNReal} {P : MvPolynomial _ _} {c : ENNReal}
      (h : ∀ μ, P.coeff μ ≠ 0 → c ≤ Finsupp.weight w μ) ↦
      (show c ≤ MvPolynomial.weightedOrder w P from
        Finset.le_inf fun _ hμ ↦ h _ (MvPolynomial.mem_support_iff.mp hμ))) fun ν hν ↦ ?_)
  · rw [hval, ← hweight μ]
    exact (fun {w : _ → ENNReal} {P : MvPolynomial _ _} {μ} (h : P.coeff μ ≠ 0) ↦
      (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w μ from
        Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) hμ
  · rw [hweight ν]
    gcongr
    exact (fun {w : _ → ENNReal} {P : MvPolynomial _ _} {μ} (h : P.coeff μ ≠ 0) ↦
      (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w μ from
        Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) hν

end MvPolynomial

end

end
