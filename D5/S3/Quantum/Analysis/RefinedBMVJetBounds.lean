/- GID: D5/S3/Quantum/Analysis/RefinedBMVJetBounds
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient and degree bounds for the affine products in the scalar certificate. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Positivity

/-! Coefficient and degree bounds for the affine products in BMV jets. -/

namespace RefinedBMV.JetBounds

open Polynomial

/-- Multiplying by an affine polynomial scales a coefficientwise absolute bound
by at most the sum of the absolute values of its two coefficients. -/
theorem coeff_abs_affine_mul (a b B : ℤ) (p : Polynomial ℤ) (hB : 0 ≤ B)
    (h : ∀ k, |p.coeff k| ≤ B) (k : ℕ) :
    |((C a + C b * X) * p).coeff k| ≤ (|a| + |b|) * B := by
  rw [add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_C_mul]
  cases k with
  | zero =>
      rw [coeff_X_mul_zero, mul_zero, add_zero, abs_mul, add_mul]
      exact (mul_le_mul_of_nonneg_left (h 0) (abs_nonneg a)).trans
        (le_add_of_nonneg_right (mul_nonneg (abs_nonneg b) hB))
  | succ k =>
      rw [coeff_X_mul, add_mul]
      exact (abs_add_le _ _).trans (by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (h _) (abs_nonneg a))
          (mul_le_mul_of_nonneg_left (h _) (abs_nonneg b)))

/-- A chain of affine factors scales the bound by one factor of `C₀` per entry. -/
theorem coeff_abs_affine_chain (L : List (ℤ × ℤ)) (P : Polynomial ℤ)
    (B C₀ : ℤ) (hB : 0 ≤ B) (hC : 0 ≤ C₀)
    (hL : ∀ r ∈ L, |r.1| + |r.2| ≤ C₀)
    (hP : ∀ k, |P.coeff k| ≤ B) (k : ℕ) :
    |((L.map (fun r => C r.1 + C r.2 * X)).prod * P).coeff k| ≤ B * C₀ ^ L.length := by
  induction L generalizing k with
  | nil => simpa using hP k
  | cons r L ih =>
      have htail : ∀ q ∈ L, |q.1| + |q.2| ≤ C₀ :=
        fun q hq => hL q (List.mem_cons_of_mem _ hq)
      have hr : |r.1| + |r.2| ≤ C₀ := hL r (by simp)
      simp only [List.map_cons, List.prod_cons, List.length_cons, mul_assoc, pow_succ]
      refine (coeff_abs_affine_mul r.1 r.2 _ _ (by positivity) (ih htail) k).trans ?_
      calc
        (|r.1| + |r.2|) * (B * C₀ ^ L.length) ≤ C₀ * (B * C₀ ^ L.length) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
        _ = B * (C₀ ^ L.length * C₀) := by ac_rfl

/-- The affine-chain term with constant multiplier `c` and binomial power `d`. -/
noncomputable def affineChainTerm (c : ℤ) (d : ℕ) (L : List (ℤ × ℤ)) : Polynomial ℤ :=
  C c * (1 + X) ^ d * (L.map fun r => C r.1 + C r.2 * X).prod

private theorem coeff_abs_one_add_X_pow (d j : ℕ) :
    |((1 + X : Polynomial ℤ) ^ d).coeff j| ≤ (2 : ℤ) ^ d := by
  rw [coeff_one_add_X_pow, abs_of_nonneg (by positivity)]
  exact_mod_cast Nat.choose_le_two_pow d j

private theorem natDegree_affine_chain_le (L : List (ℤ × ℤ)) :
    ((L.map fun r => C r.1 + C r.2 * X).prod : Polynomial ℤ).natDegree ≤ L.length := by
  induction L with
  | nil => simp
  | cons r L ih =>
      have hr : (C r.1 + C r.2 * X).natDegree ≤ 1 := by
        apply natDegree_add_le_of_degree_le
        · simp
        · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
      simpa [Nat.add_comm 1] using natDegree_mul_le_of_le hr ih

/-- Coefficient and degree bounds using the actual number of affine factors. -/
theorem affineChainTerm_bounds_length (c C₀ : ℤ) (d : ℕ) (L : List (ℤ × ℤ))
    (hC : 0 ≤ C₀) (hL : ∀ r ∈ L, |r.1| + |r.2| ≤ C₀) :
    (∀ j, |(affineChainTerm c d L).coeff j| ≤ |c| * 2 ^ d * C₀ ^ L.length) ∧
      (affineChainTerm c d L).natDegree ≤ d + L.length := by
  constructor
  · intro j
    rw [affineChainTerm, mul_comm]
    apply coeff_abs_affine_chain L _ _ C₀ (by positivity) hC hL
    intro n
    rw [coeff_C_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (coeff_abs_one_add_X_pow d n) (abs_nonneg c)
  · unfold affineChainTerm
    refine natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans ?_)
      (natDegree_affine_chain_le L)
    have h : (1 + X : Polynomial ℤ).natDegree ≤ 1 :=
      natDegree_add_le_of_degree_le (by simp) natDegree_X_le
    exact natDegree_pow_le.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left d h)

/-- A common length budget gives uniform bounds for terms with shorter chains. -/
theorem affineChainTerm_bounds (c C₀ : ℤ) (d k : ℕ) (L : List (ℤ × ℤ))
    (hC : 1 ≤ C₀) (hLen : L.length ≤ k) (hL : ∀ r ∈ L, |r.1| + |r.2| ≤ C₀) :
    (∀ j, |(affineChainTerm c d L).coeff j| ≤ |c| * 2 ^ d * C₀ ^ k) ∧
      (affineChainTerm c d L).natDegree ≤ d + k := by
  obtain ⟨hcoeff, hdeg⟩ := affineChainTerm_bounds_length c C₀ d L (by positivity) hL
  exact ⟨fun j => (hcoeff j).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hLen) (by positivity)),
    hdeg.trans (Nat.add_le_add_left hLen d)⟩

/-- Coefficient bounds add over a finite sum, and a common degree bound still holds. -/
theorem sum_bounds {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℤ)
    (B : ι → ℤ) (D : ℕ)
    (h : ∀ i ∈ s, (∀ j, |(P i).coeff j| ≤ B i) ∧ (P i).natDegree ≤ D) :
    (∀ j, |(∑ i ∈ s, P i).coeff j| ≤ ∑ i ∈ s, B i) ∧
      (∑ i ∈ s, P i).natDegree ≤ D := by
  constructor
  · intro j
    rw [finsetSum_coeff]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i hi => (h i hi).1 j)
  · exact natDegree_sum_le_of_forall_le s P fun i hi => (h i hi).2

end RefinedBMV.JetBounds
