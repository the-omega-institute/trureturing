/- GID: D5/S3/ArithSums/BrentEvenMomentPolynomial
   generality: I
   mirror-B: D5/B/S3/ArithSums/BrentEvenMomentPolynomial
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Even double binomial moments admit ordinary integer coefficient polynomials. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartitionCollisionExpansion
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

open scoped BigOperators
open Finset Polynomial

namespace D5.S3.ArithSums.BrentEvenMomentPolynomial

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Binomial coefficients with the source's zero convention for integer lower indices. -/
def binomial (N : ℕ) (k : ℤ) : ℚ :=
  if 0 ≤ k then (N.choose k.toNat : ℚ) else 0

/-- The original double sum, including both endpoints and the zeroth-power convention. -/
def W (β n : ℕ) : ℚ :=
  ∑ i ∈ Icc (-(n : ℤ)) n, ∑ j ∈ Icc (-(n : ℤ)) n,
    binomial (2 * n) (n + i) * binomial (2 * n) (n + j) *
      |(i : ℚ) ^ 2 - (j : ℚ) ^ 2| ^ β

/-- Ordinary coefficient integrality, with one polynomial for all natural arguments. -/
def claim : Prop :=
  ∀ r : ℕ, ∃ P : ℤ[X], ∀ n : ℕ,
    (2 : ℚ) ^ (4 * n) * P.eval₂ (Int.castRingHom ℚ) (n : ℚ) =
      (2 : ℚ) ^ r * W (2 * r) n

private theorem sum_shift (n : ℕ) (f : ℤ → ℚ) :
    (∑ i ∈ Icc (-(n : ℤ)) n, f i) =
      ∑ k ∈ range (2 * n + 1), f ((k : ℤ) - n) := by
  symm
  refine sum_bij (fun k _ => (k : ℤ) - n) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_range] at hk
    simp only [mem_Icc]
    omega
  · intro a ha b hb h
    omega
  · intro i hi
    simp only [mem_Icc] at hi
    refine ⟨(i + n).toNat, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro k hk
    rfl

private theorem W_shift (β n : ℕ) :
    W β n = ∑ k ∈ range (2 * n + 1), ∑ l ∈ range (2 * n + 1),
      ((2 * n).choose k : ℚ) * ((2 * n).choose l : ℚ) *
        |((k : ℚ) - n) ^ 2 - ((l : ℚ) - n) ^ 2| ^ β := by
  unfold W
  rw [sum_shift]
  apply sum_congr rfl
  intro k hk
  rw [sum_shift]
  apply sum_congr rfl
  intro l hl
  simp [binomial, Int.cast_sub, Int.cast_natCast]

private theorem sum_by_card {α : Type*} [Fintype α] (f : ℕ → ℚ) :
    (∑ s : Finset α, f s.card) =
      ∑ k ∈ range (Fintype.card α + 1), (Fintype.card α).choose k * f k := by
  classical
  have h : (univ : Finset (Finset α)) = (univ : Finset α).powerset := by
    ext s
    simp
  rw [h, sum_powerset]
  simp_rw [sum_powersetCard, card_univ, nsmul_eq_mul]

private def sampleEquiv (N : ℕ) :
    (Fin N → Bool × Bool) ≃ (Finset (Fin N) × Finset (Fin N)) where
  toFun s := (univ.filter fun t => (s t).1, univ.filter fun t => (s t).2)
  invFun p t := (decide (t ∈ p.1), decide (t ∈ p.2))
  left_inv s := by
    funext t
    apply Prod.ext <;> simp
  right_inv p := by
    apply Prod.ext <;> ext t <;> simp

private def sign (b : Bool) : ℚ := if b then 1 else -1
private def U (z : Bool × Bool) : ℚ := (sign z.1 + sign z.2) / 2
private def V (z : Bool × Bool) : ℚ := (sign z.1 - sign z.2) / 2

private theorem sum_sign (N : ℕ) (s : Fin N → Bool) :
    (∑ t, sign (s t)) = 2 * ((univ.filter fun t => s t).card : ℚ) - N := by
  simp only [sign, sum_ite, sum_const, nsmul_eq_mul, mul_one, mul_neg, mul_one]
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
    (fun t => s t = true)
  simp only [card_univ] at h
  norm_cast at *
  omega

private theorem source_sum (β n : ℕ) :
    W β n = ∑ s : Fin (2 * n) → Bool × Bool,
      |((((sampleEquiv (2 * n)) s).1.card : ℚ) - n) ^ 2 -
        ((((sampleEquiv (2 * n)) s).2.card : ℚ) - n) ^ 2| ^ β := by
  rw [W_shift]
  rw [← (sampleEquiv (2 * n)).sum_comp]
  rw [Fintype.sum_prod_type]
  symm
  rw [sum_by_card]
  simp only [Fintype.card_fin]
  apply sum_congr rfl
  intro k hk
  rw [sum_by_card]
  simp only [Fintype.card_fin]
  rw [mul_sum]
  apply sum_congr rfl
  intro l hl
  ring

private theorem source_moment (r n : ℕ) :
    W (2 * r) n = ∑ s : Fin (2 * n) → Bool × Bool,
      (∑ t, U (s t)) ^ (2 * r) * (∑ t, V (s t)) ^ (2 * r) := by
  rw [source_sum]
  apply sum_congr rfl
  intro s hs
  have hu : (∑ t, U (s t)) =
      (((sampleEquiv (2 * n)) s).1.card : ℚ) - n +
        ((((sampleEquiv (2 * n)) s).2.card : ℚ) - n) := by
    simp only [U, sum_div, sum_add_distrib, sum_sign, sampleEquiv, Equiv.coe_fn_mk]
    push_cast
    ring
  have hv : (∑ t, V (s t)) =
      (((sampleEquiv (2 * n)) s).1.card : ℚ) - n -
        ((((sampleEquiv (2 * n)) s).2.card : ℚ) - n) := by
    simp only [V, sum_div, sum_sub_distrib, sum_sign, sampleEquiv, Equiv.coe_fn_mk]
    push_cast
    ring
  rw [hu, hv, ← mul_pow, sq_sub_sq, abs_pow, pow_mul]
  simp only [pow_two]
  ring

end
end D5.S3.ArithSums.BrentEvenMomentPolynomial
