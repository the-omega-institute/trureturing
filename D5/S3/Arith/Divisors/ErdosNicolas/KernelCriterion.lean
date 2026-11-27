/- GID: D5/S3/Arith/Divisors/ErdosNicolas/KernelCriterion
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/ErdosNicolas/KernelCriterion
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Rational kernel criteria for reciprocal divisor gaps. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Basic
import D5.S3.Arith.Divisors.ErdosNicolas.TentKernel
import D5.S3.Arith.Divisors.ErdosNicolas.DivisorBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- The rational gap left after paying the two within-block bounds and the residual. -/
def criterionGap (a : ℕ) (p bA bB F : ℚ) : ℚ :=
  a + 1 - bA - a * bB / p - F

/-- The two exact comparisons required by the kernel criterion. -/
def KernelTest (a : ℕ) (p L bA bB F : ℚ) : Prop :=
  0 < criterionGap a p bA bB F ∧
    4 * a * (bA + 1 / L) * (bB / p + 1 / L) < (criterionGap a p bA bB F) ^ 2

/-- The square comparison avoids square roots and is valid over the rationals. -/
private theorem kernel_criterion_algebra {a : ℕ} {p L bA bB F H C t : ℚ}
    (ht : 0 < t) (h : KernelTest a p L bA bB F)
    (hH : H ≤ bA * t + bB * a * t / p + C + F * t)
    (hC : C ^ 2 ≤ 4 * a * t ^ 2 * (bA + 1 / L) * (bB / p + 1 / L)) :
    H < ((a : ℚ) + 1) * t := by
  rcases h with ⟨hR, hsq⟩
  have htR : 0 < t * criterionGap a p bA bB F := mul_pos ht hR
  have hh := mul_lt_mul_of_pos_left hsq (sq_pos_of_pos ht)
  have hC' : C ^ 2 < (t * criterionGap a p bA bB F) ^ 2 := by
    nlinarith only [hC, hh]
  have hlt : C < t * criterionGap a p bA bB F := by
    by_contra hn
    have he := mul_self_le_mul_self htR.le (le_of_not_gt hn)
    nlinarith only [hC', he]
  calc
    H ≤ bA * t + bB * a * t / p + C + F * t := hH
    _ < bA * t + bB * a * t / p + t * criterionGap a p bA bB F + F * t :=
      by linarith only [hlt]
    _ = ((a : ℚ) + 1) * t := by unfold criterionGap; ring

/-- Reciprocal cross-block distances; the diagonal is zero by the field convention. -/
def crossInv (A B : Finset ℕ) : ℚ :=
  ∑ x ∈ A, ∑ y ∈ B, ((Nat.dist x y : ℕ) : ℚ)⁻¹

/-- The remaining short-distance contribution between two blocks. -/
def crossResidual (L : ℕ) (A B : Finset ℕ) : ℚ :=
  ∑ x ∈ A, ∑ y ∈ B, w L (Nat.dist x y)

private theorem crossInv_symm (A B : Finset ℕ) : crossInv A B = crossInv B A := by
  unfold crossInv
  rw [sum_comm]
  simp_rw [Nat.dist_comm]

private theorem pairSum_union {A B : Finset ℕ} (hAB : Disjoint A B) :
    pairSum (A ∪ B) = pairSum A + pairSum B + crossInv A B := by
  have hfull : crossInv (A ∪ B) (A ∪ B) =
      crossInv A A + crossInv A B + crossInv B A + crossInv B B := by
    unfold crossInv
    rw [sum_union hAB]
    simp_rw [sum_union hAB, sum_add_distrib]
    ring
  have h := sum_inv_dist (A ∪ B)
  have hA := sum_inv_dist A
  have hB := sum_inv_dist B
  change crossInv (A ∪ B) (A ∪ B) = _ at h
  change crossInv A A = _ at hA
  change crossInv B B = _ at hB
  rw [hfull, crossInv_symm B A, hA, hB] at h
  linarith

/-- On disjoint blocks every reciprocal splits into its kernel and residual parts. -/
private theorem crossInv_eq_energy_add_residual {L : ℕ}
    {A B : Finset ℕ} (hAB : Disjoint A B) :
    crossInv A B = energy L A B + crossResidual L A B := by
  unfold crossInv energy crossResidual
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro y hy
  have hxy : x ≠ y := by
    intro he
    subst y
    exact (disjoint_left.mp hAB hx) hy
  exact inv_eq_K_add_w (Nat.dist_pos_of_ne hxy)

/-- Diagonal plus off-diagonal reciprocal control of a block's kernel energy. -/
private theorem energy_self_le (L : ℕ) (A : Finset ℕ) :
    energy L A A ≤ 2 * (pairSum A + (A.card : ℚ) / L) := by
  have hpoint (x y : ℕ) : K L (Nat.dist x y) ≤
      ((Nat.dist x y : ℕ) : ℚ)⁻¹ + if x = y then 2 / (L : ℚ) else 0 := by
    by_cases hxy : x = y
    · subst y
      simp
    · simp only [if_neg hxy, add_zero]
      exact K_le_inv (Nat.dist_pos_of_ne hxy)
  calc
    energy L A A ≤ ∑ x ∈ A, ∑ y ∈ A,
        (((Nat.dist x y : ℕ) : ℚ)⁻¹ + if x = y then 2 / (L : ℚ) else 0) := by
      exact sum_le_sum fun x _ => sum_le_sum fun y _ => hpoint x y
    _ = 2 * (pairSum A + (A.card : ℚ) / L) := by
      simp_rw [sum_add_distrib]
      rw [sum_inv_dist]
      have hd : (∑ x ∈ A, ∑ y ∈ A, if x = y then 2 / (L : ℚ) else 0) =
          (A.card : ℚ) * (2 / L) := by
        calc
          _ = ∑ _x ∈ A, 2 / (L : ℚ) := by
            apply sum_congr rfl
            intro x hx
            simp [hx]
          _ = _ := by simp
      rw [hd]
      ring

/-- Finite-set version of the criterion, independent of prime factorization. -/
theorem kernel_criterion_blocks {a L : ℕ} {A B : Finset ℕ} {p bA bB F : ℚ}
    (hL : 0 < L) (hAB : Disjoint A B) (ht : 0 < A.card)
    (hcard : B.card ≤ a * A.card)
    (hA : pairSum A ≤ bA * A.card)
    (hB : pairSum B ≤ bB * a * A.card / p)
    (hF : crossResidual L A B ≤ F * A.card)
    (hTest : KernelTest a p L bA bB F) :
    pairSum (A ∪ B) < ((a : ℚ) + 1) * A.card := by
  have hEA : energy L A A ≤ 2 * (A.card : ℚ) * (bA + 1 / L) := by
    calc
      _ ≤ 2 * (pairSum A + (A.card : ℚ) / L) := energy_self_le L A
      _ ≤ 2 * (bA * A.card + (A.card : ℚ) / L) := by linarith only [hA]
      _ = _ := by ring
  have hc : (B.card : ℚ) ≤ (a : ℚ) * A.card := by exact_mod_cast hcard
  have hEB : energy L B B ≤ 2 * a * (A.card : ℚ) * (bB / p + 1 / L) := by
    have h := energy_self_le L B
    have hcL := div_le_div_of_nonneg_right hc
      (show (0 : ℚ) ≤ L by positivity)
    calc
      _ ≤ 2 * (pairSum B + (a : ℚ) * A.card / L) := by linarith only [h, hcL]
      _ ≤ 2 * (bB * a * A.card / p + (a : ℚ) * A.card / L) :=
        by linarith only [hB]
      _ = _ := by ring
  have hEA0 := energy_nonneg L A A
  have hEB0 := energy_nonneg L B B
  have hC : energy L A B ^ 2 ≤
      4 * a * (A.card : ℚ) ^ 2 * (bA + 1 / L) * (bB / p + 1 / L) := by
    calc
      _ ≤ energy L A A * energy L B B := energy_sq_le hL A B
      _ ≤ (2 * (A.card : ℚ) * (bA + 1 / L)) *
          (2 * a * (A.card : ℚ) * (bB / p + 1 / L)) :=
        mul_le_mul hEA hEB hEB0 (hEA0.trans hEA)
      _ = _ := by ring
  apply kernel_criterion_algebra (by exact_mod_cast ht) hTest _ hC
  rw [pairSum_union hAB, crossInv_eq_energy_add_residual hAB]
  linarith only [hA, hB, hF]

/-- The general mathematical reduction, with the residual bound supplied by a checker. -/
theorem kernel_criterion_prime_power {p a m L : ℕ} {bA bB F : ℚ}
    (hp : p.Prime) (hpm : ¬p ∣ m) (hL : 0 < L)
    (hA : hHat m ≤ bA * m.divisors.card)
    (hB : hHat ((p ^ a * m) / p) ≤ bB * a * m.divisors.card)
    (hF : crossResidual L m.divisors
      (((p ^ a * m) / p).divisors.image (p * ·)) ≤ F * m.divisors.card)
    (hTest : KernelTest a p L bA bB F) :
    hHat (p ^ a * m) < ((p ^ a * m).divisors.card : ℚ) := by
  have hm : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  have ht : 0 < m.divisors.card := card_pos.mpr
    ⟨1, Nat.one_mem_divisors.mpr hm⟩
  by_cases ha0 : a = 0
  · subst a
    have htq : (0 : ℚ) < m.divisors.card := by exact_mod_cast ht
    have hres : 0 ≤ crossResidual L m.divisors
        (((p ^ 0 * m) / p).divisors.image (p * ·)) :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => w_nonneg _ _
    have hF0 : 0 ≤ F := (mul_nonneg_iff_of_pos_right htq).mp (hres.trans hF)
    have hgap := hTest.1
    simp only [criterionGap, Nat.cast_zero, zero_add, mul_zero, zero_mul,
      zero_div, sub_zero] at hgap
    have hba : bA < 1 := by linarith only [hgap, hF0]
    simpa only [pow_zero, one_mul] using hA.trans_lt
      (by simpa only [one_mul] using mul_lt_mul_of_pos_right hba htq)
  have ha : 0 < a := Nat.pos_of_ne_zero ha0
  have hAB := prime_power_divisor_blocks_disjoint (a := a) hpm
  have hcard := prime_power_divisor_block_card hp ha hpm
  rw [prime_power_mul_div hp.pos ha] at hB hF
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hB' : pairSum ((p ^ (a - 1) * m).divisors.image (p * ·)) ≤
      bB * a * m.divisors.card / (p : ℚ) := by
    rw [pairSum_mul_image p]
    exact div_le_div_of_nonneg_right hB hpq.le
  have h := kernel_criterion_blocks hL hAB ht hcard.le hA hB' hF hTest
  rw [← prime_power_divisors_partition hp ha] at h
  unfold hHat
  rw [card_divisors_prime_power_mul hp hpm]
  push_cast
  exact h

#print axioms kernel_criterion_algebra
#print axioms pairSum_union
#print axioms crossInv_eq_energy_add_residual
#print axioms energy_self_le
#print axioms kernel_criterion_blocks
#print axioms kernel_criterion_prime_power

end D5.S3.Arith.ErdosNicolas
