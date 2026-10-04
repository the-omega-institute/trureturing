/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGrowth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGrowth
   mirror-E: none(waiver:integral-metallic-coefficient-growth)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Catalan.Basic]
   utility: none
   digest: Catalan majorants control the coefficients of every integral metallic solution. -/

import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedGrowth

open PowerSeries Finset MetallicHankelDefs

/-- The defining quadratic equation has an exponential integral coefficient majorant. -/
theorem coefficient_growth (n : ℕ) (hn : 1 ≤ n) (Φ : PowerSeries ℤ)
    (hΦ : IsMetallic n Φ) (m : ℕ) :
    (coeff m Φ).natAbs ≤ (4 * (n + 5)) ^ m := by
  classical
  let c := n + 5
  have hc : 1 ≤ c := by dsimp [c]; omega
  have step (d : ℕ) : catalan d ≤ catalan (d + 1) := by
    rw [catalan_succ]
    have h := Finset.single_le_sum (f := fun i : Fin (d + 1) =>
      catalan i * catalan (d - i)) (fun i _ => Nat.zero_le _) (mem_univ (0 : Fin (d + 1)))
    simpa using h
  have mono : Monotone catalan := monotone_nat_of_le_succ step
  have majorant : ∀ m, (coeff m Φ).natAbs ≤ c ^ m * catalan m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      cases m with
      | zero =>
          simp [coeff_zero_eq_constantCoeff, hΦ.1]
      | succ m =>
          have lower (r : ℕ) (hr : r ≤ m) :
              (coeff r Φ).natAbs ≤ c ^ m * catalan (m + 1) := by
            exact (ih r (by omega)).trans
              (Nat.mul_le_mul (Nat.pow_le_pow_right hc hr) (mono (by omega)))
          have shift (a : ℕ) (ha : 1 ≤ a) :
              (coeff (m + 1) (X ^ a * Φ)).natAbs ≤ c ^ m * catalan (m + 1) := by
            rw [coeff_X_pow_mul']
            split_ifs with h
            · exact lower _ (by omega)
            · simp
          have quadratic : (coeff m (Φ ^ 2)).natAbs ≤ c ^ m * catalan (m + 1) := by
            rw [pow_two, coeff_mul]
            refine (Int.natAbs_sum_le _ _).trans ?_
            calc
              (∑ p ∈ antidiagonal m, (coeff p.1 Φ * coeff p.2 Φ).natAbs) ≤
                  ∑ p ∈ antidiagonal m, c ^ m * (catalan p.1 * catalan p.2) := by
                apply sum_le_sum
                intro p hp
                have he := mem_antidiagonal.mp hp
                rw [Int.natAbs_mul]
                calc
                  (coeff p.1 Φ).natAbs * (coeff p.2 Φ).natAbs ≤
                      (c ^ p.1 * catalan p.1) * (c ^ p.2 * catalan p.2) :=
                    Nat.mul_le_mul (ih _ (by omega)) (ih _ (by omega))
                  _ = c ^ m * (catalan p.1 * catalan p.2) := by
                    rw [← mul_mul_mul_comm, ← pow_add, he]
              _ = c ^ m * catalan (m + 1) := by rw [← mul_sum, ← catalan_succ']
          have equation : Φ = 1 - X * Φ ^ 2 + X * Φ - X ^ n * Φ +
              X ^ (n + 1) * Φ + ∑ i ∈ range n, X ^ (i + 1) * Φ := by
            have he := hΦ.2
            dsimp [linearCoeff] at he
            have hs : X * (∑ i ∈ range n, X ^ i) * Φ =
                ∑ i ∈ range n, X ^ (i + 1) * Φ := by
              rw [Finset.mul_sum, Finset.sum_mul]
              apply sum_congr rfl
              intro i hi
              rw [pow_succ]
              ring
            rw [← hs]
            apply sub_eq_zero.mp
            calc
              _ = (X * Φ ^ 2 +
                  ((1 + X ^ n) * (1 - X) - X * ∑ i ∈ range n, X ^ i) * Φ) - 1 := by
                rw [pow_succ]
                ring
              _ = 0 := sub_eq_zero.mpr he
          have recurrence := congrArg (coeff (m + 1)) equation
          simp only [map_add, map_sub, coeff_one, Nat.add_eq_zero_iff, Nat.one_ne_zero,
            and_false, if_false, zero_sub, coeff_succ_X_mul, map_sum] at recurrence
          rw [recurrence]
          have hsum : (∑ i ∈ range n, coeff (m + 1) (X ^ (i + 1) * Φ)).natAbs ≤
              n * (c ^ m * catalan (m + 1)) := by
            refine (Int.natAbs_sum_le _ _).trans ?_
            calc
              (∑ i ∈ range n, (coeff (m + 1) (X ^ (i + 1) * Φ)).natAbs) ≤
                  ∑ _i ∈ range n, c ^ m * catalan (m + 1) := by
                apply sum_le_sum
                intro i hi
                exact shift (i + 1) (by omega)
              _ = n * (c ^ m * catalan (m + 1)) := by simp
          calc
            _ ≤ (coeff m (Φ ^ 2)).natAbs + (coeff m Φ).natAbs +
                (coeff (m + 1) (X ^ n * Φ)).natAbs +
                (coeff (m + 1) (X ^ (n + 1) * Φ)).natAbs +
                (∑ i ∈ range n, coeff (m + 1) (X ^ (i + 1) * Φ)).natAbs := by
              calc
                _ ≤ (-coeff m (Φ ^ 2) + coeff m Φ -
                    coeff (m + 1) (X ^ n * Φ) +
                    coeff (m + 1) (X ^ (n + 1) * Φ)).natAbs +
                    (∑ i ∈ range n, coeff (m + 1) (X ^ (i + 1) * Φ)).natAbs :=
                  Int.natAbs_add_le _ _
                _ ≤ _ := by
                  have hA := Int.natAbs_add_le (-coeff m (Φ ^ 2)) (coeff m Φ)
                  have hB := Int.natAbs_sub_le (-coeff m (Φ ^ 2) + coeff m Φ)
                    (coeff (m + 1) (X ^ n * Φ))
                  have hC := Int.natAbs_add_le
                    (-coeff m (Φ ^ 2) + coeff m Φ - coeff (m + 1) (X ^ n * Φ))
                    (coeff (m + 1) (X ^ (n + 1) * Φ))
                  simp only [Int.natAbs_neg] at hA
                  omega
            _ ≤ (n + 4) * (c ^ m * catalan (m + 1)) := by
              have h₀ := quadratic
              have h₁ := lower m (le_refl m)
              have h₂ := shift n hn
              have h₃ := shift (n + 1) (by omega)
              calc
                _ ≤ c ^ m * catalan (m + 1) + c ^ m * catalan (m + 1) +
                    c ^ m * catalan (m + 1) + c ^ m * catalan (m + 1) +
                    n * (c ^ m * catalan (m + 1)) :=
                  add_le_add (add_le_add (add_le_add (add_le_add h₀ h₁) h₂) h₃) hsum
                _ = _ := by ring
            _ ≤ c ^ (m + 1) * catalan (m + 1) := by
              rw [pow_succ]
              calc
                _ ≤ c * (c ^ m * catalan (m + 1)) := by
                  apply Nat.mul_le_mul_right
                  dsimp [c]
                  omega
                _ = _ := by ring
  calc
    (coeff m Φ).natAbs ≤ c ^ m * catalan m := majorant m
    _ ≤ c ^ m * 4 ^ m := by
      apply Nat.mul_le_mul_left
      rw [catalan_eq_centralBinom_div]
      exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow m)
    _ = (4 * (n + 5)) ^ m := by rw [← mul_pow]; dsimp [c]; congr 1; omega

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedGrowth
