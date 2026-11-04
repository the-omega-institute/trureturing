/- GID: D5/S3/Arith/CharacterSums/QuadraticPrefixEnergy
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/QuadraticPrefixEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral partialSum identities and the triangular reduction for reflected character sums. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace D5.S3.Arith.CharacterSums.QuadraticPrefixEnergy

open scoped BigOperators

/-- Inclusive positive-index partialSum; its value at zero is the empty sum. -/
def partialSum (a : ℕ → ℤ) (r : ℕ) : ℤ := ∑ j ∈ Finset.range r, a (j + 1)

/-- The diagonal of the square accounts for the difference between the two triangles. -/
theorem twice_weighted_prefix (a : ℕ → ℤ) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, a (i + 1) * partialSum a (i + 1)) =
      partialSum a n ^ 2 + ∑ i ∈ Finset.range n, a (i + 1) ^ 2 := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    have hS : partialSum a (n + 1) = partialSum a n + a (n + 1) := by
      exact Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hS]
    calc
      _ = 2 * (∑ i ∈ Finset.range n, a (i + 1) * partialSum a (i + 1)) +
          2 * a (n + 1) * (partialSum a n + a (n + 1)) := by ring
      _ = _ := by rw [ih]; ring

theorem twice_weighted_predecessor (a : ℕ → ℤ) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, a (i + 1) * partialSum a i) =
      partialSum a n ^ 2 - ∑ i ∈ Finset.range n, a (i + 1) ^ 2 := by
  have h := twice_weighted_prefix a n
  have hs : (∑ i ∈ Finset.range n, a (i + 1) * partialSum a (i + 1)) =
      (∑ i ∈ Finset.range n, a (i + 1) * partialSum a i) +
        ∑ i ∈ Finset.range n, a (i + 1) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi : partialSum a (i + 1) = partialSum a i + a (i + 1) :=
      Finset.sum_range_succ _ _
    rw [hi]
    ring
  rw [hs] at h
  linarith

/-- Splitting a translated interval at its midpoint and reflecting its upper part.
There is no division in this integral identity. -/
theorem reflected_row_sum (a : ℕ → ℤ) (n i : ℕ) (hi : i ≤ n) (ε : ℤ)
    (hreflect : ∀ r, 1 ≤ r → r ≤ n → a (2 * n + 1 - r) = ε * a r) :
    (∑ k ∈ Finset.range n, a (i + k + 1)) =
      (1 + ε) * partialSum a n - partialSum a i - ε * partialSum a (n - i) := by
  have hsplit₁ : partialSum a (n + i) = partialSum a n +
      ∑ k ∈ Finset.range i, a (n + k + 1) := by
    exact Finset.sum_range_add _ _ _
  have hsplit₂ : partialSum a (n + i) = partialSum a i +
      ∑ k ∈ Finset.range n, a (i + k + 1) := by
    rw [Nat.add_comm n i]
    exact Finset.sum_range_add _ _ _
  have hsplit₃ : partialSum a n = partialSum a (n - i) +
      ∑ k ∈ Finset.range i, a (n - i + k + 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hi]
    exact Finset.sum_range_add _ _ _
  have hu : (∑ k ∈ Finset.range i, a (n + k + 1)) =
      ε * (partialSum a n - partialSum a (n - i)) := by
    calc
      _ = ∑ k ∈ Finset.range i, ε * a (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        have harg : n + k + 1 = 2 * n + 1 - (n - k) := by omega
        rw [harg, hreflect _ (by omega) (by omega)]
      _ = ε * (∑ k ∈ Finset.range i, a (n - k)) := (Finset.mul_sum _ _ _).symm
      _ = ε * (∑ k ∈ Finset.range i, a (n - i + k + 1)) := by
        congr 1
        rw [← Finset.sum_range_reflect (fun k => a (n - i + k + 1)) i]
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        have := Finset.mem_range.mp hk
        omega
      _ = _ := by rw [hsplit₃]; ring
  rw [hu] at hsplit₁
  linarith

/-- Splitting a difference row at its unique zero argument. The negative part is
reflected before summation, so no out-of-range natural subtraction is used for χ. -/
theorem difference_row_sum (χ : ℤ → ℤ) (n i : ℕ) (hi₀ : 1 ≤ i) (hi : i ≤ n)
    (ε : ℤ) (hzero : χ 0 = 0) (hneg : ∀ r : ℤ, χ (-r) = ε * χ r) :
    (∑ j ∈ Finset.range n, χ ((j : ℤ) + 1 - i)) =
      ε * partialSum (fun r => χ (r : ℤ)) (i - 1) +
        partialSum (fun r => χ (r : ℤ)) (n - i) := by
  have hi' : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by omega
  have hleft : (∑ j ∈ Finset.range (i - 1), χ ((j : ℤ) + 1 - i)) =
      ε * partialSum (fun r => χ (r : ℤ)) (i - 1) := by
    calc
      _ = ∑ j ∈ Finset.range (i - 1), ε * χ ((i - 1 - j : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have harg : (j : ℤ) + 1 - i = -((i - 1 - j : ℕ) : ℤ) := by omega
        rw [harg, hneg]
      _ = ε * (∑ j ∈ Finset.range (i - 1), χ ((i - 1 - j : ℕ) : ℤ)) :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by
        congr 1
        unfold partialSum
        rw [← Finset.sum_range_reflect (fun j => χ ((j + 1 : ℕ) : ℤ)) (i - 1)]
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        congr 1
        have hj' := Finset.mem_range.mp hj
        omega
  have hright : (∑ j ∈ Finset.range (1 + (n - i)),
      χ (((i - 1 : ℕ) : ℤ) + j + 1 - i)) =
        partialSum (fun r => χ (r : ℤ)) (n - i) := by
    rw [Nat.add_comm 1 (n - i), Finset.sum_range_succ']
    have hz : χ (((i - 1 : ℕ) : ℤ) + 0 + 1 - i) = 0 := by
      simpa only [hi', add_zero, sub_add_cancel, sub_self] using hzero
    simp only [Nat.cast_zero]
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    omega
  have hn : n = (i - 1) + (1 + (n - i)) := by omega
  calc
    _ = (∑ j ∈ Finset.range (i - 1), χ ((j : ℤ) + 1 - i)) +
        ∑ j ∈ Finset.range (1 + (n - i)), χ (((i - 1 : ℕ) : ℤ) + j + 1 - i) := by
      conv_lhs => rw [hn]
      rw [Finset.sum_range_add]
      simp only [Nat.cast_add]
    _ = _ := by rw [hleft, hright]

/-- Triangular reduction of the actual double product sum for any reflected sign sequence.
The square-one and cancellation hypotheses are supplied by the quadratic character. -/
theorem twice_triangle (a : ℕ → ℤ) (n : ℕ) (ε : ℤ)
    (hsq : ∀ r, 1 ≤ r → r ≤ n → a r ^ 2 = 1)
    (hreflect : ∀ r, 1 ≤ r → r ≤ n → a (2 * n + 1 - r) = ε * a r)
    (hcancel : (1 + ε) * partialSum a n = 0) :
    2 * (∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
      a (i + 1) * a (i + 1 + k + 1)) =
        -(partialSum a n ^ 2 + (n : ℤ)) -
          2 * ε * (∑ i ∈ Finset.range n, a (i + 1) * partialSum a (n - (i + 1))) := by
  have hrows : (∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
      a (i + 1) * a (i + 1 + k + 1)) =
        -(∑ i ∈ Finset.range n, a (i + 1) * partialSum a (i + 1)) -
          ε * (∑ i ∈ Finset.range n, a (i + 1) * partialSum a (n - (i + 1))) := by
    calc
      _ = ∑ i ∈ Finset.range n,
          (-a (i + 1) * partialSum a (i + 1) -
            ε * (a (i + 1) * partialSum a (n - (i + 1)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum, reflected_row_sum a n (i + 1)
          (by have := Finset.mem_range.mp hi; omega) ε hreflect, hcancel]
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum, neg_mul]
  have hdiag : (∑ i ∈ Finset.range n, a (i + 1) ^ 2) = (n : ℤ) := by
    calc
      _ = ∑ _i ∈ Finset.range n, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsq _ (by omega) (by have := Finset.mem_range.mp hi; omega)
      _ = _ := by simp
  have hpref := twice_weighted_prefix a n
  rw [hdiag] at hpref
  rw [hrows]
  linarith

/-- Prefixes of sign sequences have the parity of their length. -/
theorem prefix_mod_two (a : ℕ → ℤ) (n : ℕ)
    (hsq : ∀ r, 1 ≤ r → r ≤ n → a r ^ 2 = 1) :
    partialSum a n % 2 = (n : ℤ) % 2 := by
  revert hsq
  induction n with
  | zero => intro _; simp [partialSum]
  | succ n ih =>
    intro hsq
    have hp := ih (fun r hr hn => hsq r hr (by omega))
    have hv : a (n + 1) % 2 = 1 := by
      rcases sq_eq_one_iff.mp (hsq (n + 1) (by omega) (by omega)) with h | h <;>
        rw [h] <;> norm_num
    have hS : partialSum a (n + 1) = partialSum a n + a (n + 1) :=
      Finset.sum_range_succ _ _
    rw [hS]
    omega

/-- The even-case vector, defined by the integer quotient used in the ordinary proof. -/
def evenB (a : ℕ → ℤ) (n i : ℕ) : ℤ := -(partialSum a i + partialSum a (n - i)) / 2

theorem twice_evenB (a : ℕ → ℤ) (m i : ℕ) (hi : i ≤ 2 * m)
    (hsq : ∀ r, 1 ≤ r → r ≤ 2 * m → a r ^ 2 = 1) :
    2 * evenB a (2 * m) i = -(partialSum a i + partialSum a (2 * m - i)) := by
  have h₁ := prefix_mod_two a i (fun r hr hi' => hsq r hr (by omega))
  have h₂ := prefix_mod_two a (2 * m - i) (fun r hr hi' => hsq r hr (by omega))
  have hn : (2 * m - i : ℕ) + i = 2 * m := by omega
  have hn' : ((2 * m - i : ℕ) : ℤ) + (i : ℤ) = 2 * m := by exact_mod_cast hn
  unfold evenB
  omega

theorem evenB_reflect (a : ℕ → ℤ) (n i : ℕ) (hi : i ≤ n) :
    evenB a n (n - i) = evenB a n i := by
  simp only [evenB, Nat.sub_sub_self hi, add_comm]

theorem evenB_midpoint (a : ℕ → ℤ) (m : ℕ) :
    evenB a (2 * m) m = -partialSum a m := by
  have hi : 2 * m - m = m := by omega
  rw [evenB, hi]
  omega

/-- The odd-case vector; integrality is proved rather than imposed as a premise. -/
def oddB (a : ℕ → ℤ) (n i : ℕ) : ℤ :=
  (partialSum a (n - i) - partialSum a (i - 1)) / 2

theorem twice_oddB (a : ℕ → ℤ) (m i : ℕ) (hi₀ : 1 ≤ i) (hi : i ≤ 2 * m + 1)
    (hsq : ∀ r, 1 ≤ r → r ≤ 2 * m + 1 → a r ^ 2 = 1) :
    2 * oddB a (2 * m + 1) i = partialSum a (2 * m + 1 - i) - partialSum a (i - 1) := by
  have h₁ := prefix_mod_two a (2 * m + 1 - i)
    (fun r hr hi' => hsq r hr (by omega))
  have h₂ := prefix_mod_two a (i - 1) (fun r hr hi' => hsq r hr (by omega))
  have hn : (2 * m + 1 - i : ℕ) + i = 2 * m + 1 := by omega
  have hn' : ((2 * m + 1 - i : ℕ) : ℤ) + (i : ℤ) = 2 * m + 1 := by
    exact_mod_cast hn
  have hi' : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by omega
  unfold oddB
  omega

theorem oddB_reflect (a : ℕ → ℤ) (m i : ℕ) (hi₀ : 1 ≤ i) (hi : i ≤ 2 * m + 1)
    (hsq : ∀ r, 1 ≤ r → r ≤ 2 * m + 1 → a r ^ 2 = 1) :
    oddB a (2 * m + 1) (2 * m + 2 - i) = -oddB a (2 * m + 1) i := by
  have hj₀ : 1 ≤ 2 * m + 2 - i := by omega
  have hj : 2 * m + 2 - i ≤ 2 * m + 1 := by omega
  have h₁ := twice_oddB a m i hi₀ hi hsq
  have h₂ := twice_oddB a m (2 * m + 2 - i) hj₀ hj hsq
  have ht : 2 * m + 1 - (2 * m + 2 - i) = i - 1 := by omega
  have hu : 2 * m + 2 - i - 1 = 2 * m + 1 - i := by omega
  rw [ht, hu] at h₂
  linarith

theorem oddB_midpoint (a : ℕ → ℤ) (m : ℕ) : oddB a (2 * m + 1) (m + 1) = 0 := by
  have hi : 2 * m + 1 - (m + 1) = m := by omega
  simp [oddB, hi]

/-- A reflection on an odd interval pairs every term except its midpoint. -/
theorem sum_odd_reflection (f : ℕ → ℤ) (m : ℕ)
    (hreflect : ∀ j, j < m → f (2 * m - j) = f j) :
    (∑ j ∈ Finset.range (2 * m + 1), f j) =
      2 * (∑ j ∈ Finset.range m, f j) + f m := by
  have hu : (∑ j ∈ Finset.range m, f (m + 1 + j)) =
      ∑ j ∈ Finset.range m, f j := by
    calc
      _ = ∑ j ∈ Finset.range m, f (m - 1 - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have harg : m + 1 + j = 2 * m - (m - 1 - j) := by omega
        rw [harg, hreflect _ (by omega)]
      _ = _ := Finset.sum_range_reflect f m
  have hn : 2 * m + 1 = m + (m + 1) := by omega
  rw [hn, Finset.sum_range_add, Finset.sum_range_succ']
  simp only [Nat.add_zero]
  have hshift : (∑ j ∈ Finset.range m, f (m + (j + 1))) =
      ∑ j ∈ Finset.range m, f j := by
    simpa only [Nat.add_right_comm m, Nat.add_assoc] using hu
  rw [hshift]
  ring

/-- The odd-case square norm is twice its lower half, with a proved zero midpoint. -/
theorem oddB_square_sum (a : ℕ → ℤ) (m : ℕ)
    (hsq : ∀ r, 1 ≤ r → r ≤ 2 * m + 1 → a r ^ 2 = 1) :
    (∑ j ∈ Finset.range (2 * m + 1), oddB a (2 * m + 1) (j + 1) ^ 2) =
      2 * (∑ j ∈ Finset.range m, oddB a (2 * m + 1) (j + 1) ^ 2) := by
  have h := sum_odd_reflection (fun j => oddB a (2 * m + 1) (j + 1) ^ 2) m
    (fun j hj => by
      have hr := oddB_reflect a m (j + 1) (by omega) (by omega) hsq
      have harg : 2 * m + 2 - (j + 1) = 2 * m - j + 1 := by omega
      rw [harg] at hr
      rw [hr, neg_sq])
  simpa only [oddB_midpoint, zero_pow two_ne_zero, add_zero] using h

/-- The odd-integer identity is kept modulo 32 before cancellation of the factor two.
The exponent is the natural quotient from the original class-number statement. -/
theorem odd_sign_square_mod32 (h : ℕ) (hh : Odd h) :
    Int.ModEq 32 ((h : ℤ) ^ 2 + 2 * (-1 : ℤ) ^ ((h - 1) / 2) * h) 3 := by
  obtain ⟨k, hk⟩ := hh
  have hexp : (h - 1) / 2 = k := by omega
  rw [hexp]
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow]
    obtain ⟨t, ht⟩ := he
    have hk' : k = 2 * t := by omega
    have hh' : h = 4 * t + 1 := by omega
    rw [hh']
    obtain ⟨r, hr⟩ := even_iff_two_dvd.mp (Int.even_mul_succ_self (t : ℤ))
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-r, ?_⟩
    push_cast
    nlinarith [hr]
  · rw [ho.neg_one_pow]
    obtain ⟨t, ht⟩ := ho
    have hh' : h = 4 * t + 3 := by omega
    rw [hh']
    obtain ⟨r, hr⟩ := even_iff_two_dvd.mp (Int.even_mul_succ_self (t : ℤ))
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-r, ?_⟩
    push_cast
    nlinarith [hr]

end D5.S3.Arith.CharacterSums.QuadraticPrefixEnergy
