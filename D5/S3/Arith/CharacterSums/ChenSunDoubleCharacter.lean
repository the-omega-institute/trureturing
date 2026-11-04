/- GID: D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter
   generality: I
   mirror-B: D5/B/S3/Arith/CharacterSums/ChenSunDoubleCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Chen-Sun double sum and its unconditional integral triangular reduction. -/

import D5.S3.Arith.CharacterSums.QuadraticCharacterGram
import D5.S3.Arith.CharacterSums.QuadraticPrefixEnergy
import D5.S3.Arith.CharacterSums.QuadraticSignProducts

namespace D5.S3.Arith.CharacterSums.ChenSunDoubleCharacter

open scoped BigOperators
open D5.S3.Arith.CharacterSums.QuadraticPrefixEnergy D5.S3.Arith.CharacterSums.QuadraticCharacterGram

/-- Literal equation (1.8) of Chen-Sun arXiv:2409.08213v4; both endpoints are inclusive. -/
def doubleSum (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ j ∈ Finset.Icc 1 ((p - 1) / 2), ∑ k ∈ Finset.Icc 1 ((p - 1) / 2),
    legendreSym p ((j : ℤ) ^ 2 + (j : ℤ) * k)

variable (p : ℕ) [Fact p.Prime]

private theorem lower_sign_sq {r : ℕ} (hr : 1 ≤ r) (hn : r ≤ (p - 1) / 2) :
    legendreSym p (r : ℤ) ^ 2 = 1 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hrp : r < p := by omega
  apply legendreSym.sq_one
  push_cast
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_cast_of_lt hrp, ZMod.val_zero] at hv
  omega

private theorem reflection (hp : p ≠ 2) {r : ℕ} (hr : 1 ≤ r) (hn : r ≤ (p - 1) / 2) :
    legendreSym p ((2 * ((p - 1) / 2) + 1 - r : ℕ) : ℤ) =
      legendreSym p (-1) * legendreSym p (r : ℤ) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  have hp0 := (Fact.out : p.Prime).pos
  have hpn : 2 * ((p - 1) / 2) + 1 = p := by omega
  have hrp : r ≤ p := by omega
  simp only [legendreSym, Int.cast_natCast, Int.cast_neg, Int.cast_one]
  rw [hpn, Nat.cast_sub hrp, ZMod.natCast_self, zero_sub,
    neg_eq_neg_one_mul, map_mul]

private theorem cancellation (hp : p ≠ 2) :
    (1 + legendreSym p (-1)) * partialSum (fun r => legendreSym p (r : ℤ)) ((p - 1) / 2) = 0 := by
  have h := prime_half_character_cancellation p hp
  rw [sum_primeHalf] at h
  simpa [partialSum, legendreSym] using h

/-- Multiplicativity changes each summand into the row form used by the Gram identity. -/
theorem doubleSum_eq_row_sum :
    doubleSum p =
      ∑ i ∈ Finset.range ((p - 1) / 2), ∑ k ∈ Finset.range ((p - 1) / 2),
        legendreSym p ((i + 1 : ℕ) : ℤ) *
          legendreSym p ((i + 1 + k + 1 : ℕ) : ℤ) := by
  let n := (p - 1) / 2
  have hIcc (f : ℕ → ℤ) : (∑ j ∈ Finset.Icc 1 n, f j) =
      ∑ i ∈ Finset.range n, f (i + 1) := by
    have hset : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  unfold doubleSum
  change (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
    legendreSym p ((j : ℤ) ^ 2 + (j : ℤ) * k)) = _
  simp_rw [hIcc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [← legendreSym.mul]
  congr 1
  push_cast
  ring

/-- Unconditional integral triangular identity for every odd prime; no class-number input. -/
theorem twice_doubleSum_triangle (hp : p ≠ 2) :
    2 * doubleSum p =
      -(partialSum (fun r => legendreSym p (r : ℤ)) ((p - 1) / 2) ^ 2 +
        (((p - 1) / 2 : ℕ) : ℤ)) -
      2 * legendreSym p (-1) *
        (∑ i ∈ Finset.range ((p - 1) / 2),
          legendreSym p ((i + 1 : ℕ) : ℤ) *
            partialSum (fun r => legendreSym p (r : ℤ)) ((p - 1) / 2 - (i + 1))) := by
  rw [doubleSum_eq_row_sum]
  exact twice_triangle (fun r => legendreSym p (r : ℤ)) ((p - 1) / 2)
    (legendreSym p (-1)) (fun _ hr hn => lower_sign_sq p hr hn)
    (fun _ hr hn => reflection p hp hr hn) (cancellation p hp)

/-- Actual column sums of the two restricted character matrices, with integer arguments. -/
def columnSum (t : ℤ) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range ((p - 1) / 2),
    (legendreSym p ((j : ℤ) + 1 + i) + t * legendreSym p ((j : ℤ) + 1 - i))

theorem columnSum_eq_prefix (hp : p ≠ 2) (t : ℤ) {i : ℕ}
    (hi₀ : 1 ≤ i) (hi : i ≤ (p - 1) / 2) :
    columnSum p t i =
      -partialSum (fun r => legendreSym p (r : ℤ)) i +
        (t - legendreSym p (-1)) * partialSum (fun r => legendreSym p (r : ℤ)) ((p - 1) / 2 - i) +
          t * legendreSym p (-1) * partialSum (fun r => legendreSym p (r : ℤ)) (i - 1) := by
  have hplus : (∑ j ∈ Finset.range ((p - 1) / 2),
      legendreSym p ((j : ℤ) + 1 + i)) =
      (1 + legendreSym p (-1)) * partialSum (fun r => legendreSym p (r : ℤ)) ((p - 1) / 2) -
        partialSum (fun r => legendreSym p (r : ℤ)) i -
          legendreSym p (-1) * partialSum (fun r => legendreSym p (r : ℤ)) ((p - 1) / 2 - i) := by
    convert reflected_row_sum (fun r => legendreSym p (r : ℤ)) ((p - 1) / 2) i hi
      (legendreSym p (-1)) (fun _ hr hn => reflection p hp hr hn) using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  have hminus := difference_row_sum (legendreSym p) ((p - 1) / 2) i hi₀ hi
    (legendreSym p (-1)) (legendreSym.at_zero p) (fun r => by
      rw [neg_eq_neg_one_mul, legendreSym.mul])
  rw [columnSum, Finset.sum_add_distrib, ← Finset.mul_sum, hplus, hminus, cancellation p hp]
  ring

/-- Restricted Gram energy transported to the literal natural interval. -/
theorem column_energy (hp : p ≠ 2) (t : ℤ) (ht : t = 1 ∨ t = -1) :
    (∑ i ∈ Finset.range ((p - 1) / 2), columnSum p t (i + 1) ^ 2) =
      (p : ℤ) * (((p - 1) / 2 : ℕ) : ℤ) -
        (1 + t * legendreSym p (-1)) * (((p - 1) / 2 : ℕ) : ℤ) ^ 2 -
          (1 + t) * partialSum (fun r => legendreSym p (r : ℤ)) ((p - 1) / 2) ^ 2 := by
  have h := prime_column_energy p hp t ht
  simp_rw [sum_primeHalf] at h
  simpa [columnSum, partialSum, legendreSym, Nat.cast_add, Int.cast_add, Int.cast_sub] using h

private theorem prefix_step (i : ℕ) (hi : 1 ≤ i) :
    partialSum (fun r => legendreSym p (r : ℤ)) i =
      partialSum (fun r => legendreSym p (r : ℤ)) (i - 1) + legendreSym p (i : ℤ) := by
  have hi' : i - 1 + 1 = i := by omega
  simpa only [hi', partialSum] using
    (Finset.sum_range_succ (fun j => legendreSym p ((j + 1 : ℕ) : ℤ)) (i - 1))

/-- The even-case column vector is a+4b, with b an actual integral partialSum quotient. -/
theorem even_columnSum (m : ℕ) (hpm : p = 4 * m + 1) {i : ℕ}
    (hi₀ : 1 ≤ i) (hi : i ≤ 2 * m) :
    columnSum p (-1) i = legendreSym p (i : ℤ) +
      4 * evenB (fun r => legendreSym p (r : ℤ)) (2 * m) i := by
  have hp2 : p ≠ 2 := by omega
  have hn : (p - 1) / 2 = 2 * m := by omega
  have hε : legendreSym p (-1) = 1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_one_mod_four (by omega)]
  have hcol := columnSum_eq_prefix p hp2 (-1) hi₀ (by omega : i ≤ (p - 1) / 2)
  rw [hε, hn] at hcol
  have hb := twice_evenB (fun r => legendreSym p (r : ℤ)) m i hi
    (fun r hr hn' => lower_sign_sq p hr (by omega))
  have hS := prefix_step p i hi₀
  linarith

/-- The odd-case column vector is -a+4b, with the zero midpoint included. -/
theorem odd_columnSum (m : ℕ) (hpm : p = 4 * m + 3) {i : ℕ}
    (hi₀ : 1 ≤ i) (hi : i ≤ 2 * m + 1) :
    columnSum p 1 i = -legendreSym p (i : ℤ) +
      4 * oddB (fun r => legendreSym p (r : ℤ)) (2 * m + 1) i := by
  have hp2 : p ≠ 2 := by omega
  have hn : (p - 1) / 2 = 2 * m + 1 := by omega
  have hε : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four (by omega)]
  have hcol := columnSum_eq_prefix p hp2 1 hi₀ (by omega : i ≤ (p - 1) / 2)
  rw [hε, hn] at hcol
  have hb := twice_oddB (fun r => legendreSym p (r : ℤ)) m i hi₀ hi
    (fun r hr hn' => lower_sign_sq p hr (by omega))
  have hS := prefix_step p i hi₀
  linarith

private theorem sum_lower_sign_sq (n : ℕ) (hn : n ≤ (p - 1) / 2) :
    (∑ i ∈ Finset.range n, legendreSym p ((i + 1 : ℕ) : ℤ) ^ 2) = (n : ℤ) := by
  calc
    _ = ∑ _i ∈ Finset.range n, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact lower_sign_sq p (by omega) (by omega)
    _ = _ := by simp

/-- Exact even-case energy identity. The remaining mod-sixteen step is factorial parity. -/
theorem even_energy_exact (m : ℕ) (hpm : p = 4 * m + 1) :
    doubleSum p = 2 * (m : ℤ) ^ 2 -
      4 * (∑ i ∈ Finset.range (2 * m),
        evenB (fun r => legendreSym p (r : ℤ)) (2 * m) (i + 1) ^ 2) := by
  let a : ℕ → ℤ := fun r => legendreSym p (r : ℤ)
  let b : ℕ → ℤ := evenB a (2 * m)
  let A : ℤ := ∑ i ∈ Finset.range (2 * m), a (i + 1) * b (i + 1)
  let B : ℤ := ∑ i ∈ Finset.range (2 * m), b (i + 1) ^ 2
  let T : ℤ := ∑ i ∈ Finset.range (2 * m), a (i + 1) * partialSum a (2 * m - (i + 1))
  let V : ℤ := ∑ i ∈ Finset.range (2 * m), a (i + 1) * partialSum a (i + 1)
  have hp2 : p ≠ 2 := by omega
  have hn : (p - 1) / 2 = 2 * m := by omega
  have hε : legendreSym p (-1) = 1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_one_mod_four (by omega)]
  have hc : partialSum a (2 * m) = 0 := by
    have h := cancellation p hp2
    rw [hε, hn] at h
    change (1 + 1) * partialSum a (2 * m) = 0 at h
    linarith
  have hdiag : (∑ i ∈ Finset.range (2 * m), a (i + 1) ^ 2) = (2 * m : ℕ) :=
    sum_lower_sign_sq p (2 * m) (by omega)
  have hV := twice_weighted_prefix a (2 * m)
  rw [hc, hdiag] at hV
  change 2 * V = 0 ^ 2 + ((2 * m : ℕ) : ℤ) at hV
  have htri := twice_doubleSum_triangle p hp2
  rw [hε, hn] at htri
  change 2 * doubleSum p = -(partialSum a (2 * m) ^ 2 + ((2 * m : ℕ) : ℤ)) - 2 * 1 * T at htri
  rw [hc] at htri
  have hA : 2 * A = -V - T := by
    calc
      _ = ∑ i ∈ Finset.range (2 * m), a (i + 1) * (2 * b (i + 1)) := by
        dsimp only [A]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i ∈ Finset.range (2 * m),
          (-a (i + 1) * partialSum a (i + 1) -
            a (i + 1) * partialSum a (2 * m - (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hb := twice_evenB a m (i + 1) (by omega)
          (fun r hr hn' => lower_sign_sq p hr (by omega))
        change 2 * b (i + 1) = _ at hb
        rw [hb]
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib, V, T]
  have hAd : 2 * A = doubleSum p := by linarith
  have hnorm : (∑ i ∈ Finset.range (2 * m), columnSum p (-1) (i + 1) ^ 2) =
      ((2 * m : ℕ) : ℤ) + 8 * A + 16 * B := by
    calc
      _ = ∑ i ∈ Finset.range (2 * m),
          (a (i + 1) ^ 2 + 8 * (a (i + 1) * b (i + 1)) + 16 * b (i + 1) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [even_columnSum p m hpm (by omega) (by omega)]
        change (a (i + 1) + 4 * b (i + 1)) ^ 2 = _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hdiag, A, B]
  have hE := column_energy p hp2 (-1) (Or.inr rfl)
  rw [hn, hε, hnorm] at hE
  norm_num at hE
  have hpmz : (p : ℤ) = 4 * m + 1 := by exact_mod_cast hpm
  rw [hpmz] at hE
  push_cast at hE hAd
  change doubleSum p = 2 * (m : ℤ) ^ 2 - 4 * B
  nlinarith [hE, hAd]

/-- Exact odd-case energy identity, before reflection and factorial parity reduce it modulo 32. -/
theorem odd_energy_exact (m : ℕ) (hpm : p = 4 * m + 3) :
    2 * doubleSum p = partialSum (fun r => legendreSym p (r : ℤ)) (2 * m + 1) ^ 2 -
      ((2 * m + 1 : ℕ) : ℤ) * (((2 * m + 1 : ℕ) : ℤ) + 2) +
        8 * (∑ i ∈ Finset.range (2 * m + 1),
          oddB (fun r => legendreSym p (r : ℤ)) (2 * m + 1) (i + 1) ^ 2) := by
  let a : ℕ → ℤ := fun r => legendreSym p (r : ℤ)
  let b : ℕ → ℤ := oddB a (2 * m + 1)
  let c : ℤ := partialSum a (2 * m + 1)
  let A : ℤ := ∑ i ∈ Finset.range (2 * m + 1), a (i + 1) * b (i + 1)
  let B : ℤ := ∑ i ∈ Finset.range (2 * m + 1), b (i + 1) ^ 2
  let T : ℤ := ∑ i ∈ Finset.range (2 * m + 1), a (i + 1) * partialSum a (2 * m + 1 - (i + 1))
  let V : ℤ := ∑ i ∈ Finset.range (2 * m + 1), a (i + 1) * partialSum a i
  have hp2 : p ≠ 2 := by omega
  have hn : (p - 1) / 2 = 2 * m + 1 := by omega
  have hε : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four (by omega)]
  have hdiag : (∑ i ∈ Finset.range (2 * m + 1), a (i + 1) ^ 2) = (2 * m + 1 : ℕ) :=
    sum_lower_sign_sq p (2 * m + 1) (by omega)
  have hV := twice_weighted_predecessor a (2 * m + 1)
  rw [hdiag] at hV
  change 2 * V = c ^ 2 - ((2 * m + 1 : ℕ) : ℤ) at hV
  have htri := twice_doubleSum_triangle p hp2
  rw [hε, hn] at htri
  change 2 * doubleSum p = -(c ^ 2 + ((2 * m + 1 : ℕ) : ℤ)) - 2 * (-1) * T at htri
  have hA : 2 * A = T - V := by
    calc
      _ = ∑ i ∈ Finset.range (2 * m + 1), a (i + 1) * (2 * b (i + 1)) := by
        dsimp only [A]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i ∈ Finset.range (2 * m + 1),
          (a (i + 1) * partialSum a (2 * m + 1 - (i + 1)) - a (i + 1) * partialSum a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hb := twice_oddB a m (i + 1) (by omega) (by omega)
          (fun r hr hn' => lower_sign_sq p hr (by omega))
        simp only [Nat.add_sub_cancel] at hb
        change 2 * b (i + 1) = _ at hb
        rw [hb]
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib, T, V]
  have hAd : 2 * A = doubleSum p + ((2 * m + 1 : ℕ) : ℤ) := by linarith
  have hnorm : (∑ i ∈ Finset.range (2 * m + 1), columnSum p 1 (i + 1) ^ 2) =
      ((2 * m + 1 : ℕ) : ℤ) - 8 * A + 16 * B := by
    calc
      _ = ∑ i ∈ Finset.range (2 * m + 1),
          (a (i + 1) ^ 2 - 8 * (a (i + 1) * b (i + 1)) + 16 * b (i + 1) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [odd_columnSum p m hpm (by omega) (by omega)]
        change (-a (i + 1) + 4 * b (i + 1)) ^ 2 = _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hdiag, A, B]
  have hE := column_energy p hp2 1 (Or.inl rfl)
  rw [hn, hε, hnorm] at hE
  change ((2 * m + 1 : ℕ) : ℤ) - 8 * A + 16 * B =
    (p : ℤ) * ((2 * m + 1 : ℕ) : ℤ) -
      (1 + 1 * -1) * (((2 * m + 1 : ℕ) : ℤ) ^ 2) - (1 + 1) * c ^ 2 at hE
  norm_num at hE
  have hpmz : (p : ℤ) = 4 * m + 3 := by exact_mod_cast hpm
  rw [hpmz] at hE
  push_cast at hE hAd
  change 2 * doubleSum p = c ^ 2 -
    ((2 * m + 1 : ℕ) : ℤ) * (((2 * m + 1 : ℕ) : ℤ) + 2) + 8 * B
  push_cast
  nlinarith [hE, hAd]

end D5.S3.Arith.CharacterSums.ChenSunDoubleCharacter
