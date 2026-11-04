/- GID: D5/S3/Arith/CharacterSums/ChenSunModSixteen
   generality: I
   mirror-B: D5/B/S3/Arith/CharacterSums/ChenSunModSixteen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full finite modulo-sixteen and modulo-thirty-two Chen-Sun energy congruences. -/

import D5.S3.Arith.CharacterSums.ChenSunDoubleCharacter
import D5.S3.Arith.CharacterSums.QuadraticPrefixParity

namespace D5.S3.Arith.CharacterSums.ChenSunDoubleCharacter

open scoped BigOperators
open D5.S3.Arith.CharacterSums.QuadraticPrefixEnergy D5.S3.Arith.CharacterSums.QuadraticSignProducts
open D5.S3.Arith.CharacterSums.QuadraticPrefixParity
open D5.S3.Arith.CharacterSums.QuadraticCharacterGram

variable (p : ℕ) [Fact p.Prime]

private theorem sign_sq {j : ℕ} (hj : 1 ≤ j) (hjp : j < p) :
    legendreSym p (j : ℤ) ^ 2 = 1 := by
  apply legendreSym.sq_one
  push_cast
  intro hz
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_cast_of_lt hjp, ZMod.val_zero] at hv
  omega

private theorem odd_interval_product (m : ℕ) (hpm : p = 4 * m + 3) :
    (∏ i ∈ Finset.range m,
      intervalProduct (fun j => legendreSym p (j : ℤ)) m i) = 1 := by
  rw [intervalProduct_character p m (by omega)]
  rcases Nat.even_or_odd m with he | ho
  · rw [Nat.even_iff.mp he, pow_zero]
  · have hm : m % 2 = 1 := Nat.odd_iff.mp ho
    rw [hm, pow_one, legendreSym.at_two (by omega),
      ZMod.χ₈_nat_mod_eight p, show p % 8 = 7 by omega]
    rfl

private theorem even_interval_product (m : ℕ) (hpm : p = 4 * m + 1) :
    (∏ i ∈ Finset.range m,
      intervalProduct (fun j => legendreSym p (j : ℤ)) m i) = (-1 : ℤ) ^ m := by
  rw [intervalProduct_character p m (by omega)]
  rcases Nat.even_or_odd m with he | ho
  · rw [Nat.even_iff.mp he, pow_zero, he.neg_one_pow]
  · have hm : m % 2 = 1 := Nat.odd_iff.mp ho
    rw [hm, pow_one, ho.neg_one_pow, legendreSym.at_two (by omega),
      ZMod.χ₈_nat_mod_eight p, show p % 8 = 5 by omega]
    rfl

/-- The factorial-product parity of the odd-case central quotient sum. -/
theorem odd_half_sum_parity (m : ℕ) (hpm : p = 4 * m + 3) :
    Int.ModEq 4
      (2 * (∑ i ∈ Finset.range m,
        oddB (fun j => legendreSym p (j : ℤ)) (2 * m + 1) (i + 1)))
      ((m : ℤ) * (m + 1)) := by
  have h := central_half_sum_mod_four (fun j => legendreSym p (j : ℤ)) m
    (fun j hj hn => sign_sq p hj (by omega))
  simpa only [odd_interval_product p m hpm, sub_add_cancel] using h

/-- The same factorial product also fixes the even-case correction parity. -/
theorem even_half_sum_parity (m : ℕ) (hpm : p = 4 * m + 1) :
    Int.ModEq 2 (∑ i ∈ Finset.range m,
      evenB (fun j => legendreSym p (j : ℤ)) (2 * m) i) 0 := by
  have hm0 : 0 < m := by
    have hp := (Fact.out : p.Prime).one_lt
    omega
  let a : ℕ → ℤ := fun j => legendreSym p (j : ℤ)
  have hs : ∀ j, 1 ≤ j → j ≤ 2 * m + 1 → a j ^ 2 = 1 :=
    fun j hj hn => sign_sq p hj (by omega)
  have hcentral := central_half_sum_mod_four a m hs
  have hpref := twice_prefix_sum_mod_four a m (fun j hj hn => hs j hj (by omega))
  have heq :
      (∑ i ∈ Finset.range m, evenB a (2 * m) i) +
        (∑ i ∈ Finset.range m, oddB a (2 * m + 1) (i + 1)) =
          -(∑ i ∈ Finset.range m, partialSum a i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact evenB_add_central a m i (by have := Finset.mem_range.mp hi; omega) hs
  change Int.ModEq 4 _ ((m : ℤ) * (m + 1) - 1 +
    ∏ i ∈ Finset.range m, intervalProduct (fun j => legendreSym p (j : ℤ)) m i) at hcentral
  rw [even_interval_product p m hpm] at hcentral
  have hpol : (m : ℤ) * (m + 1) + (m : ℤ) * (m - 1) = 2 * (m : ℤ) ^ 2 := by ring
  have haux : Int.ModEq 4 (2 * (m : ℤ) ^ 2 - 1 + (-1 : ℤ) ^ m) 0 := by
    rcases Nat.even_or_odd m with he | ho
    · rw [he.neg_one_pow]
      obtain ⟨r, hr⟩ := he
      have hm : m = 2 * r := by omega
      rw [hm]
      apply Int.modEq_iff_dvd.mpr
      refine ⟨-2 * (r : ℤ) ^ 2, ?_⟩
      push_cast
      ring
    · rw [ho.neg_one_pow]
      obtain ⟨r, hr⟩ := ho
      have hm : m = 2 * r + 1 := by omega
      rw [hm]
      apply Int.modEq_iff_dvd.mpr
      refine ⟨-2 * (r : ℤ) * (r + 1), ?_⟩
      push_cast
      ring
  have hcomb := hcentral.add hpref
  change (_ + _) % 4 = _ % 4 at hcomb
  have heq' :
      2 * (∑ i ∈ Finset.range m, oddB a (2 * m + 1) (i + 1)) +
        2 * (∑ i ∈ Finset.range m, partialSum a i) =
          -2 * (∑ i ∈ Finset.range m, evenB a (2 * m) i) := by linarith
  rw [heq'] at hcomb
  have harg : (m : ℤ) * (m + 1) - 1 + (-1 : ℤ) ^ m + (m : ℤ) * (m - 1) =
      2 * (m : ℤ) ^ 2 - 1 + (-1 : ℤ) ^ m := by ring
  rw [harg] at hcomb
  change (2 * (m : ℤ) ^ 2 - 1 + (-1 : ℤ) ^ m) % 4 = 0 % 4 at haux
  change (∑ i ∈ Finset.range m, evenB a (2 * m) i) % 2 = 0 % 2
  omega

/-- The class-number-free odd-prime-family congruence retains the factor two,
which is essential for subsequently cancelling the modulus from 32 to 16. -/
theorem odd_doubleSum_mod32 (m : ℕ) (hpm : p = 4 * m + 3) :
    Int.ModEq 32 (2 * doubleSum p)
      (partialSum (fun j => legendreSym p (j : ℤ)) (2 * m + 1) ^ 2 + 4 * (m : ℤ) ^ 2 - 3) := by
  let a : ℕ → ℤ := fun j => legendreSym p (j : ℤ)
  let b : ℕ → ℤ := fun i => oddB a (2 * m + 1) (i + 1)
  have he := odd_energy_exact p m hpm
  rw [oddB_square_sum a m (fun j hj hn => sign_sq p hj (by omega))] at he
  have hB := odd_half_sum_parity p m hpm
  have hB8 := hB.mul_left' (c := 8)
  have hs := square_sum_mod_two b m
  have hs16 := hs.mul_left' (c := 16)
  have hpoly : -( ((2 * m + 1 : ℕ) : ℤ) * (((2 * m + 1 : ℕ) : ℤ) + 2)) +
      8 * ((m : ℤ) * (m + 1)) = 4 * (m : ℤ) ^ 2 - 3 := by push_cast; ring
  have hB8' : Int.ModEq 32 (16 * ∑ i ∈ Finset.range m, b i)
      (8 * ((m : ℤ) * (m + 1))) := by
    convert hB8 using 1 <;> (try dsimp only [b, a]) <;> ring
  have hcorr : Int.ModEq 32 (16 * ∑ i ∈ Finset.range m, b i ^ 2)
      (8 * ((m : ℤ) * (m + 1))) := hs16.trans hB8'
  have h := hcorr.add_left
    (partialSum a (2 * m + 1) ^ 2 -
      ((2 * m + 1 : ℕ) : ℤ) * (((2 * m + 1 : ℕ) : ℤ) + 2))
  convert h using 1 <;> dsimp only [b, a] at * <;> nlinarith [he, hpoly]

/-- The even-prime-family congruence includes every p congruent to one modulo four. -/
theorem even_doubleSum_mod16 (m : ℕ) (hpm : p = 4 * m + 1) :
    Int.ModEq 16 (doubleSum p) (-2 * (m : ℤ) ^ 2) := by
  let a : ℕ → ℤ := fun j => legendreSym p (j : ℤ)
  let b : ℕ → ℤ := fun i => evenB a (2 * m) i
  have hp2 : p ≠ 2 := by omega
  have hn : (p - 1) / 2 = 2 * m := by omega
  have hε : legendreSym p (-1) = 1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_one_mod_four (by omega)]
  have hc : partialSum a (2 * m) = 0 := by
    have h := prime_half_character_cancellation p hp2
    rw [sum_primeHalf] at h
    have h' : (1 + legendreSym p (-1)) * partialSum a ((p - 1) / 2) = 0 := by
      simpa [a, partialSum, legendreSym] using h
    rw [hε, hn] at h'
    linarith
  have he := even_energy_exact p m hpm
  rw [evenB_square_sum a m hc] at he
  have hB := even_half_sum_parity p m hpm
  have hsq := square_sum_mod_two b m
  have hBsq : Int.ModEq 2 (∑ i ∈ Finset.range m, b i ^ 2) 0 := hsq.trans hB
  have h8 := hBsq.mul_left' (c := 8)
  have hSM : Int.ModEq 4 (partialSum a m ^ 2) ((m : ℤ) ^ 2) := by
    have h := prefix_mod_two a m (fun j hj hn' => sign_sq p hj (by omega))
    simpa only [Int.ModEq, Int.sq_emod_four] using h
  have h4 := hSM.mul_left' (c := 4)
  have h := ((h8.add h4).neg).add_left (2 * (m : ℤ) ^ 2)
  convert h using 1 <;> dsimp only [b, a] at * <;> nlinarith [he]

end D5.S3.Arith.CharacterSums.ChenSunDoubleCharacter
