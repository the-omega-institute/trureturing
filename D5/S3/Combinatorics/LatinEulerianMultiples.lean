/- GID: D5/S3/Combinatorics/LatinEulerianMultiples
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatinEulerianMultiples
   mirror-E: none(waiver:direct-Lean-proof-of-Mirzavaziri-Yaqubi-Remark-4-16-i)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Every interior multiple of the order is attained by a Latin-square column-ascent total. -/

import D5.S3.Combinatorics.LatinEulerianPermutations
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinEulerianMultiples

theorem result : claim := by
  intro n hn k hk hkn
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have hpos : 0 < n := by omega
  have squareLatin (p : Equiv.Perm (Fin n)) :
      IsLatin n (shiftedSquare n h2 p) := by
    letI : NeZero n := ⟨by omega⟩
    have htranslate (a : Fin n) :
        Function.Bijective (fun c : Fin n => a + c) := by
      apply Finite.injective_iff_bijective.mp
      intro c₁ c₂ h
      apply (ZMod.finEquiv n).injective
      apply add_left_cancel (a := (ZMod.finEquiv n) a)
      simpa only [map_add] using congrArg (ZMod.finEquiv n) h
    constructor
    · intro i
      change Function.Bijective (fun c => swapFin n h2 (p i + c))
      exact (swapFin n h2).bijective.comp (htranslate (p i))
    · intro c
      change Function.Bijective (fun i => swapFin n h2 (p i + c))
      have hbase : Function.Bijective (fun i : Fin n => c + p i) :=
        (htranslate c).comp p.bijective
      have hswap := (swapFin n h2).bijective.comp hbase
      simpa only [Function.comp_def, add_comm] using hswap
  have reverseLatin (M : Fin n → Fin n → Fin n) (hM : IsLatin n M) :
      IsLatin n (reverseRows n M) := by
    constructor
    · intro i
      exact hM.1 i.rev
    · intro c
      exact (hM.2 c).comp Fin.rev_bijective
  have constructLow (t : ℕ) (ht : 2 ≤ t) (htn : 2 * t ≤ n - 2) :
      ∃ L : Fin n → Fin n → Fin n,
        IsLatin n L ∧ totalAscents n L = t * n := by
    by_cases ht2 : t = 2
    · subst t
      let p := twoPermutation n hn
      refine ⟨shiftedSquare n h2 p, squareLatin p, ?_⟩
      obtain ⟨ha, hu, hv, hfirst, hlast⟩ := two_statistics n hn hpos
      have hf := shiftedSquare_formula h3 h2 hpos p
      rw [ha, hu, hv, hfirst, hlast] at hf
      have hcast : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by simp
      have hInt : (totalAscents n (shiftedSquare n h2 p) : ℤ) =
          ((2 * n : ℕ) : ℤ) := by
        rw [hf, hcast]
        omega
      exact_mod_cast hInt
    · have ht3 : 3 ≤ t := by omega
      have hbound : 2 * t + 2 ≤ n := by omega
      let p := lowPermutation n t ht3 hbound
      refine ⟨shiftedSquare n h2 p, squareLatin p, ?_⟩
      obtain ⟨ha, hu, hv, hfirst, hlast⟩ :=
        low_statistics n t ht3 hbound hpos
      have hf := shiftedSquare_formula h3 h2 hpos p
      rw [ha, hu, hv, hfirst, hlast] at hf
      have hcast : ((t * n : ℕ) : ℤ) = (n : ℤ) * (t : ℤ) := by
        simp [mul_comm]
      have hInt : (totalAscents n (shiftedSquare n h2 p) : ℤ) =
          ((t * n : ℕ) : ℤ) := by
        rw [hf, hcast]
        omega
      exact_mod_cast hInt
  by_cases hlow : 2 * k ≤ n - 2
  · exact constructLow k hk hlow
  by_cases hmid : Odd n ∧ 2 * k = n - 1
  · obtain ⟨hodd, hkmid⟩ := hmid
    rcases hodd with ⟨m, rfl⟩
    have hm : 2 ≤ m := by omega
    have hkeq : k = m := by omega
    subst k
    let p := midpointPermutation m hm
    refine ⟨shiftedSquare (2 * m + 1) h2 p, squareLatin p, ?_⟩
    obtain ⟨ha, hu, hv, hfirst, hlast⟩ := midpoint_statistics m hm hpos
    have hf := shiftedSquare_formula h3 h2 hpos p
    rw [show 2 * m + 1 - 1 = 2 * m by omega] at hf
    rw [ha, hu, hv, hfirst, hlast] at hf
    have hcast : ((m * (2 * m + 1) : ℕ) : ℤ) =
        ((2 * m + 1 : ℕ) : ℤ) * (m : ℤ) := by simp [mul_comm]
    have hInt : (totalAscents (2 * m + 1)
        (shiftedSquare (2 * m + 1) h2 p) : ℤ) =
        ((m * (2 * m + 1) : ℕ) : ℤ) := by
      rw [hf, hcast]
      omega
    exact_mod_cast hInt
  · let ell := n - 1 - k
    have hell2 : 2 ≤ ell := by dsimp [ell]; omega
    have hellow : 2 * ell ≤ n - 2 := by
      dsimp [ell]
      rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
      · omega
      · have hodd' : Odd n := Nat.odd_iff.mpr hodd
        have hneq : 2 * k ≠ n - 1 := by
          intro heq
          exact hmid ⟨hodd', heq⟩
        omega
    obtain ⟨L, hLatin, hTotal⟩ := constructLow ell hell2 hellow
    refine ⟨reverseRows n L, reverseLatin L hLatin, ?_⟩
    have hsum := total_reverse h2 L hLatin
    have hell : ell + k = n - 1 := by dsimp [ell]; omega
    have hprod : ell * n + k * n = n * (n - 1) := by
      rw [← add_mul, hell, Nat.mul_comm]
    omega

end D5.S3.Combinatorics.LatinEulerianMultiples
