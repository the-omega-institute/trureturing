/- GID: D5/S3/Factorization/Mordell/GoldenCubicBlockIsogenyNonimage
   generality: I
   mirror-B: D5/B/S3/Factorization/Mordell/GoldenCubicBlockIsogenyNonimage
   mirror-E: none(waiver:explicit-cubic-isogeny-image-obstruction)
   anchors: []
   utility: none
   digest: Actual Mordell points have no preimage in the explicit affine cubic relation. -/

import D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Mordell.GoldenCubicBlockIsogenyNonimage

open D5.S1.Scale
open D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists

/-- The rational affine relation specified by the displayed cubic formulas,
restricted to nonzero finite source abscissas. -/
def CubicIsogenyAffineImage (b X Y : ℚ) : Prop :=
  ∃ s t : ℚ, s ≠ 0 ∧ t ^ 2 = s ^ 3 - 27 * b ∧
    X = (s ^ 3 - 108 * b) / (9 * s ^ 2) ∧
    Y = t * (s ^ 3 + 216 * b) / (27 * s ^ 3)

private theorem cubic_x_valuation_obstruction
    (p : ℕ) [Fact p.Prime] (X b : ℚ) (e : ℤ) (k : ℕ)
    (hX : X ≠ 0) (hb : b ≠ 0)
    (he : e = 1 ∨ e = 2)
    (hXval : padicValRat p X = e + k)
    (hbval : padicValRat p b = 2 * e)
    (h9val : padicValRat p (9 : ℚ) = 0)
    (h108val : padicValRat p (108 : ℚ) = 0) :
    ¬ ∃ s : ℚ, s ≠ 0 ∧ s ^ 3 = 9 * X * s ^ 2 + 108 * b := by
  rintro ⟨s, hs, hpoly⟩
  have hs3 : s ^ 3 ≠ 0 := pow_ne_zero 3 hs
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hmid : 9 * X * s ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hX) hs2
  have hconst : 108 * b ≠ 0 := mul_ne_zero (by norm_num) hb
  let r : ℤ := padicValRat p s
  have hleftval : padicValRat p (s ^ 3) = 3 * r := by
    rw [padicValRat.pow]
    simp only [r, Nat.cast_ofNat]
  have hmidval : padicValRat p (9 * X * s ^ 2) = e + k + 2 * r := by
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hX) hs2,
      padicValRat.mul (by norm_num : (9 : ℚ) ≠ 0) hX,
      padicValRat.pow, h9val, hXval]
    ring
  have hconstval : padicValRat p (108 * b) = 2 * e := by
    rw [padicValRat.mul (by norm_num : (108 : ℚ) ≠ 0) hb,
      h108val, hbval]
    ring
  by_cases hlow : r ≤ 0 ∨ (e = 2 ∧ r = 1)
  · have hltmid : padicValRat p (s ^ 3) < padicValRat p (9 * X * s ^ 2) := by
      rw [hleftval, hmidval]
      rcases he with he | he <;> rcases hlow with hlow | hlow <;> omega
    have hltconst : padicValRat p (s ^ 3) < padicValRat p (108 * b) := by
      rw [hleftval, hconstval]
      rcases he with he | he <;> rcases hlow with hlow | hlow <;> omega
    have hsum : 9 * X * s ^ 2 + 108 * b ≠ 0 := by rw [← hpoly]; exact hs3
    have hlt := padicValRat.lt_add_of_lt hsum hltmid hltconst
    rw [← hpoly] at hlt
    exact (lt_irrefl _ hlt)
  · have hltleft : padicValRat p (108 * b) < padicValRat p (s ^ 3) := by
      rw [hconstval, hleftval]
      rcases he with he | he <;> omega
    have hltmid : padicValRat p (108 * b) < padicValRat p (-(9 * X * s ^ 2)) := by
      rw [padicValRat.neg, hconstval, hmidval]
      rcases he with he | he <;> omega
    have hpoly' : 108 * b = s ^ 3 + -(9 * X * s ^ 2) := by linear_combination -hpoly
    have hsum : s ^ 3 + -(9 * X * s ^ 2) ≠ 0 := by rw [← hpoly']; exact hconst
    have hlt := padicValRat.lt_add_of_lt hsum hltleft hltmid
    rw [← hpoly'] at hlt
    exact (lt_irrefl _ hlt)

/-- On every actual cubic block, neither canonical point satisfies the
explicit rational affine cubic-image relation. -/
theorem actual_block_cubic_isogeny_nonimage (j : ℕ) (hj : 1 ≤ j) :
    ¬ CubicIsogenyAffineImage
        (-3 * (cubefreePart j : ℚ) ^ 2)
        ((cubefreePart j : ℚ) * cubePartRoot j)
        ((cubefreePart j : ℚ) * goldenLucas (3 ^ j)) ∧
    ¬ CubicIsogenyAffineImage
        (125 * (cubefreePart j : ℚ) ^ 2)
        (5 * (cubefreePart j : ℚ) * cubePartRoot j)
        (25 * (cubefreePart j : ℚ) * Nat.fib (3 ^ j)) := by
  have no_cubic_isogeny_affine_image
      (p : ℕ) [Fact p.Prime] (X b Y : ℚ) (e : ℤ) (k : ℕ)
      (hX : X ≠ 0) (hb : b ≠ 0)
      (he : e = 1 ∨ e = 2)
      (hXval : padicValRat p X = e + k)
      (hbval : padicValRat p b = 2 * e)
      (h9val : padicValRat p (9 : ℚ) = 0)
      (h108val : padicValRat p (108 : ℚ) = 0) :
      ¬ CubicIsogenyAffineImage b X Y := by
    rintro ⟨s, t, hs, _ht, hXcoord, _hYcoord⟩
    apply cubic_x_valuation_obstruction p X b e k hX hb he hXval hbval h9val h108val
    refine ⟨s, hs, ?_⟩
    have hden : (9 : ℚ) * s ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)
    have heq := (eq_div_iff hden).mp hXcoord
    linear_combination -heq
  have no_images_of_cubefree_factor
      (p : ℕ) [Fact p.Prime] (hpgt : 5 < p) (d c : ℕ)
      (hd : d ≠ 0) (hc : c ≠ 0)
      (he : d.factorization p = 1 ∨ d.factorization p = 2)
      (Yminus Yplus : ℚ) :
      ¬ CubicIsogenyAffineImage (-3 * (d : ℚ) ^ 2) ((d : ℚ) * c) Yminus ∧
      ¬ CubicIsogenyAffineImage (125 * (d : ℚ) ^ 2) (5 * (d : ℚ) * c) Yplus := by
    have hp : p.Prime := Fact.out
    have hnotdvd (n : ℕ) (hn : 0 < n) (hsmall : n < p) : ¬ p ∣ n := by
      intro h
      have hle := Nat.le_of_dvd hn h
      omega
    have hp2 : ¬ p ∣ 2 := hnotdvd 2 (by decide) (by omega)
    have hp3 : ¬ p ∣ 3 := hnotdvd 3 (by decide) (by omega)
    have hp5 : ¬ p ∣ 5 := hnotdvd 5 (by decide) (by omega)
    have hp9 : ¬ p ∣ 9 := by
      intro h
      have hpow : p ∣ 3 ^ (2 : ℕ) := by simpa using h
      exact hp3 (hp.dvd_of_dvd_pow hpow)
    have hp108 : ¬ p ∣ 108 := by
      intro h
      have hpow : p ∣ 2 ^ (2 : ℕ) * 3 ^ (3 : ℕ) := by simpa using h
      rcases hp.dvd_mul.mp hpow with h2 | h3
      · exact hp2 (hp.dvd_of_dvd_pow h2)
      · exact hp3 (hp.dvd_of_dvd_pow h3)
    have hp125 : ¬ p ∣ 125 := by
      intro h
      have hpow : p ∣ 5 ^ (3 : ℕ) := by simpa using h
      exact hp5 (hp.dvd_of_dvd_pow hpow)
    have val_nat (n : ℕ) (hn : ¬ p ∣ n) : padicValRat p (n : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd hn
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
    let e : ℤ := d.factorization p
    let k : ℕ := c.factorization p
    have he12 : e = 1 ∨ e = 2 := by
      rcases he with h | h <;> simp [e, h]
    have hdval : padicValRat p (d : ℚ) = e := by
      rw [padicValRat.of_nat, ← Nat.factorization_def d hp]
    have hcval : padicValRat p (c : ℚ) = k := by
      rw [padicValRat.of_nat, ← Nat.factorization_def c hp]
    have h3val : padicValRat p (3 : ℚ) = 0 := by simpa using val_nat 3 hp3
    have h5val : padicValRat p (5 : ℚ) = 0 := by simpa using val_nat 5 hp5
    have h125val : padicValRat p (125 : ℚ) = 0 := by simpa using val_nat 125 hp125
    have h9val : padicValRat p (9 : ℚ) = 0 := val_nat 9 hp9
    have h108val : padicValRat p (108 : ℚ) = 0 := val_nat 108 hp108
    constructor
    · apply no_cubic_isogeny_affine_image p _ _ _ e k
      · exact mul_ne_zero hdQ hcQ
      · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hdQ)
      · exact he12
      · rw [padicValRat.mul hdQ hcQ, hdval, hcval]
      · rw [padicValRat.mul (by norm_num : (-3 : ℚ) ≠ 0) (pow_ne_zero 2 hdQ),
          padicValRat.neg, h3val, padicValRat.pow, hdval]
        ring
      · exact h9val
      · exact h108val
    · apply no_cubic_isogeny_affine_image p _ _ _ e k
      · exact mul_ne_zero (mul_ne_zero (by norm_num) hdQ) hcQ
      · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hdQ)
      · exact he12
      · rw [padicValRat.mul (mul_ne_zero (by norm_num) hdQ) hcQ,
          padicValRat.mul (by norm_num : (5 : ℚ) ≠ 0) hdQ,
          h5val, hdval, hcval]
        ring
      · rw [padicValRat.mul (by norm_num : (125 : ℚ) ≠ 0) (pow_ne_zero 2 hdQ),
          h125val, padicValRat.pow, hdval]
        ring
      · exact h9val
      · exact h108val
  have block_prime_gt_five (j p : ℕ) (hj : 1 ≤ j)
      (hp : p.Prime) (hpB : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3) :
      5 < p := by
    let x : ℤ := goldenLucas (3 ^ j)
    have hx72 : (x : ZMod 72) = 4 :=
      (golden_cubic_lucas_block j hj).1
    have hx2 : (x : ZMod 2) = 0 := by
      have h := congrArg (ZMod.castHom (by decide : 2 ∣ 72) (ZMod 2)) hx72
      simpa only [map_intCast, map_ofNat, show (4 : ZMod 2) = 0 by decide] using h
    have hx3 : (x : ZMod 3) = 1 := by
      have h := congrArg (ZMod.castHom (by decide : 3 ∣ 72) (ZMod 3)) hx72
      simpa only [map_intCast, map_ofNat, show (4 : ZMod 3) = 1 by decide] using h
    have hx5 : (x : ZMod 5) ^ 2 = 1 := by
      simpa only [x, Int.cast_pow] using (golden_cubic_lucas_block j hj).2.2.2.1
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      have hB0 : ((x ^ 2 + 3 : ℤ) : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpB
      push_cast at hB0
      rw [hx2] at hB0
      exact (by decide : (3 : ZMod 2) ≠ 0) hB0
    have hp3 : p ≠ 3 := by
      intro heq
      subst p
      have hB0 : ((x ^ 2 + 3 : ℤ) : ZMod 3) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpB
      push_cast at hB0
      rw [hx3] at hB0
      exact (by decide : (4 : ZMod 3) ≠ 0) hB0
    have hp5 : p ≠ 5 := by
      intro heq
      subst p
      have hB0 : ((x ^ 2 + 3 : ℤ) : ZMod 5) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpB
      push_cast at hB0
      have hFour : (4 : ZMod 5) = 0 := by
        calc
          (4 : ZMod 5) = (x : ZMod 5) ^ 2 + 3 := by rw [hx5]; norm_num
          _ = 0 := hB0
      exact (by decide : (4 : ZMod 5) ≠ 0) hFour
    have hp4 : p ≠ 4 := by
      intro heq
      subst p
      norm_num at hp
    have hpge2 := hp.two_le
    omega
  have actual_block_prime_witness (j : ℕ) (hj : 1 ≤ j) :
      ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p ∣ block j ∧
        ((cubefreePart j).factorization p = 1 ∨
          (cubefreePart j).factorization p = 2) := by
    let B : ℕ := block j
    let c : ℕ := cubePartRoot j
    let d : ℕ := cubefreePart j
    have hBcast : (B : ℤ) = goldenLucas (3 ^ j) ^ 2 + 3 := by
      dsimp [B, block]
      exact Int.natCast_toNat_eq_self.mpr
        (by nlinarith [sq_nonneg (goldenLucas (3 ^ j))])
    have hfactor : B = d * c ^ 3 := by
      exact (Nat.div_mul_cancel (show c ^ 3 ∣ B from Nat.floorRoot_pow_dvd)).symm
    have hB0 : B ≠ 0 := by
      intro hz
      have hzero : (0 : ℤ) = goldenLucas (3 ^ j) ^ 2 + 3 := by
        simpa [hz] using hBcast
      nlinarith [sq_nonneg (goldenLucas (3 ^ j))]
    have hd0 : d ≠ 0 := by
      intro hz
      rw [hz] at hfactor
      exact hB0 (by simpa using hfactor)
    have hNotCube : ¬ ∃ t : ℕ, t ^ 3 = B := by
      intro ⟨t, ht⟩
      apply D5.S3.Factorization.GoldenCubicBlockNoncube.golden_cubic_block_not_cube j hj
      refine ⟨(t : ℤ), ?_⟩
      rw [← hBcast]
      exact_mod_cast ht
    have hdNotOne : d ≠ 1 := by
      intro hd1
      apply hNotCube
      refine ⟨c, ?_⟩
      rw [hfactor, hd1]
      simp
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hdNotOne
    have hpB : p ∣ B := by
      rw [hfactor]
      exact dvd_mul_of_dvd_left hpd _
    have hpBint : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3 := by
      rw [← hBcast]
      exact_mod_cast hpB
    have hpgt : 5 < p := block_prime_gt_five j p hj hp hpBint
    have hfac : d.factorization p = B.factorization p % 3 := by
      have hcdvd : c ^ 3 ∣ B := Nat.floorRoot_pow_dvd
      have hdiv := congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_div hcdvd)
      have hcpow : (c ^ 3).factorization p =
          3 * (B.factorization p / 3) := by
        simp [Nat.factorization_pow, c, cubePartRoot, B, Nat.factorization_floorRoot]
      change d.factorization p = B.factorization p - (c ^ 3).factorization p at hdiv
      rw [hcpow] at hdiv
      omega
    have hviPos : 0 < d.factorization p :=
      hp.factorization_pos_of_dvd hd0 hpd
    have hviLt : d.factorization p < 3 := by
      rw [hfac]
      exact Nat.mod_lt _ (by decide)
    refine ⟨p, hp, hpgt, ?_, ?_⟩
    · exact hpB
    · change d.factorization p = 1 ∨ d.factorization p = 2
      omega
  let Yminus : ℚ := (cubefreePart j : ℚ) * goldenLucas (3 ^ j)
  let Yplus : ℚ := 25 * (cubefreePart j : ℚ) * Nat.fib (3 ^ j)
  change ¬ CubicIsogenyAffineImage
      (-3 * (cubefreePart j : ℚ) ^ 2)
      ((cubefreePart j : ℚ) * cubePartRoot j) Yminus ∧
    ¬ CubicIsogenyAffineImage
      (125 * (cubefreePart j : ℚ) ^ 2)
      (5 * (cubefreePart j : ℚ) * cubePartRoot j) Yplus
  obtain ⟨p, hp, hpgt, _hpB, he⟩ := actual_block_prime_witness j hj
  let B : ℕ := block j
  let c : ℕ := cubePartRoot j
  let d : ℕ := cubefreePart j
  have hBcast : (B : ℤ) = goldenLucas (3 ^ j) ^ 2 + 3 := by
    dsimp [B, block]
    exact Int.natCast_toNat_eq_self.mpr
      (by nlinarith [sq_nonneg (goldenLucas (3 ^ j))])
  have hB0 : B ≠ 0 := by
    intro hz
    have hzero : (0 : ℤ) = goldenLucas (3 ^ j) ^ 2 + 3 := by
      simpa [hz] using hBcast
    nlinarith [sq_nonneg (goldenLucas (3 ^ j))]
  have hc0 : c ≠ 0 :=
    (Nat.floorRoot_ne_zero).mpr ⟨by decide, hB0⟩
  have hfactor : B = d * c ^ 3 := by
    exact (Nat.div_mul_cancel (show c ^ 3 ∣ B from Nat.floorRoot_pow_dvd)).symm
  have hd0 : d ≠ 0 := by
    intro hz
    rw [hz] at hfactor
    exact hB0 (by simpa using hfactor)
  letI : Fact p.Prime := ⟨hp⟩
  exact no_images_of_cubefree_factor p hpgt d c hd0 hc0 he Yminus Yplus

#print axioms actual_block_cubic_isogeny_nonimage

end D5.S3.Factorization.Mordell.GoldenCubicBlockIsogenyNonimage
