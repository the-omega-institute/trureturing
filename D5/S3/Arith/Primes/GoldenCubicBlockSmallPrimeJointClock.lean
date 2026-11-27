/- GID: D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact dyadic and three-adic compatibility with odd native Lucas clocks. -/

import D5.S3.Arith.Primes.GoldenCubicBlockJointClock

import D5.S3.Arith.Primes.GoldenCubicBlockThreeAdic
import D5.S3.Arith.Primes.GoldenCubicDyadicClock

set_option autoImplicit false

/-! Mixed clocks on the same sequence of native cubic Lucas blocks. -/
namespace D5.S3.Arith.Primes.GoldenCubicBlockSmallPrimeJointClock
open D5.S1.Scale GoldenCubicBlockTailPeriodClosed GoldenCubicBlockJointClock
open GoldenCubicBlockThreeAdic GoldenCubicDyadicClock

theorem orderOf_nine_dvd_half (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    orderOf (9 : ZMod p) ∣ (p-1)/2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have ha : (3:ZMod p) ≠ 0 := by
    intro he
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
      ((ZMod.natCast_eq_zero_iff 3 p).mp he))
  obtain ⟨c,hc⟩ := hp.odd_of_ne_two hp2
  have hj : 2*((p-1)/2) = p-1 := by omega
  apply orderOf_dvd_of_pow_eq_one
  rw [show (9:ZMod p) = (3:ZMod p)^2 by ring, ← pow_mul, hj]
  exact ZMod.pow_card_sub_one_eq_one ha

theorem witness_period_odd_mod_four_three (p i a : ℕ) (hp : p.Prime)
    (hp3 : p ≠ 3) (hmod : p % 4 = 3) : Odd (cubicTailPeriod p i a) := by
  have hp2 : p ≠ 2 := by omega
  dsimp only [cubicTailPeriod]
  split_ifs
  · decide
  · apply Odd.mul _ ((hp.odd_of_ne_two hp2).pow)
    have hd := orderOf_nine_dvd_half p hp hp2 hp3
    have hodd : Odd ((p-1)/2) := ⟨p/4, by omega⟩
    exact Odd.of_dvd_nat hodd hd

theorem dyadic_pair_compat
    (a Q x y : ℕ) :
    (∃ n : ℕ, n ≡ x [MOD 2^(a-7)] ∧ n ≡ y [MOD Q]) ↔
      x ≡ y [MOD (2^(a-7)).gcd Q] := by
  constructor
  · rintro ⟨n, hx, hy⟩
    exact (hx.of_dvd (Nat.gcd_dvd_left _ _)).symm.trans (hy.of_dvd (Nat.gcd_dvd_right _ _))
  · intro h
    exact ⟨Nat.chineseRemainder' h, (Nat.chineseRemainder' h).prop⟩

theorem dyadic_odd_independent (a Q x y : ℕ) (hQ : Odd Q) :
    ∃ n : ℕ, n ≡ x [MOD 2^(a-7)] ∧ n ≡ y [MOD Q] := by
  apply (dyadic_pair_compat a Q x y).mpr
  have hc : Nat.Coprime 2 Q := by
    rw [Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 2)]
    exact hQ.not_two_dvd_nat
  have hg : (2^(a-7)).gcd Q = 1 := hc.pow_left (a-7)
  rw [hg]
  exact Nat.modEq_one

private theorem block_step (i : ℕ) (hi : 1 ≤ i) :
    clockBlock (i+1) = (clockBlock i-3)*(clockBlock i)^2+3 := by
  unfold clockBlock
  rw [(golden_cubic_lucas_block i hi).2.2.2.2.2]
  ring

theorem probe_prime_1277209 : Nat.Prime 1277209 := by norm_num

private theorem block_six_mod_square : clockBlock 6 ≡ 1403945171861 [ZMOD (1277209:ℤ)^2] := by
  let p := (1277209:ℤ)^2
  have hc (i : ℕ) (hi : 1 ≤ i) (c : ℤ) (hc : clockBlock i ≡ c [ZMOD p]) :
      clockBlock (i+1) ≡ (c-3)*c^2+3 [ZMOD p] := by
    rw [block_step i hi]
    exact ((hc.sub (Int.ModEq.refl 3)).mul (hc.pow 2)).add (Int.ModEq.refl 3)
  have c1 : clockBlock 1 ≡ 19 [ZMOD p] := by
    have h : clockBlock 1 = 19 := by
      open D5.S0.Carrier in norm_num [clockBlock, goldenLucas, trace, phi, pow_succ]
    rw [h]
  have c2 : clockBlock 2 ≡ 5779 [ZMOD p] :=
    (hc 1 (by decide) 19 c1).trans (by decide)
  have c3 : clockBlock 3 ≡ 192900153619 [ZMOD p] :=
    (hc 2 (by decide) 5779 c2).trans (by decide)
  have c4 : clockBlock 4 ≡ 355158276517 [ZMOD p] :=
    (hc 3 (by decide) 192900153619 c3).trans (by decide)
  have c5 : clockBlock 5 ≡ 1264551498565 [ZMOD p] :=
    (hc 4 (by decide) 355158276517 c4).trans (by decide)
  have c6 : clockBlock 6 ≡ 1403945171861 [ZMOD p] :=
    (hc 5 (by decide) 1264551498565 c5).trans (by decide)
  exact c6

theorem block_six_witness_1277209 : (1277209:ℤ) ∣ clockBlock 6 := by
  apply Int.modEq_zero_iff_dvd.mp
  exact (block_six_mod_square.of_dvd (by decide)).trans (by decide)

theorem block_six_depth_1277209 : padicValInt 1277209 (clockBlock 6) = 1 := by
  have hno : ¬ (1277209:ℤ)^2 ∣ clockBlock 6 := by
    intro hd
    have ht := (Int.modEq_zero_iff_dvd.mpr hd).symm.trans block_six_mod_square
    exact (by decide : ¬ (0 ≡ 1403945171861 [ZMOD (1277209:ℤ)^2])) ht
  have ht := padicValInt_dvd_iff_of_ne_one (by decide : (1277209:ℕ) ≠ 1)
  have hne : clockBlock 6 ≠ 0 := fun h => hno (h ▸ dvd_zero _)
  have h1 := (ht 1 (clockBlock 6)).mp (by
    simpa only [pow_one, Nat.cast_ofNat] using block_six_witness_1277209)
  have h2 : ¬ 2 ≤ padicValInt 1277209 (clockBlock 6) := by
    intro he
    apply hno
    exact (ht 2 (clockBlock 6)).mpr (Or.inr he)
  exact Nat.le_antisymm (by omega) (h1.resolve_left hne)


theorem probe_order_even_1277209 : Even (orderOf (9 : ZMod 1277209)) := by
  have q1 : (9:ZMod 1277209)^1 = 9 := pow_one _
  have q2 : (9:ZMod 1277209)^2 = 81 := by
    rw [show (2:ℕ) = 1*2 by decide, pow_mul, q1]
    decide
  have q4 : (9:ZMod 1277209)^4 = 6561 := by
    rw [show (4:ℕ) = 2*2 by decide, pow_mul, q2]
    decide
  have q9 : (9:ZMod 1277209)^9 = 426162 := by
    rw [show (9:ℕ) = 4*2 + 1 by decide, pow_succ, pow_mul, q4]
    decide
  have q19 : (9:ZMod 1277209)^19 = 353520 := by
    rw [show (19:ℕ) = 9*2 + 1 by decide, pow_succ, pow_mul, q9]
    decide
  have q38 : (9:ZMod 1277209)^38 = 212541 := by
    rw [show (38:ℕ) = 19*2 by decide, pow_mul, q19]
    decide
  have q77 : (9:ZMod 1277209)^77 = 644040 := by
    rw [show (77:ℕ) = 38*2 + 1 by decide, pow_succ, pow_mul, q38]
    decide
  have q155 : (9:ZMod 1277209)^155 = 1200377 := by
    rw [show (155:ℕ) = 77*2 + 1 by decide, pow_succ, pow_mul, q77]
    decide
  have q311 : (9:ZMod 1277209)^311 = 343243 := by
    rw [show (311:ℕ) = 155*2 + 1 by decide, pow_succ, pow_mul, q155]
    decide
  have q623 : (9:ZMod 1277209)^623 = 347223 := by
    rw [show (623:ℕ) = 311*2 + 1 by decide, pow_succ, pow_mul, q311]
    decide
  have q1247 : (9:ZMod 1277209)^1247 = 964267 := by
    rw [show (1247:ℕ) = 623*2 + 1 by decide, pow_succ, pow_mul, q623]
    decide
  have q2494 : (9:ZMod 1277209)^2494 = 140871 := by
    rw [show (2494:ℕ) = 1247*2 by decide, pow_mul, q1247]
    decide
  have q4989 : (9:ZMod 1277209)^4989 = 672836 := by
    rw [show (4989:ℕ) = 2494*2 + 1 by decide, pow_succ, pow_mul, q2494]
    decide
  have q9978 : (9:ZMod 1277209)^9978 = 275637 := by
    rw [show (9978:ℕ) = 4989*2 by decide, pow_mul, q4989]
    decide
  have q19956 : (9:ZMod 1277209)^19956 = 978404 := by
    rw [show (19956:ℕ) = 9978*2 by decide, pow_mul, q9978]
    decide
  have q39912 : (9:ZMod 1277209)^39912 = 1132880 := by
    rw [show (39912:ℕ) = 19956*2 by decide, pow_mul, q19956]
    decide
  have q79825 : (9:ZMod 1277209)^79825 = 64686 := by
    rw [show (79825:ℕ) = 39912*2 + 1 by decide, pow_succ, pow_mul, q39912]
    decide
  have q159651 : (9:ZMod 1277209)^159651 = 1277208 := by
    rw [show (159651:ℕ) = 79825*2 + 1 by decide, pow_succ, pow_mul, q79825]
    decide
  have hneg := q159651
  have hnon : (9 : ZMod 1277209)^159651 ≠ 1 := by rw [hneg]; decide
  have hpos : (9 : ZMod 1277209)^319302 = 1 := by
    rw [show (319302:ℕ) = 159651*2 by decide,pow_mul,hneg]
    decide
  have hd := orderOf_dvd_of_pow_eq_one hpos
  by_contra h
  have ho := Nat.not_even_iff_odd.mp h
  have hc : Nat.Coprime (orderOf (9 : ZMod 1277209)) 2 := by
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 2)]
    exact ho.not_two_dvd_nat
  rw [show (319302:ℕ)=159651*2 by decide] at hd
  exact hnon (orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right hd))

/-- In contrast to the mod-four-three case, this actual block divisor
has an even clock as soon as its nonconstant window starts. -/
theorem an_even_native_witness_clock (a : ℕ)
    (ha : 2*padicValInt 1277209 (clockBlock 6) < a) :
    Even (cubicTailPeriod 1277209 6 a) := by
  simp only [clockBlock] at ha
  have hm : ¬ a ≤ 2 * padicValInt 1277209 (goldenLucas (3^6)^2 + 3) :=
    Nat.not_le.mpr ha
  simp only [cubicTailPeriod, ite_eq_right hm]
  exact probe_order_even_1277209.mul_right _

/-- At dyadic precision eight, the phase comparison reduces to parity
for this native witness. In particular the two opposite time labels
are individually available but cannot occur together. -/
theorem dyadic_eight_witness_phase (a x y : ℕ)
    (ha : 2*padicValInt 1277209 (clockBlock 6) < a) :
    (∃ n : ℕ, n ≡ x [MOD 2^((8:ℕ)-7)] ∧
      n ≡ y [MOD cubicTailPeriod 1277209 6 a]) ↔ x ≡ y [MOD 2] := by
  rw [dyadic_pair_compat, show (2:ℕ)^((8:ℕ)-7)=2 by decide,
    Nat.gcd_eq_left ((even_iff_two_dvd.mp (an_even_native_witness_clock a ha)))]

/-- In the mixed clock, a genuine three-adic transient fixes the time
exactly. The eventual three-adic residue instead permits arbitrary late
representatives of every periodic phase. -/
theorem aligned_three_periodic_exists (a K P x y : ℕ) (hP : 0 < P) :
    (∃ n : ℕ, clockBlock (K+n) ≡ clockBlock (K+x) [ZMOD (3:ℤ)^a] ∧
      n ≡ y [MOD P]) ↔ (a ≤ K+x+1 ∨ x ≡ y [MOD P]) := by
  change (∃ n : ℕ, cubicBlock (K+n) ≡ cubicBlock (K+x) [ZMOD (3:ℤ)^a] ∧
    n ≡ y [MOD P]) ↔ _
  simp only [cubicBlock_three_clamped_phase]
  constructor
  · rintro ⟨n, hc, hn⟩
    by_cases hx : a ≤ K+x+1
    · exact Or.inl hx
    · have he : n = x := by omega
      exact Or.inr (he ▸ hn)
  · rintro (hx | hx)
    · let n := y+a*P
      have hn : n ≡ y [MOD P] := by
        have hm : Nat.ModEq P y n := (Nat.modEq_iff_dvd' (by dsimp [n]; omega)).mpr (by
          dsimp [n]
          rw [Nat.add_sub_cancel_left]
          exact dvd_mul_left _ _)
        exact hm.symm
      have hnlate : a ≤ n := by
        dsimp [n]
        exact le_trans (Nat.le_mul_of_pos_right a hP) (Nat.le_add_left _ _)
      refine ⟨n, ?_, hn⟩
      omega
    · exact ⟨x, rfl, hx⟩

theorem three_witness_pair_exists
    (a p i b K x y : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hpB : (p:ℤ) ∣ clockBlock i) (hK : i+1 ≤ K) :
    (∃ n : ℕ, clockBlock (K+n) ≡ clockBlock (K+x) [ZMOD (3:ℤ)^a] ∧
      clockBlock (K+n) ≡ clockBlock (K+y) [ZMOD (p:ℤ)^b]) ↔
      (a ≤ K+x+1 ∨ x ≡ y [MOD cubicTailPeriod p i b]) := by
  simp only [aligned_collision p i b K _ y hp hi hpB hK]
  have hP := (golden_cubic_tail_period_least p i b hp hi hpB).1.1
  exact aligned_three_periodic_exists a K _ x y hP

theorem aligned_dyadic_collision (a K x y : ℕ) (hK : 1 ≤ K) :
    clockBlock (K+x) ≡ clockBlock (K+y) [ZMOD (2:ℤ)^a] ↔
    x ≡ y [MOD 2^(a-7)] := by
  have aux (u v : ℕ) (huv : v < u) :
      clockBlock (K+u) ≡ clockBlock (K+v) [ZMOD (2:ℤ)^a] ↔
      u ≡ v [MOD 2^(a-7)] := by
    change dyadicBlock (K+u) ≡ dyadicBlock (K+v) [ZMOD (2:ℤ)^a] ↔ _
    rw [dyadicBlock_collision_iff a _ _ (by omega) (by omega), Nat.add_sub_add_left]
    exact ((Nat.modEq_iff_dvd' huv.le).symm).trans Nat.ModEq.comm
  rcases lt_trichotomy y x with hm | he | hn
  · exact aux x y hm
  · subst y; exact ⟨fun _ => Nat.ModEq.refl _, fun _ => Int.ModEq.refl _⟩
  · exact ⟨fun h => ((aux y x hn).mp h.symm).symm, fun h => ((aux y x hn).mpr h.symm).symm⟩

/-- The dyadic clock can be synchronized with a native odd witness
clock exactly when the time labels match modulo the gcd of periods. -/
theorem dyadic_witness_pair_exists (a p i b K x y : ℕ)
    (hp : p.Prime) (hi : 1 ≤ i) (hpB : (p:ℤ) ∣ clockBlock i) (hK : i+1 ≤ K) :
    (∃ n : ℕ, clockBlock (K+n) ≡ clockBlock (K+x) [ZMOD (2:ℤ)^a] ∧
      clockBlock (K+n) ≡ clockBlock (K+y) [ZMOD (p:ℤ)^b]) ↔
    x ≡ y [MOD (2^(a-7)).gcd (cubicTailPeriod p i b)] := by
  simpa only [aligned_dyadic_collision a K _ x (by omega), aligned_collision p i b K _ y hp hi hpB hK]
    using dyadic_pair_compat a (cubicTailPeriod p i b) x y

/-- For witnesses congruent to three modulo four the dyadic phase is
independent, so every pair of individually attainable readings occurs. -/
theorem dyadic_witness_independent (a p i b K x y : ℕ)
    (hp : p.Prime) (hp3 : p ≠ 3) (hmod : p%4=3) (hi : 1 ≤ i)
    (hpB : (p:ℤ) ∣ clockBlock i) (hK : i+1 ≤ K) :
    ∃ n : ℕ, clockBlock (K+n) ≡ clockBlock (K+x) [ZMOD (2:ℤ)^a] ∧
      clockBlock (K+n) ≡ clockBlock (K+y) [ZMOD (p:ℤ)^b] := by
  simpa only [aligned_dyadic_collision a K _ x (by omega), aligned_collision p i b K _ y hp hi hpB hK]
    using dyadic_odd_independent a (cubicTailPeriod p i b) x y
      (witness_period_odd_mod_four_three p i b hp hp3 hmod)

/-- A concrete incompatible pair: at 2^8 and 1277209^3 two accessible
readings from adjacent indices cannot be seen at a common index. -/
theorem native_dyadic_parity_obstruction (K : ℕ) (hK : 7 ≤ K) :
    ¬ ∃ n : ℕ, clockBlock (K+n) ≡ clockBlock K [ZMOD (2:ℤ)^8] ∧
      clockBlock (K+n) ≡ clockBlock (K+1) [ZMOD (1277209:ℤ)^3] := by
  intro h
  have hh : ∃ n : ℕ, n ≡ 0 [MOD 2^((8:ℕ)-7)] ∧ n ≡ 1 [MOD cubicTailPeriod 1277209 6 3] := by
    rcases h with ⟨n, hd, ho⟩
    refine ⟨n, (aligned_dyadic_collision 8 K n 0 (by omega)).mp ?_, ?_⟩
    · rw [Nat.add_zero]
      exact hd
    · exact (aligned_collision 1277209 6 3 K n 1 probe_prime_1277209 (by decide)
        block_six_witness_1277209 hK).mp ho
  have ha : 2 * padicValInt 1277209 (clockBlock 6) < 3 := by rw [block_six_depth_1277209]; decide
  exact (by decide : ¬ (0 ≡ 1 [MOD 2])) ((dyadic_eight_witness_phase 3 0 1 ha).mp hh)


end D5.S3.Arith.Primes.GoldenCubicBlockSmallPrimeJointClock
