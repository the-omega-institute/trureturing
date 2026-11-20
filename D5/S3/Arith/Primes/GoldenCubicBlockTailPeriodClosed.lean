/- GID: D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The least period of a later Lucas block stream at every precision separates Lucas depth from base-three Fermat depth. -/

import D5.S3.Arith.Primes.GoldenCubicBlockLagValuation
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicBlockTailPeriodClosed

open GoldenCubicBlockLagValuation

open D5.S1.Scale

private theorem pow_sub_one_pos {b k : ℕ} (hb : 1 < b) (hk : k ≠ 0) :
    0 < b^k - 1 := by
  exact Nat.sub_pos_of_lt (one_lt_pow₀ hb hk)

private theorem zmod_pow_one_iff {b k N : ℕ} (hb : 1 ≤ b) :
    (b : ZMod N)^k = 1 ↔ N ∣ b^k - 1 := by
  have hs : 1 ≤ b^k := Nat.one_le_pow k b hb
  rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod N), ZMod.natCast_eq_natCast_iff]
  exact ⟨fun h => (Nat.modEq_iff_dvd' hs).mp h.symm,
    fun h => ((Nat.modEq_iff_dvd' hs).mpr h).symm⟩

private theorem prime_not_dvd_nine {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ¬ p ∣ 9 := by
  rw [show 9 = 3^2 by decide]
  exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h))

private theorem prime_not_dvd_three {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)

private theorem prime_not_dvd_pow {p b k : ℕ} (hp : p.Prime) (h : ¬ p ∣ b) :
    ¬ p ∣ b^k := fun hd => h (hp.dvd_of_dvd_pow hd)

private theorem val_pow_lift {p b k : ℕ} [Fact p.Prime] (ho : Odd p) (hb : 1 < b)
    (hd : p ∣ b-1) (hn : ¬ p ∣ b) (hk : k ≠ 0) :
    padicValNat p (b^k - 1) = padicValNat p (b-1) + padicValNat p k := by
  simpa using padicValNat.pow_sub_pow ho hb hd hn hk

/-- At a positive precision square-base periods grow only after the
three-Fermat depth of the prime. -/
theorem orderOf_nine_prime_power (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hr : 1 ≤ r) :
    orderOf (9 : ZMod (p^r)) =
      orderOf (9 : ZMod p) * p^(r - padicValNat p (3^(p-1)-1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have ho := hp.odd_of_ne_two hp2
  let t := orderOf (9 : ZMod p)
  let e := padicValNat p (3^(p-1)-1)
  change orderOf (9 : ZMod (p^r)) = t * p^(r-e)
  have h9 := prime_not_dvd_nine hp hp3
  have h3 := prime_not_dvd_three hp hp3
  have h3z : (3 : ZMod p) ≠ 0 := by
    exact fun h => h3 ((ZMod.natCast_eq_zero_iff 3 p).mp h)
  have h9z : (9 : ZMod p) ≠ 0 := by
    exact fun h => h9 ((ZMod.natCast_eq_zero_iff 9 p).mp h)
  have hd : t ∣ p-1 := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h9z)
  have hpp : 0 < p-1 := by have := hp.two_le; omega
  have ht := Nat.pos_of_dvd_of_pos hd hpp
  have htD : p ∣ 9^t-1 :=
    (zmod_pow_one_iff (b := 9) (by decide)).mp (pow_orderOf_eq_one _)
  have h3D : p ∣ 3^(p-1)-1 :=
    (zmod_pow_one_iff (b := 3) (by decide)).mp (ZMod.pow_card_sub_one_eq_one h3z)
  have he : padicValNat p (9^t-1) = e := by
    obtain ⟨m, hm⟩ := hd
    have hm0 : m ≠ 0 := by
      intro h; simp [h] at hm; omega
    have hnm : ¬ p ∣ m := by
      intro hd'
      have hd'' : p ∣ p-1 := hm ▸ dvd_mul_of_dvd_right hd' t
      have := Nat.le_of_dvd hpp hd''
      omega
    have hl9 := val_pow_lift ho (show 1 < 9^t from one_lt_pow₀ (by decide) ht.ne')
      htD (prime_not_dvd_pow hp h9) hm0
    rw [padicValNat.eq_zero_of_not_dvd hnm, add_zero, ← pow_mul, ← hm] at hl9
    have hl3 := val_pow_lift ho (show 1 < 3^(p-1) from one_lt_pow₀ (by decide) hpp.ne')
      h3D (prime_not_dvd_pow hp h3) (show (2:ℕ) ≠ 0 by decide)
    have h2n : ¬ p ∣ 2 := fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
    rw [padicValNat.eq_zero_of_not_dvd h2n, add_zero, ← pow_mul, mul_comm,
      pow_mul, show (3:ℕ)^2=9 by decide] at hl3
    exact hl9.symm.trans hl3
  have hchar (k : ℕ) : (9 : ZMod (p^r))^k = 1 ↔ t * p^(r-e) ∣ k := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    change ((9 : ℕ) : ZMod (p^r))^k = 1 ↔ _
    rw [zmod_pow_one_iff (b := 9) (by decide)]
    constructor
    · intro h
      have hpr : p ∣ p^r := by
        simpa only [pow_one] using pow_dvd_pow p hr
      have htk : t ∣ k := orderOf_dvd_of_pow_eq_one
        ((zmod_pow_one_iff (b := 9) (by decide)).mpr (hpr.trans h))
      obtain ⟨m, rfl⟩ := htk
      have hm : m ≠ 0 := by intro hz; simp [hz] at hk
      have hl := val_pow_lift ho (show 1 < 9^t from one_lt_pow₀ (by decide) ht.ne')
        htD (prime_not_dvd_pow hp h9) hm
      have hle := (padicValNat_dvd_iff_le (pow_sub_one_pos (b := 9) (by decide) hk).ne').mp h
      rw [← pow_mul, he] at hl
      rw [hl] at hle
      apply Nat.mul_dvd_mul_left t
      exact (padicValNat_dvd_iff_le hm).mpr (by omega)
    · rintro ⟨m, rfl⟩
      have hm : p^(r-e)*m ≠ 0 := by intro hz; rw [mul_assoc, hz, mul_zero] at hk; exact hk rfl
      have hdm : p^(r-e) ∣ p^(r-e)*m := dvd_mul_right _ _
      have hle := (padicValNat_dvd_iff_le hm).mp hdm
      have hl := val_pow_lift ho (show 1 < 9^t from one_lt_pow₀ (by decide) ht.ne')
        htD (prime_not_dvd_pow hp h9) hm
      apply (padicValNat_dvd_iff_le (pow_sub_one_pos (b := 9) (by decide) hk).ne').mpr
      rw [mul_assoc, pow_mul, hl, he]
      omega
  exact Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one ((hchar _).mpr dvd_rfl))
    ((hchar _).mp (pow_orderOf_eq_one _))

private theorem block_prime_ne_two_three (p i : ℕ) (hi : 1 ≤ i)
    (hB : (p : ℤ) ∣ goldenLucas (3^i)^2 + 3) : p ≠ 2 ∧ p ≠ 3 := by
  let b := goldenLucas (3^i)^2+3
  have hb80 : (b : ZMod 80) = ((19:ℤ):ZMod 80) :=
    (golden_cubic_lucas_block i hi).2.2.2.2.1
  have hb9 : (b : ZMod 9) = ((1:ℤ):ZMod 9) :=
    (golden_cubic_lucas_block i hi).2.2.1
  have hr80 := (ZMod.intCast_eq_intCast_iff' b 19 80).mp hb80
  have hr9 := (ZMod.intCast_eq_intCast_iff' b 1 9).mp hb9
  have hn2 : p ≠ 2 := by
    rintro rfl
    have hw : b % 2 = 0 := Int.emod_eq_zero_of_dvd hB
    omega
  have hn3 : p ≠ 3 := by
    rintro rfl
    have hw : b % 3 = 0 := Int.emod_eq_zero_of_dvd hB
    omega
  exact ⟨hn2, hn3⟩

/-- The least positive period of the later native Lucas blocks at
absolute precision `a`. It is one in the constant window; once the
window is passed, order growth starts only after the base-three depth. -/
noncomputable def cubicTailPeriod (p i a : ℕ) : ℕ :=
  let w := 2 * padicValInt p (goldenLucas (3^i)^2 + 3)
  if a ≤ w then 1 else
    orderOf (9 : ZMod p) * p^(a - w - padicValNat p (3^(p-1)-1))

/-- At every absolute precision, a shift preserves the entire later
block stream exactly when it is a multiple of the displayed period. -/
theorem golden_cubic_tail_period_closed (p i a lag : ℕ) (hp : p.Prime)
    (hi : 1 ≤ i) (hB : (p : ℤ) ∣ goldenLucas (3^i)^2 + 3) :
    (∀ n : ℕ,
      goldenLucas (3^(i+1+(n+lag)))^2+3 ≡ goldenLucas (3^(i+1+n))^2+3 [ZMOD (p:ℤ)^a])
      ↔ cubicTailPeriod p i a ∣ lag := by
  let w := 2 * padicValInt p (goldenLucas (3^i)^2+3)
  unfold cubicTailPeriod
  change _ ↔ (if a ≤ w then 1 else _) ∣ _
  split_ifs with h
  · exact iff_of_true (fun n => golden_cubic_tail_constant p i a (n+lag) n hp hi hB h)
      (one_dvd _)
  · obtain ⟨hn2, hn3⟩ := block_prime_ne_two_three p i hi hB
    have hp' := golden_cubic_tail_period p i (a-w) lag hp hi hB
    change (∀ n, _ ≡ _ [ZMOD (p:ℤ)^(w+(a-w))]) ↔ _ at hp'
    rw [Nat.add_sub_of_le (by omega : w ≤ a),
      orderOf_nine_prime_power p (a-w) hp hn2 hn3 (by omega)] at hp'
    exact hp'

/-- The closed form is the minimum strictly positive period, not just a
period bound or a sufficient condition. -/
theorem golden_cubic_tail_period_least (p i a : ℕ) (hp : p.Prime)
    (hi : 1 ≤ i) (hB : (p : ℤ) ∣ goldenLucas (3^i)^2 + 3) :
    IsLeast {l : ℕ | 0 < l ∧ ∀ n : ℕ,
      goldenLucas (3^(i+1+(n+l)))^2+3 ≡ goldenLucas (3^(i+1+n))^2+3 [ZMOD (p:ℤ)^a]}
      (cubicTailPeriod p i a) := by
  have ht : 0 < orderOf (9 : ZMod p) := by
    have : Fact p.Prime := ⟨hp⟩
    have hn3 := (block_prime_ne_two_three p i hi hB).2
    have hnine : (9 : ZMod p) ≠ 0 := fun h =>
      prime_not_dvd_nine hp hn3 ((ZMod.natCast_eq_zero_iff 9 p).mp h)
    have hd := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hnine)
    exact Nat.pos_of_dvd_of_pos hd (by have := hp.two_le; omega)
  have hpos : 0 < cubicTailPeriod p i a := by
    dsimp only [cubicTailPeriod]
    split_ifs
    · decide
    · exact Nat.mul_pos ht (pow_pos hp.pos _)
  refine ⟨⟨hpos, (golden_cubic_tail_period_closed p i a _ hp hi hB).mpr dvd_rfl⟩, ?_⟩
  intro l hl
  exact Nat.le_of_dvd hl.1 ((golden_cubic_tail_period_closed p i a l hp hi hB).mp hl.2)

/-- If both depths are ordinary, the clock is flat up to precision two
and multiplies by the prime for each added digit after precision three. -/
theorem cubicTailPeriod_of_depths_one (p i a : ℕ)
    (hB : padicValInt p (goldenLucas (3^i)^2+3) = 1)
    (h3 : padicValNat p (3^(p-1)-1) = 1) :
    cubicTailPeriod p i a =
      if a ≤ 2 then 1 else orderOf (9 : ZMod p) * p^(a-3) := by
  dsimp only [cubicTailPeriod]
  rw [hB, h3]
  simp [Nat.sub_sub]

/-- The seed divisor 19 is a concrete instance of the closed formula
at all absolute precisions, with first visible period 9. -/
theorem golden_cubic_tail_period_nineteen (a : ℕ) :
    cubicTailPeriod 19 1 a = if a ≤ 2 then 1 else 9 * 19^(a-3) := by
  have hLucas : goldenLucas (3^1) = 4 := by
    open D5.S0.Carrier in norm_num [goldenLucas, trace, phi, pow_succ]
  have hdepth : padicValInt 19 (goldenLucas (3^1)^2+3) = 1 := by
    rw [hLucas, show (4:ℤ)^2+3 = (↑(19:ℕ):ℤ) by decide]
    exact padicValInt.self (by decide)
  have ht : orderOf (9 : ZMod 19) = 9 := by
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact orderOf_eq_prime_pow (p := 3) (n := 1) (by decide) (by decide)
  have he : padicValNat 19 (3^(19-1)-1) = 1 := by
    have : Fact (Nat.Prime 19) := ⟨by decide⟩
    have h0 : (3^(19-1)-1 : ℕ) ≠ 0 := by decide
    have hlo := (padicValNat_dvd_iff_le (p := 19) (n := 1) h0).mp (by decide)
    have hhi := (padicValNat_dvd_iff_le (p := 19) (n := 2) h0).not.mp (by decide)
    omega
  dsimp only [cubicTailPeriod]
  rw [hdepth, ht, he]
  simp [Nat.sub_sub]

/-- Nine has a nontrivial order at every seed prime. -/
theorem golden_cubic_nine_order_gt_one (p i : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hB : (p : ℤ) ∣ goldenLucas (3^i)^2+3) :
    1 < orderOf (9 : ZMod p) := by
  obtain ⟨hp2, hp3⟩ := block_prime_ne_two_three p i hi hB
  have : Fact p.Prime := ⟨hp⟩
  have h9 : (9 : ZMod p) ≠ 0 := fun h =>
    prime_not_dvd_nine hp hp3 ((ZMod.natCast_eq_zero_iff 9 p).mp h)
  have hP := hp.two_le
  have ht := Nat.pos_of_dvd_of_pos
    (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h9))
    (show 0 < p-1 by omega)
  have hn : orderOf (9 : ZMod p) ≠ 1 := by
    intro h
    have hpow : (9 : ZMod p)^1 = 1 := h ▸ pow_orderOf_eq_one _
    have hd : p ∣ (2:ℕ)^3 :=
      (zmod_pow_one_iff (b := 9) (by decide)).mp hpow
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hd))
  omega

/-- The period profile reveals the Lucas depth: precisely the initial
window through twice that depth has period one. -/
theorem cubicTailPeriod_eq_one_iff (p i a : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hB : (p : ℤ) ∣ goldenLucas (3^i)^2+3) :
    cubicTailPeriod p i a = 1 ↔ a ≤ 2 * padicValInt p (goldenLucas (3^i)^2+3) := by
  have ht := golden_cubic_nine_order_gt_one p i hp hi hB
  dsimp only [cubicTailPeriod]
  split_ifs with h
  · simp [h]
  · have hpow : 0 < p^(a - 2 * padicValInt p (goldenLucas (3^i)^2+3) -
        padicValNat p (3^(p-1)-1)) := pow_pos hp.pos _
    have hmul := Nat.le_mul_of_pos_right (orderOf (9 : ZMod p)) hpow
    simp [h, show orderOf (9 : ZMod p) * p^(a - 2 *
      padicValInt p (goldenLucas (3^i)^2+3) - padicValNat p (3^(p-1)-1)) ≠ 1 by omega]

/-- The first nontrivial plateau reveals the base-three depth as its
width, independently of the Lucas depth. -/
theorem cubicTailPeriod_eq_initial_order_iff (p i a : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hB : (p : ℤ) ∣ goldenLucas (3^i)^2+3) :
    cubicTailPeriod p i a = orderOf (9 : ZMod p) ↔
      2 * padicValInt p (goldenLucas (3^i)^2+3) < a ∧
      a ≤ 2 * padicValInt p (goldenLucas (3^i)^2+3) +
        padicValNat p (3^(p-1)-1) := by
  have ht := golden_cubic_nine_order_gt_one p i hp hi hB
  dsimp only [cubicTailPeriod]
  set t := orderOf (9 : ZMod p)
  set w := 2 * padicValInt p (goldenLucas (3^i)^2+3)
  set e := padicValNat p (3^(p-1)-1)
  split_ifs with h
  · simp [show 1 ≠ t by omega, show ¬ w < a by omega]
  · have hlt : w < a := by omega
    simp only [hlt, true_and]
    constructor
    · intro hm
      have hm' : t * p^(a-w-e) = t*1 := by simpa using hm
      have hpow := Nat.eq_of_mul_eq_mul_left (show 0 < t by omega) hm'
      by_contra hn
      have hne : a-w-e ≠ 0 := by omega
      have hm'' : 1 < p^(a-w-e) := one_lt_pow₀ hp.one_lt hne
      omega
    · intro hle
      have hz : a-w-e = 0 := by omega
      simp [hz]

/-- The two right endpoints encode the Lucas depth and the separate
base-three Fermat depth. The nontrivial plateau is always nonempty. -/
theorem cubicTailPeriod_profile_cutoffs (p i : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hB : (p : ℤ) ∣ goldenLucas (3^i)^2+3) :
    IsGreatest {a : ℕ | cubicTailPeriod p i a = 1}
      (2 * padicValInt p (goldenLucas (3^i)^2+3)) ∧
    IsGreatest {a : ℕ | cubicTailPeriod p i a = orderOf (9 : ZMod p)}
      (2 * padicValInt p (goldenLucas (3^i)^2+3) + padicValNat p (3^(p-1)-1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hn3 := (block_prime_ne_two_three p i hi hB).2
  have h3 : (3 : ZMod p) ≠ 0 := fun h =>
    prime_not_dvd_three hp hn3 ((ZMod.natCast_eq_zero_iff 3 p).mp h)
  have hd : p ∣ 3^(p-1)-1 :=
    (zmod_pow_one_iff (b := 3) (by decide)).mp (ZMod.pow_card_sub_one_eq_one h3)
  have hpp : p-1 ≠ 0 := by have := hp.two_le; omega
  have he := (padicValNat_dvd_iff_le (n := 1)
    (pow_sub_one_pos (b := 3) (by decide) hpp).ne').mp (by simpa using hd)
  refine ⟨⟨(cubicTailPeriod_eq_one_iff p i _ hp hi hB).mpr le_rfl, ?_⟩,
    ⟨(cubicTailPeriod_eq_initial_order_iff p i _ hp hi hB).mpr ⟨by omega, le_rfl⟩, ?_⟩⟩
  · intro a ha
    exact (cubicTailPeriod_eq_one_iff p i a hp hi hB).mp ha
  · intro a ha
    exact ((cubicTailPeriod_eq_initial_order_iff p i a hp hi hB).mp ha).2

end D5.S3.Arith.Primes.GoldenCubicBlockTailPeriodClosed
