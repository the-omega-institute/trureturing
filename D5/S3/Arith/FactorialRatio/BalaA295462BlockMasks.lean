/- GID: D5/S3/Arith/FactorialRatio/BalaA295462BlockMasks
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/BalaA295462BlockMasks
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Odd A295462 values: masks below 16 commute with XOR/AND/OR; eleven XOR identities. -/

import D5.S3.Arith.FactorialRatio.BalaA295462Parity

/-! # Disjoint mask blocks for odd A295462 values

If `a(n)` of OEIS A295462 is odd, the binary positions of `n` are four-separated, so for every
`u < 16` the product `u n` is the sum of disjoint copies of `u` shifted to the positions of
`n`. Hence `(u n) ⊕ (v n) = (u ⊕ v) n` for all `u, v < 16`, and likewise for AND and OR.
The two larger triples `(12,21,25)` and `(12,37,41)` follow from a separate induction on `n`
in which the single carry out of each block of `21 n` or `37 n` stays inside its gap.
-/

namespace D5.S3.Arith.FactorialRatio.BalaA295462BlockMasks

open D5.S3.Arith.FactorialRatio.BalaA295462Parity

private lemma block (e a b A B : ℕ) (hA : A < 2 ^ e) (hB : B < 2 ^ e) :
    ((2 ^ e * a + A) ^^^ (2 ^ e * b + B) = 2 ^ e * (a ^^^ b) + (A ^^^ B)) ∧
    ((2 ^ e * a + A) &&& (2 ^ e * b + B) = 2 ^ e * (a &&& b) + (A &&& B)) ∧
    ((2 ^ e * a + A) ||| (2 ^ e * b + B) = 2 ^ e * (a ||| b) + (A ||| B)) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j
  · rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hA, Nat.testBit_two_pow_mul_add _ hB,
      Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hA hB), Nat.testBit_xor,
      Nat.testBit_xor]
    split_ifs <;> rfl
  · rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hA, Nat.testBit_two_pow_mul_add _ hB,
      Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hB), Nat.testBit_and,
      Nat.testBit_and]
    split_ifs <;> rfl
  · rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hA, Nat.testBit_two_pow_mul_add _ hB,
      Nat.testBit_two_pow_mul_add _ (Nat.or_lt_two_pow hA hB), Nat.testBit_or,
      Nat.testBit_or]
    split_ifs <;> rfl

private lemma spaced_masks :
    ∀ n, spacedBits n → ∀ u v : ℕ, u < 16 → v < 16 →
      (u * n) ^^^ (v * n) = (u ^^^ v) * n ∧ (u * n) &&& (v * n) = (u &&& v) * n ∧
        (u * n) ||| (v * n) = (u ||| v) * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hs u v hu hv
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · obtain ⟨e, h1, h2⟩ : ∃ e, 2 ^ e ≤ n ∧ n < 2 * 2 ^ e := by
        refine ⟨Nat.log 2 n, Nat.pow_log_le_self 2 hpos.ne', ?_⟩
        have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
        rwa [pow_succ, mul_comm] at this
      have hmod : n % 2 ^ e = n - 2 ^ e := by
        rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
      have hbit : n.testBit e = true := by
        rw [show n = 2 ^ e + (n - 2 ^ e) by omega, Nat.testBit_two_pow_add_eq,
          Nat.testBit_lt_two_pow (by omega)]
        rfl
      have hys := sparse_mod n e hs
      have ht := tail_bound n e hs hbit
      rw [hmod] at hys ht
      generalize hY : n - 2 ^ e = y at hys ht
      obtain rfl : n = 2 ^ e + y := by omega
      have huy : u * y < 2 ^ e := lt_of_le_of_lt (Nat.mul_le_mul_right y (by omega)) ht
      have hvy : v * y < 2 ^ e := lt_of_le_of_lt (Nat.mul_le_mul_right y (by omega)) ht
      obtain ⟨hx, ha, ho⟩ := ih y (by omega) hys u v hu hv
      have eu : u * (2 ^ e + y) = 2 ^ e * u + u * y := by ring
      have ev : v * (2 ^ e + y) = 2 ^ e * v + v * y := by ring
      obtain ⟨bx, ba, bo⟩ := block e u v (u * y) (v * y) huy hvy
      refine ⟨?_, ?_, ?_⟩
      · rw [eu, ev, bx, hx]; ring
      · rw [eu, ev, ba, ha]; ring
      · rw [eu, ev, bo, ho]; ring

private lemma spaced_double (n : ℕ) (hs : spacedBits (2 * n)) : spacedBits n := by
  intro i j hij hi hj
  have h1 : (2 * n).testBit (i + 1) = true := by
    rw [show 2 * n = n * 2 ^ 1 by ring, Nat.testBit_mul_two_pow]; simpa using hi
  have h2 : (2 * n).testBit (j + 1) = true := by
    rw [show 2 * n = n * 2 ^ 1 by ring, Nat.testBit_mul_two_pow]; simpa using hj
  have := hs (i + 1) (j + 1) (by omega) h1 h2
  omega

private lemma spaced_odd (n : ℕ) (hs : spacedBits n) (hodd : n % 2 = 1) :
    n = 16 * (n / 16) + 1 ∧ spacedBits (n / 16) := by
  have h0 : n.testBit 0 = true := by
    rw [Nat.testBit_zero]; simp [hodd]
  have hmod : n % 16 = 1 := by
    have : n % 2 ^ 4 = 1 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow]
      rcases Nat.lt_or_ge i 4 with hi | hi
      · rcases (by omega : i = 0 ∨ 1 ≤ i) with rfl | hi1
        · simp [h0]
        · have : n.testBit i = false := by
            by_contra hb
            have := hs 0 i (by omega) h0 (by simpa using hb)
            omega
          simp [this, Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (show i ≠ 0 by omega))]
      · simp [show ¬ i < 4 by omega,
          Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (show i ≠ 0 by omega))]
    simpa using this
  refine ⟨by omega, ?_⟩
  intro i j hij hi hj
  have h1 : n.testBit (i + 4) = true := by
    rw [← Nat.testBit_div_two_pow]
    simpa using hi
  have h2 : n.testBit (j + 4) = true := by
    rw [← Nat.testBit_div_two_pow]
    simpa using hj
  have := hs (i + 4) (j + 4) (by omega) h1 h2
  omega

private lemma xor16 (a b A B : ℕ) (hA : A < 16) (hB : B < 16) :
    (16 * a + A) ^^^ (16 * b + B) = 16 * (a ^^^ b) + (A ^^^ B) :=
  (block 4 a b A B (by norm_num; omega) (by norm_num; omega)).1

private lemma xor2 (a b A B : ℕ) (hA : A < 2) (hB : B < 2) :
    (2 * a + A) ^^^ (2 * b + B) = 2 * (a ^^^ b) + (A ^^^ B) :=
  (block 1 a b A B (by norm_num; omega) (by norm_num; omega)).1

private lemma carry_masks : ∀ n, spacedBits n →
    (12 * n) ^^^ (21 * n) = 25 * n ∧ (12 * n) ^^^ (21 * n + 1) = 25 * n + 1 ∧
    (12 * n) ^^^ (37 * n) = 41 * n ∧ (12 * n) ^^^ (37 * n + 2) = 41 * n + 2 ∧
    (12 * n) ^^^ (37 * n + 1) = 41 * n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hs
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; decide
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      obtain ⟨P, Q, P', Q', R'⟩ := ih k (by omega) (spaced_double k hs)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := xor2 (12 * k) (21 * k) 0 0 (by norm_num) (by norm_num)
        rw [show 12 * (2 * k) = 2 * (12 * k) + 0 by ring,
          show 21 * (2 * k) = 2 * (21 * k) + 0 by ring, this, P]; norm_num; ring
      · have := xor2 (12 * k) (21 * k) 0 1 (by norm_num) (by norm_num)
        rw [show 12 * (2 * k) = 2 * (12 * k) + 0 by ring,
          show 21 * (2 * k) + 1 = 2 * (21 * k) + 1 by ring, this, P]; norm_num; ring
      · have := xor2 (12 * k) (37 * k) 0 0 (by norm_num) (by norm_num)
        rw [show 12 * (2 * k) = 2 * (12 * k) + 0 by ring,
          show 37 * (2 * k) = 2 * (37 * k) + 0 by ring, this, P']; norm_num; ring
      · have := xor2 (12 * k) (37 * k + 1) 0 0 (by norm_num) (by norm_num)
        rw [show 12 * (2 * k) = 2 * (12 * k) + 0 by ring,
          show 37 * (2 * k) + 2 = 2 * (37 * k + 1) + 0 by ring, this, R']; norm_num; ring
      · have := xor2 (12 * k) (37 * k) 0 1 (by norm_num) (by norm_num)
        rw [show 12 * (2 * k) = 2 * (12 * k) + 0 by ring,
          show 37 * (2 * k) + 1 = 2 * (37 * k) + 1 by ring, this, P']; norm_num; ring
    · obtain ⟨hn, hms⟩ := spaced_odd n hs ho
      set m := n / 16
      have hm : m < n := by omega
      obtain ⟨_, Q, _, Q', _⟩ := ih m hm hms
      rw [hn]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := xor16 (12 * m) (21 * m + 1) 12 5 (by norm_num) (by norm_num)
        rw [show 12 * (16 * m + 1) = 16 * (12 * m) + 12 by ring,
          show 21 * (16 * m + 1) = 16 * (21 * m + 1) + 5 by ring, this, Q]
        norm_num; ring
      · have := xor16 (12 * m) (21 * m + 1) 12 6 (by norm_num) (by norm_num)
        rw [show 12 * (16 * m + 1) = 16 * (12 * m) + 12 by ring,
          show 21 * (16 * m + 1) + 1 = 16 * (21 * m + 1) + 6 by ring, this, Q]
        norm_num; ring
      · have := xor16 (12 * m) (37 * m + 2) 12 5 (by norm_num) (by norm_num)
        rw [show 12 * (16 * m + 1) = 16 * (12 * m) + 12 by ring,
          show 37 * (16 * m + 1) = 16 * (37 * m + 2) + 5 by ring, this, Q']
        norm_num; ring
      · have := xor16 (12 * m) (37 * m + 2) 12 7 (by norm_num) (by norm_num)
        rw [show 12 * (16 * m + 1) = 16 * (12 * m) + 12 by ring,
          show 37 * (16 * m + 1) + 2 = 16 * (37 * m + 2) + 7 by ring, this, Q']
        norm_num; ring
      · have := xor16 (12 * m) (37 * m + 2) 12 6 (by norm_num) (by norm_num)
        rw [show 12 * (16 * m + 1) = 16 * (12 * m) + 12 by ring,
          show 37 * (16 * m + 1) + 1 = 16 * (37 * m + 2) + 6 by ring, this, Q']
        norm_num; ring

/-- If `a(n)` is an odd natural number, then for all `u, v < 16`, `(u n) ⊕ (v n) = (u ⊕ v) n`,
and the same holds with AND and OR in place of XOR. In particular `(u n) ⊕ (v n) = w n` for the
eleven triples `(1,14,15), (3,9,10), (3,13,14), (5,9,12), (5,11,14), (6,11,13), (7,9,14),
(7,10,13), (7,11,12), (12,21,25), (12,37,41)`. -/
theorem block_masks (n : ℕ) (hodd : ∃ k : ℕ, a n = (k : ℚ) ∧ Odd k) :
    (∀ u v : ℕ, u < 16 → v < 16 →
      (u * n) ^^^ (v * n) = (u ^^^ v) * n ∧ (u * n) &&& (v * n) = (u &&& v) * n ∧
        (u * n) ||| (v * n) = (u ||| v) * n) ∧
    (1 * n) ^^^ (14 * n) = 15 * n ∧ (3 * n) ^^^ (9 * n) = 10 * n ∧
    (3 * n) ^^^ (13 * n) = 14 * n ∧ (5 * n) ^^^ (9 * n) = 12 * n ∧
    (5 * n) ^^^ (11 * n) = 14 * n ∧ (6 * n) ^^^ (11 * n) = 13 * n ∧
    (7 * n) ^^^ (9 * n) = 14 * n ∧ (7 * n) ^^^ (10 * n) = 13 * n ∧
    (7 * n) ^^^ (11 * n) = 12 * n ∧
    (12 * n) ^^^ (21 * n) = 25 * n ∧ (12 * n) ^^^ (37 * n) = 41 * n := by
  have hs : spacedBits n := by
    obtain ⟨k, hk, hko⟩ := hodd
    obtain ⟨m, hm, hmo⟩ := result n
    have : k = m := by exact_mod_cast hk.symm.trans hm
    exact hmo.mp (this ▸ hko)
  have H := spaced_masks n hs
  refine ⟨H, (H 1 14 (by norm_num) (by norm_num)).1, (H 3 9 (by norm_num) (by norm_num)).1,
    (H 3 13 (by norm_num) (by norm_num)).1, (H 5 9 (by norm_num) (by norm_num)).1,
    (H 5 11 (by norm_num) (by norm_num)).1, (H 6 11 (by norm_num) (by norm_num)).1,
    (H 7 9 (by norm_num) (by norm_num)).1, (H 7 10 (by norm_num) (by norm_num)).1,
    (H 7 11 (by norm_num) (by norm_num)).1, (carry_masks n hs).1,
    (carry_masks n hs).2.2.1⟩

end D5.S3.Arith.FactorialRatio.BalaA295462BlockMasks
