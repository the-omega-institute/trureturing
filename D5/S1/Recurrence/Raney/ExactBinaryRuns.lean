/- GID: D5/S1/Recurrence/Raney/ExactBinaryRuns
   generality: G
   mirror-B: D5/B/S1/Recurrence/Raney/ExactBinaryRuns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact binary maximal zero runs of the literal Raney sequence. -/

import D5.S1.Recurrence.Raney.ZeroRunFamilies

/-! Exact binary support and maximal zero intervals of the literal integral Raney numbers. -/

namespace TrureTuring.Raney

private abbrev BinarySupported (n : Nat) : Prop :=
  (raneyNumber 3 1 n : ZMod 2) ≠ 0

private theorem binary_readout (n : Nat) :
    (raneyNumber 3 1 n : ZMod 2) = (Nat.choose (3 * n) n : ZMod 2) := by
  have bridge : (if n = 0 then 0 else 2 * Nat.choose (3 * n) (n - 1)) ≤
      Nat.choose (3 * n) n ∧
      raneyNumber 3 1 n = Nat.choose (3 * n) n -
        (if n = 0 then 0 else 2 * Nat.choose (3 * n) (n - 1)) := by
    cases n with
    | zero => simp [raneyNumber]
    | succ n =>
      let N := 3 * (n + 1) + 1
      let M := 3 * (n + 1)
      let C := Nat.choose N (n + 1)
      let B := Nat.choose M n
      let D := Nat.choose M (n + 1)
      have hN : 0 < N := by dsimp [N]; omega
      have hPred : N * B = C * (n + 1) := by
        simpa [N, M, B, C, Nat.mul_comm] using Nat.add_one_mul_choose_eq M n
      have hNormal : D * N = C * (2 * (n + 1) + 1) := by
        have h := Nat.choose_mul_succ_eq M (n + 1)
        have hm : M + 1 = N := rfl
        rw [hm, show N - (n + 1) = 2 * (n + 1) + 1 by dsimp [N]; omega] at h
        exact h
      have hDecomp : D * N = (2 * B) * N + C := by
        calc
          D * N = C * (2 * (n + 1) + 1) := hNormal
          _ = 2 * (C * (n + 1)) + C := by ring
          _ = (2 * B) * N + C := by rw [← hPred]; ring
      have hLe : 2 * B ≤ D :=
        Nat.le_of_mul_le_mul_right (by rw [hDecomp]; omega) hN
      have hCross : N * (D - 2 * B) = C := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_comm N D, Nat.mul_comm N (2 * B)]
        omega
      refine ⟨by simpa [B, D, M] using hLe, ?_⟩
      have hQuot : C / N = D - 2 * B := by
        rw [← hCross, Nat.mul_div_right _ hN]
      simpa [raneyNumber, C, D, B, M, N] using hQuot
  rw [bridge.2, Nat.cast_sub bridge.1]
  split_ifs
  · simp
  · rw [Nat.cast_mul, show ((2 : Nat) : ZMod 2) = 0 by decide, zero_mul, sub_zero]

private theorem binary_lucas (a b : Nat) :
    (Nat.choose a b : ZMod 2) =
      (Nat.choose (a % 2) (b % 2) : ZMod 2) *
        (Nat.choose (a / 2) (b / 2) : ZMod 2) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := a) (k := b) (p := 2)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  exact_mod_cast h

private theorem binary_support_zero : BinarySupported 0 := by
  simp [BinarySupported, raneyNumber]

private theorem binary_support_even (n : Nat) :
    BinarySupported (2 * n) ↔ BinarySupported n := by
  simp only [BinarySupported, binary_readout]
  rw [show 3 * (2 * n) = 2 * (3 * n) by ring, binary_lucas]
  simp

private theorem binary_support_one (n : Nat) :
    BinarySupported (4 * n + 1) ↔ BinarySupported n := by
  simp only [BinarySupported, binary_readout]
  rw [binary_lucas,
    show 3 * (4 * n + 1) % 2 = 1 by omega,
    show (4 * n + 1) % 2 = 1 by omega,
    show 3 * (4 * n + 1) / 2 = 6 * n + 1 by omega,
    show (4 * n + 1) / 2 = 2 * n by omega]
  simp only [Nat.choose_self, Nat.cast_one, one_mul]
  rw [binary_lucas,
    show (6 * n + 1) % 2 = 1 by omega,
    show (2 * n) % 2 = 0 by omega,
    show (6 * n + 1) / 2 = 3 * n by omega,
    show (2 * n) / 2 = n by omega]
  simp

private theorem binary_support_three (n : Nat) : ¬ BinarySupported (4 * n + 3) := by
  simp only [BinarySupported, binary_readout, not_not]
  rw [binary_lucas,
    show 3 * (4 * n + 3) % 2 = 1 by omega,
    show (4 * n + 3) % 2 = 1 by omega,
    show 3 * (4 * n + 3) / 2 = 6 * n + 4 by omega,
    show (4 * n + 3) / 2 = 2 * n + 1 by omega]
  simp only [Nat.choose_self, Nat.cast_one, one_mul]
  rw [binary_lucas,
    show (6 * n + 4) % 2 = 0 by omega,
    show (2 * n + 1) % 2 = 1 by omega]
  simp

private theorem binary_support_one_index : BinarySupported 1 := by
  simpa using (binary_support_one 0).mpr binary_support_zero

private theorem binary_support_power (m : Nat) : BinarySupported (2 ^ m) := by
  have h := Choose.choose_pow_mul_pow_mul_modEq_choose
    (p := 2) (k := m) (a := 3) (b := 1)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  have hc : (Nat.choose (2 ^ m * 3) (2 ^ m * 1) : ZMod 2) =
      (Nat.choose 3 1 : ZMod 2) := by exact_mod_cast h
  change (raneyNumber 3 1 (2 ^ m) : ZMod 2) ≠ 0
  rw [binary_readout]
  have hc' : (Nat.choose (3 * 2 ^ m) (2 ^ m) : ZMod 2) = (3 : ZMod 2) := by
    simpa [Nat.mul_comm] using hc
  rw [hc']
  decide

/-- The top half of each binary prefix is a translated shorter literal support. -/
private theorem binary_support_high (m n : Nat) (hn : n < 2 ^ m) :
    BinarySupported (2 ^ m + n) ↔ n < 2 ^ (m - 1) ∧ BinarySupported n := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    match m with
    | 0 =>
      have : n = 0 := by simpa using hn
      subst n
      change BinarySupported 1 ↔ 0 < 1 ∧ BinarySupported 0
      exact ⟨fun _ => ⟨by decide, binary_support_zero⟩,
        fun _ => binary_support_one_index⟩
    | 1 =>
      have : n = 0 ∨ n = 1 := by norm_num at hn; omega
      rcases this with rfl | rfl
      · norm_num
        exact ⟨fun _ => binary_support_zero, fun _ => binary_support_power 1⟩
      · simpa using binary_support_three 0
    | k + 2 =>
      have hp : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
      have hp' : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hr := Nat.mod_lt n (by decide : 0 < 4)
      by_cases heven : n % 2 = 0
      · obtain ⟨t, rfl⟩ : ∃ t, n = 2 * t := ⟨n / 2, by omega⟩
        have ht : t < 2 ^ (k + 1) := by rw [hp, hp'] at *; omega
        rw [show 2 ^ (k + 2) + 2 * t = 2 * (2 ^ (k + 1) + t) by
          rw [hp, hp']; ring, binary_support_even,
          ih (k + 1) (by omega) t ht, binary_support_even]
        have heq : 2 ^ (k + 1 - 1) = 2 ^ k := by congr 1
        rw [heq, show k + 2 - 1 = k + 1 by omega, hp']
        exact and_congr (by omega) Iff.rfl
      · by_cases hrem : n % 4 = 1
        · obtain ⟨t, rfl⟩ : ∃ t, n = 4 * t + 1 := ⟨n / 4, by omega⟩
          have ht : t < 2 ^ k := by rw [hp] at hn; omega
          rw [show 2 ^ (k + 2) + (4 * t + 1) = 4 * (2 ^ k + t) + 1 by
            rw [hp]; ring, binary_support_one,
            ih k (by omega) t ht, binary_support_one]
          rw [show k + 2 - 1 = k + 1 by omega, hp']
          apply and_congr_left
          intro _
          cases k with
          | zero =>
            have : t = 0 := by simpa using ht
            subst t
            norm_num
          | succ k =>
            simp only [Nat.add_sub_cancel, pow_succ]
            omega
        · have hnrem : n % 4 = 3 := by omega
          obtain ⟨t, rfl⟩ : ∃ t, n = 4 * t + 3 := ⟨n / 4, by omega⟩
          rw [show 2 ^ (k + 2) + (4 * t + 3) = 4 * (2 ^ k + t) + 3 by
            rw [hp]; ring]
          simp [binary_support_three]

private theorem binary_power_mod_three (m : Nat) : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> simp [h]

private theorem binary_rounding (m : Nat) :
    (2 ^ (m + 1) + 2) / 3 = 2 ^ (m + 1) / 3 + 1 ∧
    2 ^ m - 1 - 2 ^ (m + 1) / 3 = 2 ^ m / 3 := by
  have hp := binary_power_mod_three m
  have hp' := binary_power_mod_three (m + 1)
  have hpos : 0 < 2 ^ m := by positivity
  rw [pow_succ] at *
  omega

private theorem binary_maximum (m : Nat) :
    2 ^ (m + 1) / 3 < 2 ^ m ∧
    BinarySupported (2 ^ (m + 1) / 3) ∧
    (∀ n, n < 2 ^ m → BinarySupported n → n ≤ 2 ^ (m + 1) / 3) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 =>
      change 0 < 1 ∧ BinarySupported 0 ∧ (∀ n, n < 1 → BinarySupported n → n ≤ 0)
      exact ⟨by decide, binary_support_zero, fun n hn _ => by omega⟩
    | 1 =>
      change 1 < 2 ∧ BinarySupported 1 ∧ (∀ n, n < 2 → BinarySupported n → n ≤ 1)
      exact ⟨by decide, binary_support_one_index, fun n hn _ => by omega⟩
    | k + 2 =>
      have old := ih k (by omega)
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
      have hp' : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have htop : 2 ^ (k + 2 + 1) / 3 = 2 ^ (k + 1) + 2 ^ (k + 1) / 3 := by
        rw [show k + 2 + 1 = (k + 1) + 2 by omega, pow_add]
        omega
      rw [htop]
      have hsmall : 2 ^ (k + 1) / 3 < 2 ^ (k + 1) := by
        have hpos : 0 < 2 ^ k := by positivity
        omega
      refine ⟨by omega, ?_, ?_⟩
      · exact (binary_support_high (k + 1) _ hsmall).mpr
          ⟨by simpa using old.1, old.2.1⟩
      · intro n hn hs
        by_cases hnLow : n < 2 ^ (k + 1)
        · omega
        · have hn' : n - 2 ^ (k + 1) < 2 ^ (k + 1) := by omega
          have heq : 2 ^ (k + 1) + (n - 2 ^ (k + 1)) = n := by omega
          have hh := (binary_support_high (k + 1) _ hn').mp (by simpa only [heq] using hs)
          have hsmall' : n - 2 ^ (k + 1) < 2 ^ k := by simpa using hh.1
          have hle := old.2.2 _ hsmall' hh.2
          omega

/-- Every positive gap in an augmented finite prefix descends either to an
earlier prefix or to its terminal gap. Both endpoints are actual support. -/
private theorem binary_gap_prefix (M a b : Nat)
    (hab : a + 1 < b) (hb : b ≤ 2 ^ M)
    (haS : BinarySupported a) (hbS : BinarySupported b)
    (hgap : ∀ n, a < n → n < b → ¬ BinarySupported n) :
    ∃ m, 2 ≤ m ∧ m ≤ M ∧ b - a - 1 = 2 ^ m / 3 ∧ 2 ^ m ≤ b := by
  induction M using Nat.strong_induction_on generalizing a b with
  | h M ih =>
    match M with
    | 0 => norm_num at hb; omega
    | 1 =>
      have hb' : b ≤ 2 := by simpa using hb
      exact (hgap 1 (by omega) (by omega) binary_support_one_index).elim
    | k + 2 =>
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
      by_cases hbLow : b ≤ 2 ^ (k + 1)
      · obtain ⟨m, hm, hmk, hlen, hfirst⟩ :=
          ih (k + 1) (by omega) a b hab hbLow haS hbS hgap
        exact ⟨m, hm, by omega, hlen, hfirst⟩
      · have haHigh : 2 ^ (k + 1) ≤ a := by
          by_contra h
          exact hgap _ (by omega) (by omega) (binary_support_power (k + 1))
        by_cases hbTop : b = 2 ^ (k + 2)
        · have hmax := binary_maximum (k + 2)
          have haLt : a < 2 ^ (k + 2) := by omega
          have haLe := hmax.2.2 a haLt haS
          have haEq : a = 2 ^ (k + 2 + 1) / 3 := by
            by_contra h
            exact hgap _ (by omega) (by omega) hmax.2.1
          refine ⟨k + 2, by omega, le_rfl, ?_, by omega⟩
          rw [hbTop, haEq]
          have hround := (binary_rounding (k + 2)).2
          omega
        · have hbLt : b - 2 ^ (k + 1) < 2 ^ (k + 1) := by omega
          have haLt : a - 2 ^ (k + 1) < 2 ^ (k + 1) := by omega
          have heqa : 2 ^ (k + 1) + (a - 2 ^ (k + 1)) = a := by omega
          have heqb : 2 ^ (k + 1) + (b - 2 ^ (k + 1)) = b := by omega
          have ha' := (binary_support_high (k + 1) _ haLt).mp (by simpa only [heqa] using haS)
          have hb' := (binary_support_high (k + 1) _ hbLt).mp (by simpa only [heqb] using hbS)
          have haSmall : a - 2 ^ (k + 1) < 2 ^ k := by simpa using ha'.1
          have hbSmall : b - 2 ^ (k + 1) < 2 ^ k := by simpa using hb'.1
          have gap' : ∀ n, a - 2 ^ (k + 1) < n → n < b - 2 ^ (k + 1) →
              ¬ BinarySupported n := by
            intro n han hnb hsn
            have hnSmall : n < 2 ^ k := by omega
            have hnLarge : n < 2 ^ (k + 1) := by
              have : 2 ^ k ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
              omega
            have hnS := (binary_support_high (k + 1) n hnLarge).mpr
              ⟨by simpa using hnSmall, hsn⟩
            exact hgap (2 ^ (k + 1) + n) (by omega) (by omega) hnS
          obtain ⟨m, hm, hmk, hlen, hfirst⟩ :=
            ih k (by omega) (a - 2 ^ (k + 1)) (b - 2 ^ (k + 1))
              (by omega) hbSmall.le ha'.2 hb'.2 gap'
          exact ⟨m, hm, by omega, by omega, by omega⟩

private theorem binary_length_strict (m k : Nat) (hm : 2 ≤ m) (hmk : m < k) :
    2 ^ m / 3 < 2 ^ k / 3 := by
  have hmPow : 4 ≤ 2 ^ m := by
    calc
      4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  have hpow : 2 * 2 ^ m ≤ 2 ^ k := by
    calc
      2 * 2 ^ m = 2 ^ (m + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hmk
  omega

private theorem binary_interval_classification (first last : Nat)
    (block : IsMaximalDeltaInterval {0}
      (fun n => (raneyNumber 3 1 n : ZMod 2)) first last) :
    ∃ m, 2 ≤ m ∧ last + 1 - first = 2 ^ m / 3 ∧
      (2 ^ (m + 1) + 2) / 3 ≤ first := by
  simp only [IsMaximalDeltaInterval, Finset.mem_singleton] at block
  have hfirst : 0 < first := by
    by_contra h
    have hf : first = 0 := by omega
    exact binary_support_zero (block.2.1 0 (by omega) (by omega))
  have hleft : BinarySupported (first - 1) := by
    rcases block.2.2.1 with h | h
    · omega
    · exact h
  have hright : BinarySupported (last + 1) := block.2.2.2
  have hgap : ∀ n, first - 1 < n → n < last + 1 → ¬ BinarySupported n := by
    intro n hn hn' hs
    exact hs (block.2.1 n (by omega) (by omega))
  have hb : last + 1 ≤ 2 ^ (last + 1) :=
    (Nat.lt_pow_self (by decide : 1 < 2)).le
  obtain ⟨m, hm, _, hlen, hbound⟩ := binary_gap_prefix (last + 1) (first - 1)
    (last + 1) (by omega) hb hleft hright hgap
  have hround := binary_rounding m
  have hmax := (binary_maximum m).1
  refine ⟨m, hm, by omega, ?_⟩
  omega

private theorem binary_terminal_interval (m : Nat) (hm : 2 ≤ m) :
    IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 2))
      ((2 ^ (m + 1) + 2) / 3) (2 ^ m - 1) ∧
    (2 ^ m - 1) + 1 - ((2 ^ (m + 1) + 2) / 3) = 2 ^ m / 3 := by
  have hmax := binary_maximum m
  have hround := binary_rounding m
  have hp : 0 < 2 ^ m := by positivity
  have hmPow : 4 ≤ 2 ^ m := by
    calc
      4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  have hlenPos : 0 < 2 ^ m / 3 := by omega
  simp only [IsMaximalDeltaInterval, Finset.mem_singleton]
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, by omega⟩
  · intro n hfirst hlast
    by_contra hn
    have hle := hmax.2.2 n (by omega) hn
    omega
  · right
    have heq : (2 ^ (m + 1) + 2) / 3 - 1 = 2 ^ (m + 1) / 3 := by omega
    simpa only [heq] using hmax.2.1
  · have heq : 2 ^ m - 1 + 1 = 2 ^ m := by omega
    simpa only [heq] using binary_support_power m

/-- All positive maximal binary zero-run lengths of the literal Raney sequence
are exactly `floor (2^m/3)` for `m ≥ 2`. The displayed terminal intervals are
actual maximal intervals, and every earlier maximal interval is strictly shorter.
The strict earlier bound implies the source's tied-record convention as well. -/
theorem raney_binary_exact_zero_run_spectrum :
    (∀ first last : Nat,
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 2)) first last →
      ∃ m : Nat, 2 ≤ m ∧ last + 1 - first = 2 ^ m / 3 ∧
        (2 ^ (m + 1) + 2) / 3 ≤ first) ∧
    (∀ m : Nat, 2 ≤ m →
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 2))
        ((2 ^ (m + 1) + 2) / 3) (2 ^ m - 1) ∧
      (2 ^ m - 1) + 1 - ((2 ^ (m + 1) + 2) / 3) = 2 ^ m / 3 ∧
      ∀ first last : Nat,
        IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 2)) first last →
        first < (2 ^ (m + 1) + 2) / 3 → last + 1 - first < 2 ^ m / 3) ∧
    (∀ m k : Nat, 2 ≤ m → m < k → 2 ^ m / 3 < 2 ^ k / 3) := by
  refine ⟨binary_interval_classification, ?_, binary_length_strict⟩
  intro m hm
  obtain ⟨hblock, hlen⟩ := binary_terminal_interval m hm
  refine ⟨hblock, hlen, ?_⟩
  intro first last block hearlier
  obtain ⟨k, hk, hklength, hkfirst⟩ := binary_interval_classification first last block
  have hkm : k < m := by
    by_contra h
    have hpow : 2 ^ (m + 1) ≤ 2 ^ (k + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [hklength]
  exact binary_length_strict k m hk hkm

#print axioms raney_binary_exact_zero_run_spectrum

end TrureTuring.Raney
