/- GID: D5/S1/Recurrence/Raney/ExactTernaryRuns
   generality: I
   mirror-B: D5/B/S1/Recurrence/Raney/ExactTernaryRuns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact ternary support and all maximal zero intervals of the literal Raney quotient. -/

import D5.S1.Recurrence.Raney.ZeroRunFamilies
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.IsNormal

/-! # Exact zero runs at the exceptional prime three

The nonzero support is derived from the literal integral quotient by Lucas'
theorem. The prime and Raney parameters are fixed in this result.
-/

namespace TrureTuring.Raney

private theorem ternary_quotient_readout (n : Nat) :
    (raneyNumber 3 1 n : ZMod 3) = (Nat.choose (3 * n + 1) n : ZMod 3) := by
  have hdvd : 3 * n + 1 ∣ Nat.choose (3 * n + 1) n := by
    cases n with
    | zero => simp
    | succ n =>
      have hcop : (3 * (n + 1) + 1).Coprime (n + 1) := by simp
      apply hcop.dvd_of_dvd_mul_right
      rw [← Nat.add_one_mul_choose_eq]
      exact dvd_mul_right _ _
  have hmul : raneyNumber 3 1 n * (3 * n + 1) = Nat.choose (3 * n + 1) n := by
    simpa [raneyNumber] using Nat.div_mul_cancel hdvd
  have hcast := congrArg (fun k : Nat => (k : ZMod 3)) hmul
  have hthree : (3 : ZMod 3) = 0 := by decide
  simpa [Nat.cast_add, Nat.cast_mul, hthree] using hcast

private theorem ternary_lucas (N K : Nat) :
    (Nat.choose N K : ZMod 3) =
      (Nat.choose (N % 3) (K % 3) : ZMod 3) *
        (Nat.choose (N / 3) (K / 3) : ZMod 3) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := N) (k := K) (p := 3)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  exact_mod_cast h

private theorem ternary_central_zero (n : Nat) (hn : 0 < n) :
    (Nat.choose (3 * n) n : ZMod 3) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [ternary_lucas]
    by_cases hd : n % 3 = 0
    · have hnq : 0 < n / 3 := by omega
      have hnlt : n / 3 < n := Nat.div_lt_self hn (by decide)
      have hnd : n = 3 * (n / 3) := by omega
      simp only [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by decide : 0 < 3),
        hd, Nat.choose_zero_right, Nat.cast_one, one_mul]
      have hi := ih (n / 3) hnlt hnq
      rwa [← hnd] at hi
    · have hchoose : Nat.choose 0 (n % 3) = 0 :=
        Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hd)
      simp [hchoose]

private theorem ternary_digit_one (n : Nat) :
    (raneyNumber 3 1 (3 * n + 1) : ZMod 3) = (raneyNumber 3 1 n : ZMod 3) := by
  rw [ternary_quotient_readout, ternary_quotient_readout, ternary_lucas]
  have htop : 3 * (3 * n + 1) + 1 = 1 + 3 * (3 * n + 1) := by omega
  have hlow : (3 * n + 1) / 3 = n := by omega
  rw [htop]
  simp [Nat.add_mul_div_left, Nat.add_mul_mod_self_left, hlow]

private theorem ternary_digit_zero (n : Nat) (hn : 0 < n) :
    (raneyNumber 3 1 (3 * n) : ZMod 3) = 0 := by
  rw [ternary_quotient_readout, ternary_lucas]
  have htop : 3 * (3 * n) + 1 = 1 + 3 * (3 * n) := by omega
  rw [htop]
  simpa [Nat.add_mul_div_left, Nat.add_mul_mod_self_left] using ternary_central_zero n hn

private theorem ternary_digit_two (n : Nat) :
    (raneyNumber 3 1 (3 * n + 2) : ZMod 3) = 0 := by
  rw [ternary_quotient_readout, ternary_lucas]
  have htop : 3 * (3 * n + 2) + 1 = 1 + 3 * (3 * n + 2) := by omega
  rw [htop]
  simp [Nat.add_mul_mod_self_left]

private theorem ternary_power_rec (n : Nat) (hn : 0 < n) :
    (∃ m : Nat, 2 * n + 1 = 3 ^ m) ↔
      n % 3 = 1 ∧ ∃ m : Nat, 2 * (n / 3) + 1 = 3 ^ m := by
  constructor
  · rintro ⟨m, hm⟩
    cases m with
    | zero => norm_num at hm; omega
    | succ m =>
      rw [pow_succ] at hm
      have hd : n % 3 = 1 := by omega
      exact ⟨hd, m, by omega⟩
  · rintro ⟨hd, m, hm⟩
    exact ⟨m + 1, by rw [pow_succ]; omega⟩

open Classical in
private theorem ternary_coefficients (n : Nat) :
    (raneyNumber 3 1 n : ZMod 3) =
      if ∃ m : Nat, 2 * n + 1 = 3 ^ m then 1 else 0 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have hex : ∃ m : Nat, 2 * 0 + 1 = 3 ^ m := ⟨0, by decide⟩
      simp [hex, raneyNumber]
    · have hnpos := Nat.pos_of_ne_zero hn
      have hdlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
      have hq := ih (n / 3) (Nat.div_lt_self hnpos (by decide))
      have hrec := ternary_power_rec n hnpos
      rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with hd | hd | hd
      · have hnd : n = 3 * (n / 3) := by omega
        have hc : (raneyNumber 3 1 n : ZMod 3) = 0 := by
          rw [hnd]
          exact ternary_digit_zero _ (by omega)
        have hnot : ¬ ∃ m : Nat, 2 * n + 1 = 3 ^ m := by
          rw [hrec]
          omega
        simp [hc, hnot]
      · have hnd : n = 3 * (n / 3) + 1 := by omega
        have hc : (raneyNumber 3 1 n : ZMod 3) = (raneyNumber 3 1 (n / 3) : ZMod 3) := by
          conv_lhs => rw [hnd]
          exact ternary_digit_one _
        rw [hc, hq]
        simp only [hrec, hd, true_and]
      · have hnd : n = 3 * (n / 3) + 2 := by omega
        have hc : (raneyNumber 3 1 n : ZMod 3) = 0 := by
          rw [hnd]
          exact ternary_digit_two _
        have hnot : ¬ ∃ m : Nat, 2 * n + 1 = 3 ^ m := by
          rw [hrec]
          omega
        simp [hc, hnot]

private def ternarySupportIndex (m : Nat) : Nat := (3 ^ m - 1) / 2

private theorem ternary_index_identity (m : Nat) :
    2 * ternarySupportIndex m + 1 = 3 ^ m := by
  rcases ((by decide : Odd (3 : Nat)).pow : Odd (3 ^ m)) with ⟨k, hk⟩
  dsimp [ternarySupportIndex]
  omega

private theorem ternary_index_step (m : Nat) :
    ternarySupportIndex (m + 1) = 3 * ternarySupportIndex m + 1 := by
  have hm := ternary_index_identity m
  have hs := ternary_index_identity (m + 1)
  rw [pow_succ] at hs
  omega

private theorem ternary_index_strict : StrictMono ternarySupportIndex := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [ternary_index_step]
  omega

private theorem ternary_support (n : Nat) :
    (raneyNumber 3 1 n : ZMod 3) ≠ 0 ↔ ∃ m : Nat, n = ternarySupportIndex m := by
  classical
  rw [ternary_coefficients]
  have heq : (∃ m : Nat, 2 * n + 1 = 3 ^ m) ↔ ∃ m : Nat, n = ternarySupportIndex m := by
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, by have hi := ternary_index_identity m; omega⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, ternary_index_identity m⟩
  split_ifs with h <;> simp_all

private theorem ternary_gap_zero (m n : Nat)
    (hlo : ternarySupportIndex m < n) (hhi : n < ternarySupportIndex (m + 1)) :
    (raneyNumber 3 1 n : ZMod 3) = 0 := by
  by_contra hn
  obtain ⟨t, ht⟩ := (ternary_support n).1 hn
  exact ternary_index_strict.monotone.ne_of_lt_of_lt_nat m hlo hhi t ht.symm

private theorem ternary_bracket (n : Nat) :
    ∃ m : Nat, ternarySupportIndex m ≤ n ∧ n < ternarySupportIndex (m + 1) := by
  have hnormal : Order.IsNormal ternarySupportIndex := {
    strictMono := ternary_index_strict
    mem_lowerBounds_upperBounds_of_isSuccLimit := by
      intro a ha
      exact (Order.not_isSuccLimit ha).elim }
  exact hnormal.exists_map_le_lt_map_succ (by simp [ternarySupportIndex])

private theorem ternary_maximal_iff (first last : Nat) :
    IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 3)) first last ↔
      ∃ m : Nat, 1 ≤ m ∧ first = ternarySupportIndex m + 1 ∧
        last + 1 = ternarySupportIndex (m + 1) := by
  simp only [IsMaximalDeltaInterval, Finset.mem_singleton]
  constructor
  · rintro ⟨hle, inside, left, right⟩
    have hzero := inside first (by omega) hle
    obtain ⟨m, hlo, hhi⟩ := ternary_bracket first
    have hstrict : ternarySupportIndex m < first := by
      by_contra h
      have heq : first = ternarySupportIndex m := by omega
      exact ((ternary_support first).2 ⟨m, heq⟩) hzero
    have hfirstpos : 0 < first := by omega
    have hleft : (raneyNumber 3 1 (first - 1) : ZMod 3) ≠ 0 :=
      left.resolve_left (by omega)
    have hm : 1 ≤ m := by
      by_contra h
      have hmzero : m = 0 := by omega
      subst m
      norm_num [ternarySupportIndex] at hhi
      omega
    have hf : first = ternarySupportIndex m + 1 := by
      by_contra h
      exact hleft (ternary_gap_zero m (first - 1) (by omega) (by omega))
    have hlower : last < ternarySupportIndex (m + 1) := by
      by_contra h
      have hs : (raneyNumber 3 1 (ternarySupportIndex (m + 1)) : ZMod 3) ≠ 0 :=
        (ternary_support _).2 ⟨m + 1, rfl⟩
      exact hs (inside _ (by omega) (by omega))
    have hl : last + 1 = ternarySupportIndex (m + 1) := by
      by_contra h
      exact right (ternary_gap_zero m (last + 1) (by omega) (by omega))
    exact ⟨m, hm, hf, hl⟩
  · rintro ⟨m, hm, hf, hl⟩
    have hidx : 1 ≤ ternarySupportIndex m := by
      have h := ternary_index_strict.monotone hm
      norm_num [ternarySupportIndex] at h
      exact h
    have hstep := ternary_index_step m
    refine ⟨by omega, ?_, Or.inr ?_, ?_⟩
    · intro n hn hn'
      exact ternary_gap_zero m n (by omega) (by omega)
    · have heq : first - 1 = ternarySupportIndex m := by omega
      exact (ternary_support _).2 ⟨m, heq⟩
    · exact (ternary_support _).2 ⟨m + 1, hl⟩

private theorem ternary_endpoint_formulas (m : Nat) :
    ternarySupportIndex m + 1 = (3 ^ m + 1) / 2 ∧
      ternarySupportIndex (m + 1) - 1 = (3 ^ (m + 1) - 3) / 2 := by
  have hm := ternary_index_identity m
  have hs := ternary_index_identity (m + 1)
  have hstep := ternary_index_step m
  constructor <;> omega

private theorem ternary_length (m : Nat) :
    ternarySupportIndex (m + 1) - (ternarySupportIndex m + 1) = 3 ^ m - 1 := by
  have hm := ternary_index_identity m
  have hs := ternary_index_step m
  omega

private theorem ternary_lengths_strict : StrictMono (fun m : Nat => 3 ^ m - 1) := by
  apply strictMono_nat_of_lt_succ
  intro m
  have hp : 0 < 3 ^ m := pow_pos (by decide) m
  rw [pow_succ]
  omega

open Classical in
/-- The complete positive maximal zero-run spectrum at the exceptional prime
`3`, with its first intervals and the tied left-to-right record convention.
The coefficient formula is for the literal natural-number quotient. -/
theorem raney_three_exact_zero_runs :
    (∀ n : Nat, (raneyNumber 3 1 n : ZMod 3) =
      if ∃ m : Nat, 2 * n + 1 = 3 ^ m then 1 else 0) ∧
    (∀ first last : Nat,
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 3)) first last ↔
        ∃ m : Nat, 1 ≤ m ∧ first = (3 ^ m + 1) / 2 ∧
          last = (3 ^ (m + 1) - 3) / 2) ∧
    (∀ m : Nat, 1 ≤ m →
      (3 ^ (m + 1) - 3) / 2 + 1 - (3 ^ m + 1) / 2 = 3 ^ m - 1) ∧
    StrictMono (fun m : Nat => 3 ^ m - 1) ∧
    (∀ m : Nat, 1 ≤ m → ∀ first last : Nat,
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 3)) first last →
      first ≤ (3 ^ m + 1) / 2 → last + 1 - first ≤ 3 ^ m - 1) ∧
    (∀ m : Nat, 1 ≤ m → ∀ first last : Nat,
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 3)) first last →
      last + 1 - first = 3 ^ m - 1 →
        first = (3 ^ m + 1) / 2 ∧ last = (3 ^ (m + 1) - 3) / 2) := by
  have exactIntervals (first last : Nat) :
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 3)) first last ↔
        ∃ m : Nat, 1 ≤ m ∧ first = (3 ^ m + 1) / 2 ∧
          last = (3 ^ (m + 1) - 3) / 2 := by
    rw [ternary_maximal_iff]
    constructor
    · rintro ⟨m, hm, hf, hl⟩
      have he := ternary_endpoint_formulas m
      exact ⟨m, hm, by omega, by omega⟩
    · rintro ⟨m, hm, hf, hl⟩
      have he := ternary_endpoint_formulas m
      have hs : 0 < ternarySupportIndex (m + 1) := by
        have hi := ternary_index_step m
        omega
      exact ⟨m, hm, by omega, by omega⟩
  have exactLength (m : Nat) (hm : 1 ≤ m) :
      (3 ^ (m + 1) - 3) / 2 + 1 - (3 ^ m + 1) / 2 = 3 ^ m - 1 := by
    have he := ternary_endpoint_formulas m
    have hl := ternary_length m
    have hs := ternary_index_step m
    omega
  refine ⟨ternary_coefficients, exactIntervals, exactLength, ternary_lengths_strict, ?_, ?_⟩
  · intro m hm first last hrun hfirst
    obtain ⟨t, ht, hf, hl⟩ := (exactIntervals first last).1 hrun
    have hmidx := (ternary_endpoint_formulas m).1
    have htidx := (ternary_endpoint_formulas t).1
    have htle : t ≤ m := ternary_index_strict.le_iff_le.mp (by omega)
    have hlen := exactLength t ht
    have hmono := ternary_lengths_strict.monotone htle
    omega
  · intro m hm first last hrun hlength
    obtain ⟨t, ht, hf, hl⟩ := (exactIntervals first last).1 hrun
    have hlen := exactLength t ht
    have htm : t = m := ternary_lengths_strict.injective (by omega)
    subst t
    exact ⟨hf, hl⟩

end TrureTuring.Raney
