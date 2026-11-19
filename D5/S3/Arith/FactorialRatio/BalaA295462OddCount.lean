/- GID: D5/S3/Arith/FactorialRatio/BalaA295462OddCount
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/BalaA295462OddCount
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The odd A295462 values below 2^m are counted by c_m=c_{m-1}+c_{m-4} and enumerated by blocks. -/

import D5.S3.Arith.FactorialRatio.BalaA295462Parity
import Mathlib.Data.Nat.Nth

/-! # Counting and enumerating the odd values of A295462

The value `a(n)` of OEIS A295462 is odd exactly when the binary positions of `n` are
four-separated. Splitting by the top binary digit, the number `c m` of odd values with
`n < 2^m` satisfies `c_0 = 1, c_1 = 2, c_2 = 3, c_3 = 4` and `c_m = c_{m-1} + c_{m-4}`,
and the increasing enumeration `u` of these indices satisfies `u_j = 2^e + u_{j - c_e}`.
-/

namespace D5.S3.Arith.FactorialRatio.BalaA295462OddCount

open D5.S3.Arith.FactorialRatio.BalaA295462Parity
open Classical

noncomputable section

/-- `a n` is an odd natural number. -/
def oddValue (n : ℕ) : Prop := ∃ k : ℕ, a n = (k : ℚ) ∧ Odd k

/-- The number of odd values `a n` with `n < 2^m`. -/
def c (m : ℕ) : ℕ := ((Finset.range (2 ^ m)).filter oddValue).card

/-- The indices of the odd values of `a`, in increasing order. -/
def u (j : ℕ) : ℕ := Nat.nth oddValue j

private lemma oddValue_iff (n : ℕ) : oddValue n ↔ spacedBits n := by
  obtain ⟨m, ham, hodd⟩ := result n
  constructor
  · rintro ⟨k, hk, hko⟩
    have : k = m := by exact_mod_cast hk.symm.trans ham
    rw [← hodd, ← this]
    exact hko
  · intro h
    exact ⟨m, ham, hodd.mpr h⟩

private lemma oddValue_eq : oddValue = spacedBits := funext fun n => propext (oddValue_iff n)

private lemma bit_shift {e y : ℕ} (hy : y < 2 ^ e) (i : ℕ) :
    (2 ^ e + y).testBit i = (decide (i = e) || y.testBit i) := by
  rcases lt_trichotomy i e with h | h | h
  · rw [Nat.testBit_two_pow_add_gt h]
    simp [show i ≠ e by omega]
  · subst h
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy]
    simp
  · have hlt : 2 ^ e + y < 2 ^ i := by
      have : 2 ^ (e + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at this
      omega
    rw [Nat.testBit_lt_two_pow hlt, Nat.testBit_lt_two_pow (lt_of_lt_of_le hy
      (Nat.pow_le_pow_right (by norm_num) h.le))]
    simp [show i ≠ e by omega]

private lemma low_bits_iff (e y : ℕ) :
    (∀ i, y.testBit i = true → i + 4 ≤ e) ↔ y < 2 ^ (e - 3) := by
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_contra hb
    have := h i (by simpa using hb)
    omega
  · intro hy i hi
    by_contra hlt
    have hle : 2 ^ (e - 3) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hle)] at hi
    exact Bool.false_ne_true hi

private lemma spaced_shift {e y : ℕ} (hy : y < 2 ^ e) :
    spacedBits (2 ^ e + y) ↔ spacedBits y ∧ y < 2 ^ (e - 3) := by
  rw [← low_bits_iff]
  unfold spacedBits
  simp only [bit_shift hy, Bool.or_eq_true, decide_eq_true_eq]
  have hye : ∀ i, y.testBit i = true → i < e := by
    intro i hi
    by_contra h
    have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hy
      (Nat.pow_le_pow_right (by norm_num) (not_lt.mp h)))
    rw [this] at hi
    exact Bool.false_ne_true hi
  constructor
  · intro h
    refine ⟨fun i j hij hi hj => h i j hij (Or.inr hi) (Or.inr hj), fun i hi => ?_⟩
    exact h i e (hye i hi) (Or.inr hi) (Or.inl rfl)
  · rintro ⟨h1, h2⟩ i j hij hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · omega
    · have := hye j hj
      omega
    · subst hj
      exact h2 i hi
    · exact h1 i j hij hi hj

private lemma spaced_zero : spacedBits 0 := by
  intro i j _ hi
  simp at hi

private lemma spaced_two_pow (e : ℕ) : spacedBits (2 ^ e) := by
  intro i j hij hi hj
  rw [Nat.testBit_two_pow] at hi hj
  simp at hi hj
  omega

private lemma c_eq_count (m : ℕ) : c m = Nat.count spacedBits (2 ^ m) := by
  rw [c, Nat.count_eq_card_filter_range, oddValue_eq]

private lemma count_low (e : ℕ) :
    Nat.count (fun k => spacedBits (2 ^ e + k)) (2 ^ e) = Nat.count spacedBits (2 ^ (e - 3)) := by
  have hle : 2 ^ (e - 3) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, h⟩
    have := (spaced_shift hk).mp h
    exact ⟨this.2, this.1⟩
  · rintro ⟨hk, h⟩
    have hk' : k < 2 ^ e := lt_of_lt_of_le hk hle
    exact ⟨hk', (spaced_shift hk').mpr ⟨h, hk⟩⟩

private lemma c_succ (e : ℕ) : c (e + 1) = c e + c (e - 3) := by
  rw [c_eq_count, c_eq_count, c_eq_count, pow_succ, mul_two, Nat.count_add, count_low]

/-- The odd values below `2^m` are counted by `c_0 = 1, c_1 = 2, c_2 = 3, c_3 = 4` and
`c_m = c_{m-1} + c_{m-4}` for every `m ≥ 4`. -/
theorem count_recurrence :
    c 0 = 1 ∧ c 1 = 2 ∧ c 2 = 3 ∧ c 3 = 4 ∧ ∀ m, 4 ≤ m → c m = c (m - 1) + c (m - 4) := by
  have h0 : c 0 = 1 := by
    rw [c_eq_count, pow_zero, Nat.count_one]
    simp [spaced_zero]
  have h1 : c 1 = 2 := by rw [c_succ 0, h0]
  have h2 : c 2 = 3 := by rw [c_succ 1, h1, show 1 - 3 = 0 by rfl, h0]
  have h3 : c 3 = 4 := by rw [c_succ 2, h2, show 2 - 3 = 0 by rfl, h0]
  refine ⟨h0, h1, h2, h3, fun m hm => ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
  rw [c_succ e, show e + 1 - 1 = e by omega, show e + 1 - 4 = e - 3 by omega]

private lemma c_pos (m : ℕ) : 1 ≤ c m := by
  induction m with
  | zero => rw [(count_recurrence).1]
  | succ m ih => rw [c_succ]; omega

private lemma c_strictMono : StrictMono c :=
  strictMono_nat_of_lt_succ fun m => by rw [c_succ]; have := c_pos (m - 3); omega

private lemma spaced_infinite : (Set.ofPred spacedBits).Infinite :=
  Set.infinite_of_forall_exists_gt fun n => ⟨2 ^ n, spaced_two_pow n, Nat.lt_two_pow_self⟩

/-- The increasing enumeration of the indices of odd values satisfies `u_0 = 0`, and for every
`j > 0` there is exactly one `e` with `c_e ≤ j < c_{e+1}`, for which `u_j = 2^e + u_{j - c_e}`. -/
theorem enumeration :
    u 0 = 0 ∧ ∀ j, 0 < j →
      (∃! e, c e ≤ j ∧ j < c (e + 1)) ∧
      ∀ e, c e ≤ j → j < c (e + 1) → u j = 2 ^ e + u (j - c e) := by
  have hu : u = Nat.nth spacedBits := by
    funext j
    rw [u, oddValue_eq]
  refine ⟨?_, fun j hj => ⟨?_, fun e he hj' => ?_⟩⟩
  · rw [hu]
    exact Nat.nth_zero_of_zero spaced_zero
  · have hex : ∃ e, j < c (e + 1) := ⟨j, by
      have := c_strictMono.id_le (j + 1)
      have h0 := c_pos 0
      have : j + 1 ≤ c (j + 1) := c_strictMono.id_le (j + 1)
      omega⟩
    refine ⟨Nat.find hex, ⟨?_, Nat.find_spec hex⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · rw [h, (count_recurrence).1]
        omega
      · obtain ⟨e', he'⟩ : ∃ e', Nat.find hex = e' + 1 := ⟨Nat.find hex - 1, by omega⟩
        have := Nat.find_min hex (show e' < Nat.find hex by omega)
        rw [he']
        omega
    · rintro e' ⟨h1, h2⟩
      rcases lt_trichotomy e' (Nat.find hex) with h | h | h
      · exact absurd h2 (Nat.find_min hex h)
      · exact h
      · have := c_strictMono.monotone (show Nat.find hex + 1 ≤ e' by omega)
        have := Nat.find_spec hex
        omega
  · rw [hu]
    set i := j - c e
    have hi : i < Nat.count spacedBits (2 ^ (e - 3)) := by
      rw [← c_eq_count]
      have := c_succ e
      omega
    have hlt : Nat.nth spacedBits i < 2 ^ (e - 3) := Nat.nth_lt_of_lt_count hi
    have hle : 2 ^ (e - 3) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hp : spacedBits (2 ^ e + Nat.nth spacedBits i) :=
      (spaced_shift (lt_of_lt_of_le hlt hle)).mpr
        ⟨Nat.nth_mem_of_infinite spaced_infinite i, hlt⟩
    have hcount : Nat.count spacedBits (2 ^ e + Nat.nth spacedBits i) = j := by
      rw [Nat.count_add]
      have hlow : Nat.count (fun k => spacedBits (2 ^ e + k)) (Nat.nth spacedBits i) =
          Nat.count spacedBits (Nat.nth spacedBits i) := by
        rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hk, h⟩
          exact ⟨hk, ((spaced_shift (by omega)).mp h).1⟩
        · rintro ⟨hk, h⟩
          exact ⟨hk, (spaced_shift (by omega)).mpr ⟨h, by omega⟩⟩
      rw [hlow, Nat.count_nth_of_infinite spaced_infinite, ← c_eq_count]
      omega
    rw [← hcount, Nat.nth_count hp]

end

end D5.S3.Arith.FactorialRatio.BalaA295462OddCount
