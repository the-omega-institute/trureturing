/- GID: D5/S3/Arith/CounterSequences/LeadingCounter
   generality: I
   mirror-B: D5/B/S3/Arith/CounterSequences/LeadingCounter
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact finite multiplicities in the leading-decimal-digit counter sequence. -/

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.CounterSequences.LeadingCounter

/-- The most significant decimal digit; the value at zero is zero. -/
def leading10 (n : ℕ) : ℕ := (Nat.digits 10 n).getLastD 0

private theorem leading10_bounds {n : ℕ} (hn : 0 < n) :
    0 < leading10 n ∧ leading10 n < 10 := by
  have hne := (Nat.digits_ne_nil_iff_ne_zero (b := 10)).mpr (Nat.ne_of_gt hn)
  simp only [leading10, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
    Option.getD_some]
  exact ⟨Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 10 (Nat.ne_of_gt hn)),
    Nat.digits_lt_base (by decide) (List.getLast_mem hne)⟩

/-- The nine counters, indexed from zero; positive inputs use their leading digit minus one. -/
def digit (n : ℕ) : Fin 9 := ⟨(leading10 n - 1) % 9, Nat.mod_lt _ (by decide)⟩

private theorem digit_val {n : ℕ} (hn : 0 < n) : (digit n).val = leading10 n - 1 := by
  have := leading10_bounds hn
  exact Nat.mod_eq_of_lt (by omega)

private theorem digit_eq_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    digit m = digit n ↔ leading10 m = leading10 n := by
  rw [Fin.ext_iff, digit_val hm, digit_val hn]
  have := leading10_bounds hm
  have := leading10_bounds hn
  omega

private theorem leading10_pow (d : Fin 9) (m : ℕ) :
    leading10 (10 ^ m * (d.val + 1)) = d.val + 1 := by
  rw [leading10, Nat.digits_base_pow_mul (by decide) (by omega),
    Nat.digits_of_lt 10 (d.val + 1) (by omega) (by omega), List.getLastD_concat]

private theorem digit_fiber_infinite (d : Fin 9) : {n | 0 < n ∧ digit n = d}.Infinite := by
  have hi : Function.Injective (fun m : ℕ => 10 ^ m * (d.val + 1)) := by
    intro m n h
    exact Nat.pow_right_injective (by decide : 2 ≤ 10)
      (Nat.eq_of_mul_eq_mul_right (by omega) h)
  apply (Set.infinite_range_of_injective hi).mono
  rintro n ⟨m, rfl⟩
  have hp : 0 < 10 ^ m * (d.val + 1) := by positivity
  refine ⟨hp, Fin.ext ?_⟩
  rw [digit_val hp, leading10_pow]
  omega

/-- Before step n: the current term and the counters for the n earlier terms. -/
def orbit : ℕ → ℕ × (Fin 9 → ℕ)
  | 0 => (1, fun _ => 0)
  | n + 1 =>
    let s := orbit n
    let d := digit s.1
    (s.2 d + 1, Function.update s.2 d (s.2 d + 1))

private abbrev term (n : ℕ) : ℕ := (orbit n).1

private theorem term_pos (n : ℕ) : 0 < term n := by
  cases n <;> simp [term, orbit]

private theorem orbit_count (n : ℕ) (d : Fin 9) :
    (orbit n).2 d = Nat.count (fun i => digit (term i) = d) n := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    rw [Nat.count_succ]
    change (Function.update (orbit n).2 (digit (term n)) ((orbit n).2 (digit (term n)) + 1)) d
      = Nat.count (fun i => digit (term i) = d) n + _
    by_cases h : digit (term n) = d
    · subst d
      simp [ih]
    · simp [Function.update_of_ne (Ne.symm h), h, ih]

private theorem term_recurrence (n : ℕ) :
    term (n + 1) = Nat.count (fun i => digit (term i) = digit (term n)) (n + 1) := by
  rw [Nat.count_succ]
  simp only [ite_true]
  exact congrArg (· + 1) (orbit_count n (digit (term n)))

private theorem emit_nth (d : Fin 9) (hd : {i | digit (term i) = d}.Infinite) (k : ℕ) :
    term (Nat.nth (fun i => digit (term i) = d) k + 1) = k + 1 := by
  rw [term_recurrence, Nat.nth_mem_of_infinite hd k,
    Nat.count_nth_succ_of_infinite hd k]

private theorem positive_in_range (k : ℕ) (hk : 0 < k) : k ∈ Set.range term := by
  obtain ⟨d, hd⟩ := Finite.exists_infinite_fiber (fun i => digit (term i))
  have hi : {i | digit (term i) = d}.Infinite := Set.infinite_coe_iff.mp hd
  refine ⟨Nat.nth (fun i => digit (term i) = d) (k - 1) + 1, ?_⟩
  simpa [Nat.sub_add_cancel hk] using emit_nth d hi (k - 1)

private theorem all_digits_infinite (d : Fin 9) : {i | digit (term i) = d}.Infinite := by
  have h := (digit_fiber_infinite d).preimage (f := term)
    (fun n hn => positive_in_range n hn.1)
  exact h.mono (fun _ hn => hn.2)

private theorem successor_bijOn (k : ℕ) (hk : 0 < k) :
    Set.BijOn (fun n => digit (term n)) {n | term (n + 1) = k} Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro m hm n hn he
    change digit (term m) = digit (term n) at he
    have hrm := term_recurrence m
    have hrn := term_recurrence n
    simp only [← he, Nat.count_succ, ite_true] at hrn
    rw [Nat.count_succ, if_pos rfl] at hrm
    apply Nat.count_injective (p := fun i => digit (term i) = digit (term m)) rfl he.symm
    change term (m + 1) = k at hm
    change term (n + 1) = k at hn
    omega
  · intro d _
    let n := Nat.nth (fun i => digit (term i) = d) (k - 1)
    refine ⟨n, ?_, Nat.nth_mem_of_infinite (all_digits_infinite d) (k - 1)⟩
    simpa [Nat.sub_add_cancel hk] using emit_nth d (all_digits_infinite d) (k - 1)

private theorem successor_multiplicity (k : ℕ) (hk : 0 < k) :
    {n | term (n + 1) = k}.Finite ∧ {n | term (n + 1) = k}.ncard = 9 := by
  have h := successor_bijOn k hk
  exact ⟨h.finite_iff_finite.mpr Set.finite_univ, by simpa using h.ncard_eq⟩

/-- A384309, indexed from 1. The unused index 0 has value 0. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => term n

/-- Number of positions j in 1,...,t whose term has leading digit d. -/
def counter (d t : ℕ) : ℕ := Nat.count (fun i => leading10 (a (i + 1)) = d) t

/-- Initial condition for the sequence. -/
theorem a_one : a 1 = 1 := rfl

/-- The current term is counted before the next term is read from its counter. -/
theorem a_recurrence (t : ℕ) (ht : 0 < t) :
    a (t + 1) = counter (leading10 (a t)) t := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  change term (n + 1) = Nat.count (fun i => leading10 (term i) = leading10 (term n)) (n + 1)
  have he : (fun i => digit (term i) = digit (term n)) =
      (fun i => leading10 (term i) = leading10 (term n)) := by
    funext i
    exact propext (digit_eq_iff (term_pos i) (term_pos n))
  simpa only [he] using term_recurrence n

/-- Every positive integer occurs at exactly nine positions, with one extra initial 1. -/
theorem leading_counter_multiplicity (k : ℕ) (hk : 0 < k) :
    {n | a n = k}.Finite ∧ {n | a n = k}.ncard = 9 + (if k = 1 then 1 else 0) := by
  obtain ⟨hs, hc⟩ := successor_multiplicity k hk
  let T : Set ℕ := (fun n => n + 2) '' {n | term (n + 1) = k}
  have hTf : T.Finite := hs.image _
  have hTc : T.ncard = 9 := by
    rw [Set.ncard_image_of_injective _ (by intro m n h; exact Nat.add_right_cancel h), hc]
  have h0 : 0 ∉ T := by rintro ⟨n, _, h⟩; change n + 2 = 0 at h; omega
  have h1 : 1 ∉ T := by rintro ⟨n, _, h⟩; change n + 2 = 1 at h; omega
  have hT (n : ℕ) : n + 2 ∈ T ↔ term (n + 1) = k := by simp [T]
  have he : {n | a n = k} = if k = 1 then insert 1 T else T := by
    ext n
    rcases n with _ | (_ | n)
    · by_cases h : k = 1 <;> simp [a, h, h0, hk.ne]
    · change (a 1 = k) ↔ _
      by_cases h : k = 1 <;> simp [a_one, h, h1, eq_comm]
    · have hne : n + 2 ≠ 1 := by omega
      by_cases h : k = 1 <;> simp [a, h, hne, hT, Nat.add_assoc]
  rw [he]
  by_cases h : k = 1
  · simp only [h, ite_true]
    exact ⟨hTf.insert 1, by rw [Set.ncard_insert_of_notMem h1 hTf, hTc]⟩
  · simp only [h, if_false, Nat.add_zero]
    exact ⟨hTf, hTc⟩

end D5.S3.Arith.CounterSequences.LeadingCounter
