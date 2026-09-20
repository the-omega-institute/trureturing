import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace AyadProbe

def reverseBase (B m : ℕ) : ℕ := Nat.ofDigits B (Nat.digits B m).reverse

def HasReverseMultipleProperty (B n : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → n ∣ m → n ∣ reverseBase B m

-- c indexes the positive coefficient c+1 of the preregistered construction.
def sparseWord (T : ℕ) : ℕ → List ℕ
  | 0 => [1, 1] ++ List.replicate (T - 2) 0 ++ [1]
  | c + 1 => sparseWord T c ++ List.replicate (T - 1) 0 ++ [1]

-- This is one substantive component of the intended witness, not a public API proposal.
theorem property_coprime {B n : ℕ} (hB : 2 ≤ B) (hn : 0 < n)
    (hp : HasReverseMultipleProperty B n) : Nat.Coprime n B := by
  have hb : 1 < B := by omega
  let p := B ^ n
  have hnp : n < p := lt_of_lt_of_le (Nat.lt_two_pow_self (n := n))
    (Nat.pow_le_pow_left hB n)
  let r := n - p % n
  have hr : r < p := lt_of_le_of_lt (Nat.sub_le _ _) hnp
  let L := Nat.digitsAppend B n r ++ [1]
  have hdigits : Nat.digits B (Nat.ofDigits B L) = L := by
    apply Nat.digits_ofDigits B hb
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact Nat.lt_of_mem_digitsAppend hb n d hd
      · simp only [List.mem_singleton] at hd
        omega
    · intro h
      simp [L]
  have hvalue : Nat.ofDigits B L = r + p := by
    change Nat.ofDigits B (Nat.digitsAppend B n r ++ [1]) = r + p
    rw [Nat.ofDigits_append, Nat.length_digitsAppend hb n hr, Nat.ofDigits_singleton,
      mul_one]
    simp [Nat.digitsAppend, Nat.ofDigits_digits, p]
  have hdiv : n ∣ Nat.ofDigits B L := by
    rw [hvalue]
    refine ⟨p / n + 1, ?_⟩
    have hmod := Nat.mod_add_div p n
    have hlt := Nat.mod_lt p hn
    dsimp [r]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hpos : 0 < Nat.ofDigits B L := by rw [hvalue]; omega
  have hreversed := hp _ hpos hdiv
  have heq : reverseBase B (Nat.ofDigits B L) =
      1 + B * Nat.ofDigits B (Nat.digitsAppend B n r).reverse := by
    simp [reverseBase, hdigits, L, List.reverse_append, Nat.ofDigits]
  rw [heq] at hreversed
  have hd : n.gcd B ∣ 1 + B * Nat.ofDigits B (Nat.digitsAppend B n r).reverse :=
    dvd_trans (Nat.gcd_dvd_left n B) hreversed
  have hdB : n.gcd B ∣ B * Nat.ofDigits B (Nat.digitsAppend B n r).reverse :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_right n B) _
  have hone : n.gcd B ∣ 1 := by
    exact (Nat.dvd_add_iff_left hdB).mpr hd
  exact Nat.dvd_one.mp hone

-- The list has actual positive coefficient c+1; no bounded numeral is expanded.
theorem sparse_spec {B T n : ℕ} (hB : 2 ≤ B) (hT : 2 ≤ T)
    (hperiod : (B : ZMod n) ^ T = 1) (c : ℕ) :
    Nat.digits B (Nat.ofDigits B (sparseWord T c)) = sparseWord T c ∧
    0 < Nat.ofDigits B (sparseWord T c) ∧
    ((Nat.ofDigits B (sparseWord T c) : ℕ) : ZMod n) = 1 + B + (c + 1 : ℕ) ∧
    (B : ZMod n) * ((Nat.ofDigits B (sparseWord T c).reverse : ℕ) : ZMod n) =
      1 + B + (c + 1 : ℕ) * (B : ZMod n) := by
  have hlen : ∀ c, (sparseWord T c).length = (c + 1) * T + 1 := by
    intro c
    induction c with
    | zero => simp [sparseWord]; omega
    | succ c ih =>
      simp only [sparseWord, List.length_append, List.length_replicate,
        List.length_singleton, ih, Nat.add_mul, Nat.one_mul]
      omega
  have hsmall : ∀ c, ∀ d ∈ sparseWord T c, d < B := by
    intro c
    induction c with
    | zero =>
      intro d hd
      simp only [sparseWord, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, List.mem_replicate] at hd
      rcases hd with ((rfl | rfl) | ⟨_, rfl⟩) | rfl <;> omega
    | succ c ih =>
      intro d hd
      simp only [sparseWord, List.mem_append, List.mem_singleton,
        List.mem_replicate] at hd
      rcases hd with (hd | ⟨_, rfl⟩) | rfl
      · exact ih d hd
      · omega
      · omega
  have hdigits : Nat.digits B (Nat.ofDigits B (sparseWord T c)) = sparseWord T c := by
    apply Nat.digits_ofDigits B (by omega) _ (hsmall c)
    intro h
    cases c <;> simp [sparseWord]
  refine ⟨hdigits, ?_, ?_⟩
  · have hne : sparseWord T c ≠ [] := by
      intro heq
      have := hlen c
      simp [heq] at this
    have := (Nat.digits_ne_nil_iff_ne_zero).mp (hdigits ▸ hne)
    omega
  · clear hdigits
    induction c with
    | zero =>
      have hpred2 : (B : ZMod n)^2 * (B : ZMod n)^(T - 2) = 1 := by
        rw [← pow_add, show 2 + (T - 2) = T by omega, hperiod]
      constructor
      · simp only [sparseWord, Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
          List.length_append, List.length_cons, List.length_nil,
          List.length_replicate, Nat.ofDigits_cons, Nat.ofDigits_nil]
        have he : 1 + (1 + 0) + (T - 2) = T := by omega
        simp only [he, Nat.cast_add, Nat.cast_pow,
          Nat.cast_one, mul_zero, add_zero, mul_one, zero_add, hperiod]
      · simp only [sparseWord, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.reverse_replicate, List.nil_append,
          Nat.ofDigits_append, Nat.ofDigits_singleton, Nat.ofDigits_replicate_zero,
          List.length_cons, List.length_nil, List.length_replicate]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_one, mul_one, zero_add]
        linear_combination (1 + (B : ZMod n)) * hpred2
    | succ c ih =>
      have hpow : (B : ZMod n) ^ ((c + 1) * T + 1 + (T - 1)) = 1 := by
        have he : (c + 1) * T + 1 + (T - 1) = T * (c + 2) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_two, Nat.mul_comm c T]
          omega
        rw [he, pow_mul, hperiod, one_pow]
      constructor
      · simp only [sparseWord, Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
          Nat.ofDigits_singleton, List.length_append, List.length_replicate,
          hlen, mul_zero, add_zero, mul_one, Nat.cast_add, Nat.cast_pow,
          hpow, ih.1, Nat.cast_succ]
        ring
      · simp only [sparseWord, List.reverse_append, List.reverse_replicate,
          List.reverse_cons, List.reverse_nil, List.nil_append,
          Nat.ofDigits_append, Nat.ofDigits_singleton, Nat.ofDigits_replicate_zero,
          List.length_singleton, List.length_replicate,
          Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
        have hpred : (B : ZMod n) * (B : ZMod n) ^ (T - 1) = 1 := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega), hperiod]
        simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
        linear_combination (B : ZMod n) *
          ((Nat.ofDigits B (sparseWord T c).reverse : ℕ) : ZMod n) * hpred + ih.2

-- Exact preregistered witness target, with no proof holes.
theorem witness {B n : ℕ} (hB : 2 ≤ B) (hn : 0 < n)
    (hbad : ¬ n ∣ B ^ 2 - 1) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m ∧ ¬ n ∣ reverseBase B m := by
  classical
  by_contra hnone
  have hp : HasReverseMultipleProperty B n := by
    intro m hm hnm
    by_contra hnr
    exact hnone ⟨m, hm, hnm, hnr⟩
  have hcop := property_coprime hB hn hp
  let : NeZero n := ⟨by omega⟩
  have hbadmod : (B : ZMod n)^2 ≠ 1 := by
    intro heq
    apply hbad
    apply (ZMod.natCast_eq_zero_iff (B^2 - 1) n).mp
    rw [Nat.cast_sub (Nat.one_le_pow 2 B (by omega)), Nat.cast_pow,
      Nat.cast_one, heq, sub_self]
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime B n).mpr hcop.symm
  have hperiod : (B : ZMod n)^(orderOf u) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, hu] using
      congrArg (fun v : (ZMod n)ˣ => (v : ZMod n)) (pow_orderOf_eq_one u)
  have hT : 2 ≤ orderOf u := by
    have hpos := orderOf_pos u
    by_contra hsmall
    have hone : orderOf u = 1 := by omega
    have hbone : (B : ZMod n) = 1 := by simpa [hone] using hperiod
    exact hbadmod (by simp [hbone])
  let c := (-(2 + (B : ZMod n))).val
  have hc : (c : ZMod n) = -(2 + (B : ZMod n)) := ZMod.natCast_zmod_val _
  obtain ⟨hdigits, hpos, hforward, hreverse⟩ := sparse_spec hB hT hperiod c
  have hdiv : n ∣ Nat.ofDigits B (sparseWord (orderOf u) c) := by
    apply (ZMod.natCast_eq_zero_iff _ n).mp
    rw [hforward]
    simp only [Nat.cast_add, Nat.cast_one, hc]
    ring
  have hz := (ZMod.natCast_eq_zero_iff _ n).mpr (hp _ hpos hdiv)
  dsimp only [reverseBase] at hz
  rw [hdigits] at hz
  rw [hz, mul_zero] at hreverse
  apply hbadmod
  simp only [Nat.cast_add, Nat.cast_one, hc] at hreverse
  linear_combination hreverse

-- The exact externally preregistered theorem, with all quantifiers preserved.
theorem result : ∀ B : ℕ, 2 ≤ B → ∀ n : ℕ, 0 < n →
    (HasReverseMultipleProperty B n ↔ n ∣ B ^ 2 - 1) := by
  intro B hB n hn
  constructor
  · intro hp
    by_contra hbad
    obtain ⟨m, hm, hnm, hnr⟩ := witness hB hn hbad
    exact hnr (hp m hm hnm)
  · intro hdiv m _hm hnm
    have hsq : (B : ZMod n)^2 = 1 := by
      have hz := (ZMod.natCast_eq_zero_iff (B^2 - 1) n).mpr hdiv
      rw [Nat.cast_sub (Nat.one_le_pow 2 B (by omega)), Nat.cast_pow,
        Nat.cast_one, sub_eq_zero] at hz
      exact hz
    have hlist : ∀ L : List ℕ,
        (B : ZMod n) * ((Nat.ofDigits B L.reverse : ℕ) : ZMod n) =
        (B : ZMod n)^L.length * ((Nat.ofDigits B L : ℕ) : ZMod n) := by
      intro L
      induction L with
      | nil => simp [Nat.ofDigits]
      | cons d L ih =>
        rw [Nat.ofDigits_reverse_cons, Nat.ofDigits_cons]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, List.length_cons, pow_succ]
        linear_combination ih -
          (B : ZMod n)^L.length * ((Nat.ofDigits B L : ℕ) : ZMod n) * hsq
    have hz := hlist (Nat.digits B m)
    rw [Nat.ofDigits_digits, (ZMod.natCast_eq_zero_iff m n).mpr hnm, mul_zero] at hz
    apply (ZMod.natCast_eq_zero_iff (reverseBase B m) n).mp
    have hmul := congrArg (fun z : ZMod n => (B : ZMod n) * z) hz
    have hBB : (B : ZMod n) * B = 1 := by simpa only [pow_two] using hsq
    simpa only [← mul_assoc, hBB, one_mul, mul_zero, reverseBase] using hmul

#print axioms property_coprime
#print axioms sparse_spec
#print axioms witness
#print axioms result

end AyadProbe
