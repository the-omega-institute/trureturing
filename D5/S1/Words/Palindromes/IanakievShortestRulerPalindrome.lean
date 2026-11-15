/- GID: D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/IanakievShortestRulerPalindrome
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.Padics.PadicVal.Basic]
   utility: none
   digest: Ianakiev's shortest-palindrome and first-occurrence laws for literal factorial runs. -/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Binary factorial plateaus and their shortest contiguous palindromes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome

noncomputable section

private theorem factorial_witness (m : ℕ) : ∃ h : ℕ, 1 ≤ h ∧ 2 ^ m ∣ h.factorial :=
  ⟨2 ^ m, by have := Nat.two_pow_pos m; omega,
    Nat.dvd_factorial (by positivity) le_rfl⟩

/-- A007843, including the positive factorial-index convention at exponent zero. -/
def F (m : ℕ) : ℕ := Nat.find (factorial_witness m)

private def V (h : ℕ) : ℕ := padicValNat 2 h.factorial

private theorem f_spec (m : ℕ) : 1 ≤ F m ∧ 2 ^ m ∣ (F m).factorial :=
  Nat.find_spec (factorial_witness m)

private theorem f_le_iff (m h : ℕ) (hh : 1 ≤ h) : F m ≤ h ↔ m ≤ V h := by
  constructor
  · intro hle
    exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero h)).mp
      (dvd_trans (f_spec m).2 (Nat.factorial_dvd_factorial hle))
  · intro hv
    exact Nat.find_min' (factorial_witness m)
      ⟨hh, (padicValNat_dvd_iff_le (Nat.factorial_ne_zero h)).mpr hv⟩

private theorem f_mono : Monotone F := by
  intro m n hmn
  apply (f_le_iff m (F n) (f_spec n).1).mpr
  have h := (f_le_iff n (F n) (f_spec n).1).mp le_rfl
  omega

private theorem f_zero : F 0 = 1 := by
  have hu := (f_le_iff 0 1 (by decide)).mpr (Nat.zero_le _)
  have hl := (f_spec 0).1
  omega

private theorem boundary_witness (a : ℕ) : ∃ m : ℕ, a < m ∧ F m ≠ F a := by
  have ha := (f_le_iff a (F a) (f_spec a).1).mp le_rfl
  refine ⟨V (F a) + 1, by omega, ?_⟩
  intro he
  have hh : F (V (F a) + 1) ≤ F a := by omega
  have := (f_le_iff _ _ (f_spec a).1).mp hh
  omega

private def nextBoundary (a : ℕ) : ℕ := Nat.find (boundary_witness a)

/-- Successive starts of the maximal constant runs of the literal sequence F. -/
def S : ℕ → ℕ
  | 0 => 0
  | r + 1 => nextBoundary (S r)

private theorem next_spec (a : ℕ) : a < nextBoundary a ∧ F (nextBoundary a) ≠ F a :=
  Nat.find_spec (boundary_witness a)

private theorem next_formula (a : ℕ) : nextBoundary a = V (F a) + 1 := by
  have ha := (f_le_iff a (F a) (f_spec a).1).mp le_rfl
  have hgt : ¬ F (V (F a) + 1) ≤ F a := by
    rw [f_le_iff _ _ (f_spec a).1]
    omega
  have hu : nextBoundary a ≤ V (F a) + 1 :=
    Nat.find_min' (boundary_witness a) ⟨by omega, by omega⟩
  have hn := next_spec a
  have hm := f_mono hn.1.le
  have hl : V (F a) < nextBoundary a := by
    by_contra h
    have hx := (f_le_iff (nextBoundary a) (F a) (f_spec a).1).mpr (by omega)
    omega
  omega

private theorem even_step (r : ℕ) :
    V (2 * (r + 1)) = 1 + padicValNat 2 (r + 1) + V (2 * r) := by
  have ho := padicValNat_factorial_mul_add (p := 2) (n := 1) r (by decide)
  have he : 2 * (r + 1) = (2 * r + 1) + 1 := by omega
  unfold V
  rw [he, Nat.factorial_succ,
    padicValNat.mul (by omega) (Nat.factorial_ne_zero _), ho]
  rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega,
    padicValNat.mul (by decide) (by omega), padicValNat_self]

private theorem f_after_even (r : ℕ) : F (V (2 * r) + 1) = 2 * (r + 1) := by
  have hv := even_step r
  have hu := (f_le_iff (V (2 * r) + 1) (2 * (r + 1)) (by omega)).mpr (by omega)
  have ho : V (2 * r + 1) = V (2 * r) :=
    padicValNat_factorial_mul_add (p := 2) (n := 1) r (by decide)
  have hl : ¬ F (V (2 * r) + 1) ≤ 2 * r + 1 := by
    rw [f_le_iff _ _ (by omega), ho]
    omega
  omega

private theorem boundaries (r : ℕ) :
    S (r + 1) = V (2 * r) + 1 ∧ F (S (r + 1)) = 2 * (r + 1) := by
  induction r with
  | zero =>
    have hs : S 1 = 1 := by
      change nextBoundary 0 = 1
      rw [next_formula, f_zero]
      simp [V]
    constructor
    · simpa [V] using hs
    · simpa [hs, V] using f_after_even 0
  | succ r ih =>
    have hs : S (r + 1 + 1) = V (2 * (r + 1)) + 1 := by
      change nextBoundary (S (r + 1)) = _
      rw [next_formula, ih.2]
    exact ⟨hs, hs ▸ f_after_even (r + 1)⟩

/-- The positive-indexed lengths of the actual constant runs of F. -/
def B (i : ℕ) : ℕ := S i - S (i - 1)

private theorem b_succ (r : ℕ) (hr : 0 < r) : B (r + 1) = 1 + padicValNat 2 r := by
  cases r with
  | zero => omega
  | succ r =>
    simp only [B, Nat.add_sub_cancel]
    rw [(boundaries (r + 1)).1, (boundaries r).1, even_step]
    omega

/-- Contiguous palindromes, with length admissibility imposed separately. -/
def Pal (i L : ℕ) : Prop := ∀ t : ℕ, t < L → B (i + t) = B (i + L - 1 - t)

private theorem odd_decomposition (a : ℕ) (ha : 0 < a) :
    ∃ u : ℕ, 0 < u ∧ u % 2 = 1 ∧ a = 2 ^ padicValNat 2 a * u := by
  obtain ⟨u, hu⟩ := (pow_padicValNat_dvd (p := 2) (n := a))
  have hu0 : 0 < u := by
    by_contra h
    have hz : u = 0 := by omega
    simp [hz] at hu
    omega
  have hodd : ¬ 2 ∣ u := by
    intro hd
    apply pow_succ_padicValNat_not_dvd (p := 2) ha.ne'
    obtain ⟨v, hv⟩ := hd
    refine ⟨v, ?_⟩
    calc
      a = 2 ^ padicValNat 2 a * u := hu
      _ = 2 ^ (padicValNat 2 a + 1) * v := by rw [hv, pow_succ]; ring
  exact ⟨u, hu0, by omega, hu⟩

private theorem endpoint_spacing (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hv : padicValNat 2 a = padicValNat 2 b) :
    2 ^ (padicValNat 2 a + 1) ≤ b - a := by
  obtain ⟨u, hu0, huodd, hu⟩ := odd_decomposition a ha
  obtain ⟨v, hv0, hvodd, hve⟩ := odd_decomposition b (by omega)
  rw [← hv] at hve
  have hq : 0 < 2 ^ padicValNat 2 a := by positivity
  have huv : u < v := by nlinarith
  have huv2 : u + 2 ≤ v := by omega
  rw [pow_succ]
  have : a + 2 ^ padicValNat 2 a * 2 ≤ b := by nlinarith
  omega

private theorem reflected_valuations (c s : ℕ) (hs : 0 < s) (hsc : s < c)
    (hv : padicValNat 2 s < padicValNat 2 c) :
    padicValNat 2 (c - s) = padicValNat 2 (c + s) := by
  have hsq : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast (lt_trans hs hsc).ne'
  have hvq : padicValRat 2 (s : ℚ) < padicValRat 2 (c : ℚ) := by
    simp only [padicValRat.of_nat]
    exact_mod_cast hv
  have hp := padicValRat.add_eq_of_lt (p := 2) (by positivity) hsq hcq hvq
  have hz : -(s : ℚ) + (c : ℚ) ≠ 0 := by
    have hlt : (s : ℚ) < c := by exact_mod_cast hsc
    linarith
  have hm := padicValRat.add_eq_of_lt (p := 2) hz (neg_ne_zero.mpr hsq) hcq
    (by simpa only [padicValRat.neg] using hvq)
  have he : -(s : ℚ) + (c : ℚ) = ((c - s : ℕ) : ℚ) := by
    rw [Nat.cast_sub hsc.le]
    ring
  rw [he, padicValRat.neg, padicValRat.of_nat, padicValRat.of_nat] at hm
  rw [add_comm, ← Nat.cast_add, padicValRat.of_nat, padicValRat.of_nat] at hp
  exact_mod_cast hm.trans hp.symm

private theorem palindrome_attainment (i : ℕ) (hi : 2 ≤ i) :
    Pal i (2 ^ (padicValNat 2 (i - 1) + 1) + 1) := by
  let j := i - 1
  let k := padicValNat 2 j
  let q := 2 ^ k
  have hj : 0 < j := by dsimp [j]; omega
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨u, hu0, huodd, hju⟩ := odd_decomposition j hj
  change j = q * u at hju
  let c := j + q
  have hqc : q < c := by dsimp [c]; omega
  have hcv : k + 1 ≤ padicValNat 2 c := by
    apply (padicValNat_dvd_iff_le (by dsimp [c]; omega : c ≠ 0)).mp
    have heven : 2 ∣ u + 1 := by omega
    obtain ⟨v, hv⟩ := heven
    refine ⟨v, ?_⟩
    change j + q = 2 ^ (k + 1) * v
    calc
      j + q = q * (u + 1) := by rw [hju]; ring
      _ = q * (2 * v) := by rw [hv]
      _ = 2 ^ (k + 1) * v := by dsimp [q]; rw [pow_succ]; ring
  have reflect (s : ℕ) (hs : s ≤ q) :
      padicValNat 2 (c - s) = padicValNat 2 (c + s) := by
    by_cases hz : s = 0
    · simp [hz]
    · have hs0 : 0 < s := by omega
      have hp := Nat.le_of_dvd hs0 (pow_padicValNat_dvd (p := 2) (n := s))
      have hvs : padicValNat 2 s ≤ k :=
        (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp (hp.trans hs)
      exact reflected_valuations c s hs0 (by omega) (by omega)
  have hlen : 2 ^ (k + 1) = 2 * q := by dsimp [q]; rw [pow_succ]; omega
  change Pal i (2 ^ (k + 1) + 1)
  rw [hlen]
  intro t ht
  have hleft : 0 < j + t := by omega
  have hright : 0 < j + 2 * q - t := by omega
  rw [show i + t = (j + t) + 1 by dsimp [j]; omega,
    b_succ _ hleft,
    show i + (2 * q + 1) - 1 - t = (j + 2 * q - t) + 1 by dsimp [j]; omega,
    b_succ _ hright]
  by_cases h : t ≤ q
  · have hh := reflect (q - t) (by omega)
    have hx : c - (q - t) = j + t := by dsimp [c]; omega
    have hy : c + (q - t) = j + 2 * q - t := by dsimp [c]; omega
    rw [hx, hy] at hh
    omega
  · have hh := reflect (t - q) (by omega)
    have hx : c - (t - q) = j + 2 * q - t := by dsimp [c]; omega
    have hy : c + (t - q) = j + t := by dsimp [c]; omega
    rw [hx, hy] at hh
    omega

private theorem palindrome_lower (i L : ℕ) (hi : 2 ≤ i) (hL : 2 ≤ L) (hp : Pal i L) :
    2 ^ (padicValNat 2 (i - 1) + 1) + 1 ≤ L := by
  have he := hp 0 (by omega)
  simp only [Nat.add_zero, Nat.sub_zero] at he
  rw [show i = (i - 1) + 1 by omega, b_succ _ (by omega)] at he
  rw [show i - 1 + 1 + L - 1 = (i + L - 2) + 1 by omega,
    b_succ _ (by omega)] at he
  have hv : padicValNat 2 (i - 1) = padicValNat 2 (i + L - 2) := by omega
  have hs := endpoint_spacing (i - 1) (i + L - 2) (by omega) (by omega) hv
  omega

private theorem palindrome_witness (i : ℕ) (hi : 2 ≤ i) :
    ∃ L : ℕ, 2 ≤ L ∧ Pal i L :=
  ⟨2 ^ (padicValNat 2 (i - 1) + 1) + 1,
    by have := Nat.two_pow_pos (padicValNat 2 (i - 1) + 1); omega,
    palindrome_attainment i hi⟩

/-- The stipulated first value, followed by the literal shortest-length minimum. -/
def P (i : ℕ) : ℕ := by
  classical
  exact if hi : 2 ≤ i then Nat.find (palindrome_witness i hi) else 1

private theorem p_spec (i : ℕ) (hi : 2 ≤ i) : 2 ≤ P i ∧ Pal i (P i) := by
  classical
  simpa only [P, dite_eq_left hi] using Nat.find_spec (palindrome_witness i hi)

private theorem p_formula (i : ℕ) (hi : 2 ≤ i) :
    P i = 2 ^ (padicValNat 2 (i - 1) + 1) + 1 := by
  classical
  apply le_antisymm
  · simp only [P, dite_eq_left hi]
    exact Nat.find_min' (palindrome_witness i hi)
      ⟨by have := Nat.two_pow_pos (padicValNat 2 (i - 1) + 1); omega,
        palindrome_attainment i hi⟩
  · exact palindrome_lower i (P i) hi (p_spec i hi).1 (p_spec i hi).2

private theorem p_one : P 1 = 1 := by simp [P]

/-- The present sequence A094373, at its original zero offset. -/
def A : ℕ → ℕ
  | 0 => 1
  | e + 1 => 2 ^ e + 1

/-- First appearance of a value in the positive-indexed sequence P. -/
def First (i : ℕ) : Prop := ∀ j : ℕ, 1 ≤ j → j < i → P j ≠ P i

private theorem first_one : First 1 := by intro j hj hlt; omega

private theorem first_power (e : ℕ) : First (2 ^ e + 1) := by
  have hq : 0 < 2 ^ e := by positivity
  have hval : P (2 ^ e + 1) = 2 ^ (e + 1) + 1 := by
    rw [p_formula _ (by omega), Nat.add_sub_cancel, padicValNat.prime_pow]
  intro j hj hjq he
  by_cases hj1 : j = 1
  · subst j
    rw [p_one, hval] at he
    have := Nat.two_pow_pos (e + 1)
    omega
  · rw [p_formula j (by omega), hval] at he
    have heq : 2 ^ (padicValNat 2 (j - 1) + 1) = 2 ^ (e + 1) := by omega
    have hv : padicValNat 2 (j - 1) = e := by
      have := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) heq
      omega
    have hd := pow_padicValNat_dvd (p := 2) (n := j - 1)
    rw [hv] at hd
    have := Nat.le_of_dvd (by omega : 0 < j - 1) hd
    omega

private theorem first_iff (i : ℕ) (hi : 1 ≤ i) : First i ↔ ∃ m : ℕ, i = A m := by
  constructor
  · intro hfirst
    by_cases hi1 : i = 1
    · exact ⟨0, hi1⟩
    · let e := padicValNat 2 (i - 1)
      have hq : 0 < 2 ^ e := by positivity
      have hle : 2 ^ e + 1 ≤ i := by
        have := Nat.le_of_dvd (by omega : 0 < i - 1)
          (pow_padicValNat_dvd (p := 2) (n := i - 1))
        dsimp [e] at *
        omega
      have heq : P (2 ^ e + 1) = P i := by
        rw [p_formula _ (by omega), Nat.add_sub_cancel, padicValNat.prime_pow,
          p_formula i (by omega)]
      have heqi : i = 2 ^ e + 1 := by
        by_contra hne
        exact hfirst (2 ^ e + 1) (by omega) (by omega) heq
      exact ⟨e + 1, heqi⟩
  · rintro ⟨m, rfl⟩
    cases m with
    | zero => exact first_one
    | succ e => exact first_power e

private theorem a_strict : StrictMono A := by
  apply strictMono_nat_of_lt_succ
  intro m
  cases m with
  | zero => norm_num [A]
  | succ e =>
    change 2 ^ e + 1 < 2 ^ (e + 1) + 1
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mpr (by omega : e < e + 1)
    omega

private theorem position_identity (m : ℕ) (hm : 2 ≤ m) : P (A (m - 1)) = A m := by
  cases m with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ e =>
      have hq : 0 < 2 ^ e := by positivity
      change P (2 ^ e + 1) = 2 ^ (e + 1) + 1
      rw [p_formula _ (by omega), Nat.add_sub_cancel, padicValNat.prime_pow]

/-- The full construction and both clauses of Ianakiev's A094373 conjecture. -/
def claim : Prop :=
  (∀ m : ℕ, IsLeast {h : ℕ | 1 ≤ h ∧ 2 ^ m ∣ h.factorial} (F m)) ∧
  S 0 = 0 ∧
  (∀ r : ℕ, IsLeast {m : ℕ | S r < m ∧ F m ≠ F (S r)} (S (r + 1))) ∧
  P 1 = 1 ∧
  (∀ i : ℕ, 2 ≤ i → IsLeast {L : ℕ | 2 ≤ L ∧ Pal i L} (P i)) ∧
  StrictMono A ∧
  (∀ i : ℕ, 1 ≤ i → (First i ↔ ∃ m : ℕ, i = A m)) ∧
  (∀ m : ℕ, 2 ≤ m → P (A (m - 1)) = A m)

/-- All minima exist; the full first-occurrence list and position identity hold. -/
theorem result : claim := by
  classical
  refine ⟨?_, rfl, ?_, p_one, ?_, a_strict, first_iff, position_identity⟩
  · intro m
    exact ⟨f_spec m, fun h hh => Nat.find_min' (factorial_witness m) hh⟩
  · intro r
    exact ⟨next_spec (S r), fun m hm => Nat.find_min' (boundary_witness (S r)) hm⟩
  · intro i hi
    refine ⟨p_spec i hi, ?_⟩
    intro L hL
    simp only [P, dite_eq_left hi]
    exact Nat.find_min' (palindrome_witness i hi) hL

#print axioms result

end

end D5.S1.Words.Palindromes.IanakievShortestRulerPalindrome
