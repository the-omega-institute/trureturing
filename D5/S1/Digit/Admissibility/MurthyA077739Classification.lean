/- GID: D5/S1/Digit/Admissibility/MurthyA077739Classification
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/MurthyA077739Classification
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S1/Digit/Admissibility/MurthyA077739Classification.result; instance=D5/S1/Digit/Admissibility/MurthyA077739Classification.certificateData; result=D5/S1/Digit/Admissibility/MurthyA077739Classification.result
   digest: The complete unbounded existence and least-or-zero classification for Murthy A077739. -/
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

/-! Decimal blocks and the exact unbounded source predicate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.Admissibility.MurthyA077739Classification

/-- Usual decimal digit sum. -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- Number of decimal digits; zero has the empty expansion. -/
def width (n : ℕ) : ℕ := (Nat.digits 10 n).length

/-- Arithmetic positional prefix, including the empty appended block. -/
def Begins (n N : ℕ) : Prop :=
  ∃ k r : ℕ, r < 10 ^ k ∧ N = n * 10 ^ k + r

/-- Both prescribed ends may overlap. The modulus uses the full width of n. -/
def Witness (n N : ℕ) : Prop :=
  0 < N ∧ n ∣ N ∧ digitSum N = n ∧ Begins n N ∧ N % 10 ^ width n = n

/-- The exact unbounded existence predicate in OEIS A077739. -/
def Admissible (n : ℕ) : Prop := ∃ N : ℕ, Witness n N

/-- Least positive witness, or zero when there is none. -/
noncomputable def a (n : ℕ) : ℕ := sInf {N : ℕ | Witness n N}

/-- Whole source assertion, with no bound on the witness or its length. -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n = 11 ∨ n = 17 ∨ n = 19)

private theorem sum_step (n : ℕ) : digitSum n = n % 10 + digitSum (n / 10) := by
  by_cases hn : n = 0
  · simp [hn, digitSum]
  · simpa [digitSum] using congrArg List.sum
      (Nat.digits_def' (by norm_num : 1 < 10) (Nat.pos_of_ne_zero hn))

private theorem sum_cons (q r : ℕ) (hr : r < 10) :
    digitSum (10 * q + r) = r + digitSum q := by
  rw [sum_step]
  simp [Nat.add_mod, Nat.add_div, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr,
    Nat.not_le_of_gt hr]

private theorem sum_add_shift (L x y : ℕ) (hx : x < 10 ^ L) :
    digitSum (x + 10 ^ L * y) = digitSum x + digitSum y := by
  induction L generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    simp [this, digitSum]
  | succ L ih =>
    have hq : x / 10 < 10 ^ L := by
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)).2
      simpa [pow_succ] using hx
    have he : x + 10 ^ (L + 1) * y =
        10 * (x / 10 + 10 ^ L * y) + x % 10 := by
      have := Nat.mod_add_div x 10
      rw [pow_succ]
      nlinarith
    rw [he, sum_cons _ _ (Nat.mod_lt _ (by norm_num)), ih _ hq, sum_step x]
    omega

private theorem sum_complement (L x : ℕ) (hx : x < 10 ^ L) :
    digitSum x + digitSum (10 ^ L - 1 - x) = 9 * L := by
  induction L generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    simp [this, digitSum]
  | succ L ih =>
    have hq : x / 10 < 10 ^ L := by
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)).2
      simpa [pow_succ] using hx
    have hr := Nat.mod_lt x (by norm_num : 0 < 10)
    have hp : 0 < 10 ^ L := by positivity
    have he : 10 ^ (L + 1) - 1 - x =
        10 * (10 ^ L - 1 - x / 10) + (9 - x % 10) := by
      have := Nat.mod_add_div x 10
      rw [pow_succ]
      omega
    rw [he, sum_cons _ _ (by omega), sum_step x]
    have := ih (x / 10) hq
    omega

private theorem sum_multiple_nines (n L : ℕ) (hn : 0 < n) (hL : n ≤ 10 ^ L) :
    digitSum (n * (10 ^ L - 1)) = 9 * L := by
  have hp : 0 < 10 ^ L := by positivity
  have he : n * (10 ^ L - 1) = (10 ^ L - n) + 10 ^ L * (n - 1) := by
    have := Nat.sub_add_cancel (show 1 ≤ n by omega)
    have := Nat.sub_add_cancel (show 1 ≤ 10 ^ L by omega)
    have := Nat.sub_add_cancel hL
    nlinarith
  rw [he, sum_add_shift _ _ _ (by omega)]
  have hc := sum_complement L (n - 1) (by omega)
  have : 10 ^ L - 1 - (n - 1) = 10 ^ L - n := by omega
  rw [this] at hc
  omega

/-- Decimal concatenation. A zero second operand contributes no digits. -/
def concat (x y : ℕ) : ℕ := x * 10 ^ width y + y

private theorem sum_concat (x y : ℕ) :
    digitSum (concat x y) = digitSum x + digitSum y := by
  simpa [concat, Nat.add_comm, Nat.mul_comm] using
    sum_add_shift (width y) y x (Nat.lt_base_pow_length_digits (by norm_num))

private theorem begins_concat {n x : ℕ} (h : Begins n x) (y : ℕ) :
    Begins n (concat x y) := by
  obtain ⟨k, r, hr, rfl⟩ := h
  refine ⟨k + width y, r * 10 ^ width y + y, ?_, ?_⟩
  · have hy : y < 10 ^ width y := Nat.lt_base_pow_length_digits (by norm_num)
    rw [pow_add]
    nlinarith
  · simp [concat, pow_add]
    ring

private theorem begins_self (n : ℕ) : Begins n n := by
  exact ⟨0, 0, by norm_num, by simp⟩

private theorem dvd_concat {n x y : ℕ} (hx : n ∣ x) (hy : n ∣ y) :
    n ∣ concat x y := dvd_add (dvd_mul_of_dvd_left hx _) hy

/-- Well-ordering is the bridge from existence to the source's least-or-zero sequence. -/
private theorem a_zero_iff (n : ℕ) : a n = 0 ↔ ¬ Admissible n := by
  classical
  constructor
  · intro hz ⟨N, hN⟩
    have hmem := Nat.sInf_mem (s := {N : ℕ | Witness n N}) ⟨N, hN⟩
    change Witness n (a n) at hmem
    have hp := hmem.1
    omega
  · intro h
    apply Nat.sInf_eq_zero.mpr
    right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro N hN
    exact h ⟨N, hN⟩


private def extend (x : ℕ) : List ℕ → ℕ
  | [] => x
  | y :: ys => extend (concat x y) ys

private theorem extend_properties (n x : ℕ) (bs : List ℕ)
    (hx : 0 < x) (hd : n ∣ x) (hp : Begins n x)
    (hb : ∀ y ∈ bs, n ∣ y) :
    0 < extend x bs ∧ n ∣ extend x bs ∧ Begins n (extend x bs) ∧
      digitSum (extend x bs) = digitSum x + (bs.map digitSum).sum := by
  induction bs generalizing x with
  | nil =>
    change 0 < x ∧ n ∣ x ∧ Begins n x ∧ digitSum x = digitSum x + 0
    exact ⟨hx, hd, hp, by omega⟩
  | cons y ys ih =>
    have hpos : 0 < concat x y := by
      have : 0 < 10 ^ width y := by positivity
      dsimp [concat]
      positivity
    obtain ⟨h1,h2,h3,h4⟩ := ih (concat x y) hpos
      (dvd_concat hd (hb y (by simp))) (begins_concat hp y)
      (fun z hz => hb z (by simp [hz]))
    exact ⟨h1,h2,h3,by simpa [extend, sum_concat, Nat.add_assoc] using h4⟩

private theorem from_blocks (n : ℕ) (hn : 0 < n) (bs : List ℕ)
    (hb : ∀ y ∈ bs, n ∣ y)
    (hs : 2 * digitSum n + (bs.map digitSum).sum = n) : Admissible n := by
  obtain ⟨h1,h2,h3,h4⟩ := extend_properties n n bs hn (dvd_refl n) (begins_self n) hb
  refine ⟨concat (extend n bs) n, ?_⟩
  refine ⟨?_, dvd_concat h2 (dvd_refl n), ?_, begins_concat h3 n, ?_⟩
  · dsimp [concat]
    omega
  · rw [sum_concat, h4]
    omega
  · simp [concat, Nat.add_mod,
      Nat.mod_eq_of_lt (show n < 10 ^ width n from Nat.lt_base_pow_length_digits (by norm_num))]


private theorem digit_sum_width (n : ℕ) : digitSum n ≤ 9 * width n := by
  have h : ∀ xs : List ℕ, (∀ x ∈ xs, x < 10) → xs.sum ≤ 9 * xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro hx
      have hx0 := hx x (by simp)
      have hh := ih (fun y hy => hx y (by simp [hy]))
      simp only [List.sum_cons, List.length_cons]
      omega
  exact h _ (fun x hx => Nat.digits_lt_base (by norm_num) hx)

private theorem polynomial_bound (k : ℕ) :
    9 * (k + 4) ^ 2 + 81 * (k + 4) ≤ 10 ^ (k + 3) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hh := Nat.mul_le_mul_left 10 ih
    rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ 10]
    nlinarith

private theorem tail_parameters (n : ℕ) (hn : 1000 ≤ n) :
    ∃ d a b : ℕ, n < 10 ^ d ∧
      10 * digitSum n + 9 * (a * d + b * (d + 1)) = n := by
  let d := width n
  have hlarge : 4 ≤ d := by
    by_contra h
    have hd : d ≤ 3 := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 10) hd
    have hlt : n < 10 ^ d := Nat.lt_base_pow_length_digits (by norm_num)
    norm_num at hpow
    omega
  have hpow := Nat.base_pow_length_digits_le 10 n (by norm_num) (by omega)
  change 10 ^ d ≤ 10 * n at hpow
  have he : d = (d - 4) + 4 := by omega
  have hb := polynomial_bound (d - 4)
  have hde : d = (d - 4 + 3) + 1 := by omega
  rw [← he] at hb
  rw [hde, pow_succ] at hpow
  have hpoly : 9 * d ^ 2 + 81 * d ≤ n := by nlinarith
  have hs := digit_sum_width n
  change digitSum n ≤ 9 * d at hs
  have hten : 10 * digitSum n ≤ n := by nlinarith
  have hmod := Nat.modEq_nine_digits_sum n
  change n % 9 = digitSum n % 9 at hmod
  have hdiv : 9 ∣ n - 10 * digitSum n := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let q := (n - 10 * digitSum n) / 9
  have hq : 9 * q = n - 10 * digitSum n := Nat.mul_div_cancel' hdiv
  have hsubn := Nat.sub_add_cancel hten
  have hqmin : d * (d - 1) ≤ q := by
    have hdsub : d - 1 + 1 = d := by omega
    nlinarith
  let b := q % d
  let a := q / d - b
  have hdp : 0 < d := by omega
  have hblt : b < d := Nat.mod_lt q hdp
  have hquot : d - 1 ≤ q / d := (Nat.le_div_iff_mul_le hdp).2 (by nlinarith)
  have hab : b ≤ q / d := by omega
  have hrem : b + d * (q / d) = q := Nat.mod_add_div q d
  refine ⟨d, a, b, Nat.lt_base_pow_length_digits (by norm_num), ?_⟩
  dsimp [a]
  have hsub := Nat.sub_add_cancel hab
  nlinarith

/-- Every index at least one thousand has a witness, without a length bound. -/
private theorem admissible_tail (n : ℕ) (hn : 1000 ≤ n) : Admissible n := by
  obtain ⟨d,a,b,hd,hs⟩ := tail_parameters n hn
  let B := n * (10 ^ d - 1)
  let C := n * (10 ^ (d + 1) - 1)
  let bs := List.replicate 8 n ++ List.replicate a B ++ List.replicate b C
  apply from_blocks n (by omega) bs
  · intro y hy
    simp only [bs, List.mem_append, List.mem_replicate] at hy
    rcases hy with (⟨_,hy⟩ | ⟨_,hy⟩) | ⟨_,hy⟩
    · simpa only [← hy] using dvd_refl n
    · rw [hy]
      exact dvd_mul_right n _
    · rw [hy]
      exact dvd_mul_right n _
  · have hB : digitSum B = 9 * d := sum_multiple_nines n d (by omega) (by omega)
    have hC : digitSum C = 9 * (d + 1) := by
      apply sum_multiple_nines n (d + 1) (by omega)
      have := Nat.pow_le_pow_right (by norm_num : 0 < 10) (show d ≤ d+1 by omega)
      omega
    simp only [bs, List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, smul_eq_mul, hB, hC]
    nlinarith


private theorem sum_zero (n : ℕ) : digitSum n = 0 ↔ n = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn, digitSum]
    have hq := ih (n / 10) (Nat.div_lt_self (by omega) (by norm_num))
    rw [sum_step]
    have := Nat.mod_add_div n 10
    constructor
    · intro h
      have hzero : n / 10 = 0 := hq.mp (by omega)
      omega
    · intro h
      contradiction

private theorem sum_one (n : ℕ) (hn : digitSum n = 1) : ∃ j : ℕ, n = 10 ^ j := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hpos : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      simp [this, digitSum] at hn
    have hstep := sum_step n
    by_cases hq : n / 10 = 0
    · have : n = 1 := by
        rw [hq, show digitSum 0 = 0 from rfl] at hstep
        have := Nat.mod_add_div n 10
        omega
      exact ⟨0, by simpa⟩
    · have hsumpos : 0 < digitSum (n / 10) := by
        have := sum_zero (n / 10)
        omega
      have hsum : digitSum (n / 10) = 1 := by omega
      obtain ⟨j,hj⟩ := ih _ (Nat.div_lt_self hpos (by norm_num)) hsum
      refine ⟨j+1, ?_⟩
      have := Nat.mod_add_div n 10
      rw [pow_succ]
      omega

private theorem signed_digits_bound (xs : List ℕ) :
    -(xs.sum : ℤ) ≤ Nat.ofDigits (-1 : ℤ) xs ∧
      Nat.ofDigits (-1 : ℤ) xs ≤ (xs.sum : ℤ) ∧
      Nat.ofDigits (-1 : ℤ) xs % 2 = (xs.sum : ℤ) % 2 := by
  induction xs with
  | nil => simp [Nat.ofDigits]
  | cons x xs ih =>
    simp only [Nat.ofDigits, List.sum_cons, Nat.cast_add, neg_one_mul]
    omega

/-- The suffix 11 already prevents digit sum 11 for a multiple of 11. -/
private theorem not_admissible_eleven : ¬ Admissible 11 := by
  rintro ⟨N, hpos, hd, hs, hp, ht⟩
  change N % 100 = 11 at ht
  let q := N / 100
  have he : N = 11 + 100 * q := by have := Nat.mod_add_div N 100; omega
  have hsum := sum_add_shift 2 11 q (by norm_num)
  change digitSum (11 + 100 * q) = digitSum 11 + digitSum q at hsum
  rw [← he, hs, show digitSum 11 = 2 by decide] at hsum
  have hqd : 11 ∣ q := by omega
  have ha : (11 : ℤ) ∣ Nat.ofDigits (-1 : ℤ) (Nat.digits 10 q) :=
    (Nat.dvd_iff_dvd_ofDigits 11 10 (-1) (by norm_num) q).mp hqd
  obtain ⟨z,hz⟩ := ha
  have hb := signed_digits_bound (Nat.digits 10 q)
  change -(digitSum q : ℤ) ≤ _ ∧ _ ≤ (digitSum q : ℤ) ∧ _ = (digitSum q : ℤ) % 2 at hb
  have hsq : digitSum q = 9 := by omega
  rw [hsq] at hb
  omega

private theorem two_end_decomposition (n N : ℕ) (hn : n = 17 ∨ n = 19)
    (hs : digitSum N = n) (hp : Begins n N) (ht : N % 100 = n) :
    ∃ k M : ℕ, N = n * 10 ^ (k+2) + M * 100 + n ∧
      digitSum N = 2 * digitSum n + digitSum M := by
  obtain ⟨k,r,hr,he⟩ := hp
  have hk : 2 ≤ k := by
    by_contra hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · norm_num at hr
      have : r = 0 := by omega
      subst r
      simp only [pow_zero, mul_one, add_zero] at he
      subst N
      rcases hn with rfl | rfl <;>
        norm_num [show digitSum 17 = 8 by decide, show digitSum 19 = 10 by decide] at hs
    · norm_num at hr he
      rcases hn with rfl | rfl <;> omega
  obtain ⟨l,hl⟩ := Nat.exists_eq_add_of_le hk
  have hpow : 10 ^ k = 100 * 10 ^ l := by rw [hl, pow_add]; ring
  have hrmod : r % 100 = n := by
    rw [he, hpow, show n * (100 * 10 ^ l) = 100 * (n * 10 ^ l) by ring] at ht
    simpa [Nat.add_mod] using ht
  let M := r / 100
  have hr' : r = M * 100 + n := by have := Nat.mod_add_div r 100; omega
  refine ⟨l,M,?_,?_⟩
  · rw [he, hpow, hr']
    rw [pow_add]
    ring
  · have hn100 : n < 100 := by omega
    have hh := sum_add_shift k r n hr
    have hh' := sum_add_shift 2 n M (by simpa using hn100)
    rw [he, show n * 10 ^ k + r = r + 10 ^ k * n by ring, hh]
    rw [hr', show M * 100 + n = n + 10 ^ 2 * M by ring, hh']
    omega

/-- The two disjoint ends have digit sum twenty; overlap cannot give a witness. -/
private theorem not_admissible_nineteen : ¬ Admissible 19 := by
  rintro ⟨N,hpos,hd,hs,hp,ht⟩
  change N % 100 = 19 at ht
  obtain ⟨k,M,he,hs'⟩ := two_end_decomposition 19 N (Or.inr rfl) hs hp ht
  rw [hs, show digitSum 19 = 10 by decide] at hs'
  omega

/-- A remaining digit sum of one is a power of ten, which cannot be divisible by 17. -/
private theorem not_admissible_seventeen : ¬ Admissible 17 := by
  rintro ⟨N,hpos,hd,hs,hp,ht⟩
  change N % 100 = 17 at ht
  obtain ⟨k,M,he,hs'⟩ := two_end_decomposition 17 N (Or.inl rfl) hs hp ht
  have hM : digitSum M = 1 := by rw [hs, show digitSum 17 = 8 by decide] at hs'; omega
  obtain ⟨j,hj⟩ := sum_one M hM
  have hdM : 17 ∣ M * 100 := by rw [he] at hd; omega
  have hcop : Nat.Coprime 17 100 := by decide
  have hMd : 17 ∣ M := hcop.dvd_mul_right.mp hdM
  rw [hj] at hMd
  have hprime : Nat.Prime 17 := by norm_num
  have : 17 ∣ 10 := hprime.dvd_of_dvd_pow hMd
  norm_num at this

private def certificateData : Array (List (ℕ × ℕ)) := #[
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(1, 8)],
  [],
  [(1, 2)],
  [(8, 1)],
  [(8, 1)],
  [(2, 1)],
  [(125, 1)],
  [],
  [],
  [],
  [(5, 16)],
  [(1, 5)],
  [(5, 7)],
  [(44, 1), (87, 3)],
  [(5, 4)],
  [(4, 11)],
  [(5, 1), (12, 1)],
  [(1, 1)],
  [(5, 1), (75, 1)],
  [(38, 1), (69, 1)],
  [(1, 8)],
  [(1, 4), (4, 1)],
  [(35, 4), (66, 1)],
  [(1, 1), (13, 1)],
  [(3, 5), (65, 1)],
  [(6, 5), (32, 1)],
  [(1, 2)],
  [(2, 1), (3, 2)],
  [(29, 4)],
  [(3, 1), (8, 1)],
  [(25, 32)],
  [(1, 5), (3, 1)],
  [(5, 10)],
  [(7, 6), (47, 1)],
  [(25, 14)],
  [(1, 3)],
  [(22, 5), (24, 1)],
  [(43, 5)],
  [(25, 8)],
  [(9, 1), (49, 2)],
  [(2, 40)],
  [(2, 13)],
  [(6, 1), (25, 8)],
  [(2, 1), (4, 6)],
  [(1, 4)],
  [(2, 12), (11, 1)],
  [(2, 7), (75, 1)],
  [(193, 11)],
  [(19, 8)],
  [(17, 6), (68, 1)],
  [(2, 16)],
  [(1, 1), (2, 8)],
  [(5, 10), (21, 1)],
  [(1, 5)],
  [(175, 11)],
  [(16, 1), (154, 19)],
  [(2, 7)],
  [(2, 1), (3, 11)],
  [(5, 1), (15, 11)],
  [(29, 13)],
  [(143, 28)],
  [(2, 1), (141, 16)],
  [(1, 6)],
  [(14, 1), (137, 24)],
  [(5, 1), (15, 14)],
  [(4, 17)],
  [(15, 1), (145, 11)],
  [(4, 1), (13, 19)],
  [(4, 8)],
  [(19, 1), (38, 8)],
  [(125, 64)],
  [(1, 7)],
  [(5, 11), (16, 1)],
  [(17, 1), (147, 9)],
  [(25, 20)],
  [(12, 18), (26, 1)],
  [(12, 1), (35, 13)],
  [(23, 19)],
  [(125, 28)],
  [(3, 1), (118, 5)],
  [(1, 8)],
  [(11, 34), (111, 1)],
  [(11, 16), (12, 1)],
  [(11, 10), (12, 1)],
  [(11, 1), (15, 10)],
  [(14, 1), (116, 15)],
  [(125, 22)],
  [(26, 1), (33, 9)],
  [(145, 8)],
  [(1, 2), (111, 1)],
  [(1, 98)],
  [(1, 43), (109, 1)],
  [(1, 32)],
  [(1, 22), (4, 1)],
  [(3, 1), (125, 22)],
  [(2, 31)],
  [(1, 1), (2, 17)],
  [(3, 1), (103, 17)],
  [(1, 10)],
  [(8, 1), (189, 8)],
  [(1, 53)],
  [(1, 35)],
  [(1, 26)],
  [(1, 2), (177, 31)],
  [(1, 17)],
  [(2, 1), (174, 32)],
  [(95, 25)],
  [(1, 11)],
  [(85, 23), (195, 1)],
  [(17, 1), (169, 18)],
  [(1, 38)],
  [(1, 25), (172, 1)],
  [(1, 21), (5, 1)],
  [(1, 17), (9, 1)],
  [(25, 26), (105, 1)],
  [(8, 109)],
  [(1, 12)],
  [(9, 1), (16, 14)],
  [(25, 20), (165, 1)],
  [(8, 16), (9, 1)],
  [(77, 61)],
  [(1, 23), (84, 1)],
  [(1, 20)],
  [(1, 17)],
  [(15, 37), (83, 1)],
  [(1, 13)],
  [(17, 1), (75, 36)],
  [(9, 1), (73, 53)],
  [(145, 38)],
  [(8, 21), (29, 1)],
  [(8, 1), (15, 42)],
  [(71, 43)],
  [(5, 1), (155, 24)],
  [(7, 58), (142, 1)],
  [(1, 14)],
  [(14, 1), (138, 40)],
  [(137, 31)],
  [(3, 1), (83, 19)],
  [(5, 1), (75, 37)],
  [(9, 1), (68, 16)],
  [(2, 46)],
  [(1, 1), (2, 26)],
  [(8, 1), (66, 21)],
  [(1, 15)],
  [(65, 67)],
  [(2, 32), (142, 1)],
  [(2, 22)],
  [(3, 1), (13, 17)],
  [(19, 26)],
  [(7, 20), (9, 1)],
  [(125, 73)],
  [(2, 19), (15, 1)],
  [(1, 16)],
  [(1, 1), (7, 19)],
  [(8, 1), (25, 27)],
  [(2, 21), (5, 1)],
  [(67, 20)],
  [(2, 1), (6, 43)],
  [(125, 46)],
  [(19, 1), (119, 26)],
  [(6, 50), (59, 1)],
  [(1, 17)],
  [(175, 38)],
  [(7, 29), (174, 1)],
  [(115, 50)],
  [(8, 1), (12, 48)],
  [(125, 37)],
  [(113, 49)],
  [(7, 1), (118, 19)],
  [(56, 1), (57, 23)],
  [(1, 18)],
  [(61, 23)],
  [(55, 80)],
  [(11, 25), (57, 1)],
  [(6, 1), (55, 38)],
  [(2, 1), (6, 49)],
  [(7, 26)],
  [(6, 24), (107, 1)],
  [(8, 1), (75, 24)],
  [(6, 17)],
  [(6, 1), (58, 41)],
  [(11, 40), (54, 1)],
  [(11, 28)],
  [(11, 1), (57, 53)],
  [(11, 1), (165, 26)],
  [(6, 1), (16, 26)],
  [(17, 1), (72, 17)],
  [(56, 1), (66, 26)],
  [(1, 9)],
  [(9, 1), (56, 13)],
  [(5, 196)],
  [(1, 65)],
  [(5, 97)],
  [(1, 37), (7, 1)],
  [(5, 64)],
  [(2, 37), (6, 1)],
  [(5, 46), (102, 1)],
  [(1, 21)],
  [(5, 36), (53, 1)],
  [(2, 1), (48, 29)],
  [(1, 68)],
  [(1, 48), (5, 1)],
  [(1, 39), (5, 1)],
  [(47, 67)],
  [(5, 1), (15, 32)],
  [(2, 1), (14, 48)],
  [(1, 22)],
  [(2, 1), (6, 31)],
  [(6, 1), (139, 23)],
  [(6, 1), (137, 31)],
  [(5, 106)],
  [(1, 39), (14, 1)],
  [(5, 70)],
  [(1, 28), (7, 1)],
  [(5, 52)],
  [(1, 23)],
  [(5, 40), (177, 1)],
  [(53, 1), (93, 33)],
  [(5, 34)],
  [(49, 29)],
  [(44, 1), (87, 72)],
  [(1, 34), (4, 1)],
  [(1, 30), (5, 1)],
  [(1, 25), (19, 1)],
  [(1, 24)],
  [(86, 43)],
  [(1, 1), (17, 29)],
  [(3, 1), (173, 34)],
  [(9, 1), (85, 29)],
  [(59, 29), (88, 1)],
  [(5, 76)],
  [(1, 1), (83, 44)],
  [(5, 54), (17, 1)],
  [(1, 25)],
  [(5, 42), (123, 1), (125, 1)],
  [(2, 1), (98, 30)],
  [(5, 37)],
  [(5, 1), (13, 30)],
  [(125, 55)],
  [(9, 1), (49, 35)],
  [(4, 236)],
  [(4, 47)],
  [(1, 26)],
  [(4, 55), (85, 1)],
  [(4, 1), (8, 32)],
  [(4, 77)],
  [(125, 46)],
  [(39, 37), (86, 1)],
  [(4, 38)],
  [(8, 1), (39, 72)],
  [(5, 61)],
  [(1, 27)],
  [(5, 47), (115, 1)],
  [(5, 1), (8, 33)],
  [(5, 40)],
  [(8, 46), (54, 1)],
  [(5, 34)],
  [(2, 1), (3, 25)],
  [(5, 1), (75, 76)],
  [(16, 1), (38, 32)],
  [(1, 28)],
  [(2, 1), (41, 48)],
  [(5, 1), (75, 40)],
  [(37, 83)],
  [(73, 62)],
  [(4, 118), (22, 1)],
  [(4, 41)],
  [(73, 35)],
  [(4, 47), (9, 1)],
  [(4, 27)],
  [(5, 1), (75, 85)],
  [(1, 1), (4, 31)],
  [(5, 43)],
  [(4, 35), (39, 1)],
  [(11, 1), (75, 41)],
  [(4, 41), (6, 1)],
  [(35, 127)],
  [(5, 1), (46, 30)],
  [(4, 28)],
  [(4, 1), (7, 34)],
  [(38, 1), (69, 88)],
  [(11, 43), (21, 1)],
  [(5, 1), (35, 51)],
  [(8, 1), (14, 36)],
  [(5, 1), (15, 28)],
  [(34, 64), (136, 1)],
  [(17, 1), (75, 42)],
  [(1, 13), (37, 1)],
  [(34, 36), (35, 1)],
  [(37, 1), (67, 31)],
  [(1, 98)],
  [(1, 70), (37, 1)],
  [(1, 57), (5, 1)],
  [(1, 46), (43, 1)],
  [(5, 1), (33, 47)],
  [(1, 1), (4, 55), (66, 1)],
  [(1, 32)],
  [(2, 1), (33, 46)],
  [(39, 1), (65, 70)],
  [(36, 1), (68, 46)],
  [(1, 74), (33, 1)],
  [(1, 58), (4, 1)],
  [(1, 50)],
  [(1, 41), (39, 1)],
  [(16, 1), (65, 41)],
  [(1, 33)],
  [(2, 1), (32, 57)],
  [(3, 1), (13, 35)],
  [(35, 49)],
  [(32, 1), (69, 47)],
  [(35, 76), (66, 1)],
  [(1, 50), (63, 1)],
  [(1, 44)],
  [(31, 59), (87, 1)],
  [(1, 34)],
  [(4, 75), (32, 1)],
  [(5, 1), (35, 42)],
  [(2, 1), (63, 32)],
  [(4, 1), (125, 59)],
  [(7, 36), (8, 1)],
  [(1, 53)],
  [(1, 43), (37, 1)],
  [(1, 37), (35, 2)],
  [(1, 35)],
  [(3, 101), (65, 1)],
  [(6, 101), (32, 1)],
  [(125, 52)],
  [(3, 101), (92, 1)],
  [(3, 50), (74, 1)],
  [(59, 103)],
  [(3, 107), (65, 1)],
  [(3, 52), (5, 1)],
  [(1, 36)],
  [(7, 45), (35, 1)],
  [(3, 52), (5, 1)],
  [(58, 107)],
  [(35, 64)],
  [(3, 52), (32, 1)],
  [(115, 53)],
  [(3, 1), (29, 61)],
  [(6, 110), (32, 1)],
  [(1, 37)],
  [(6, 54), (35, 1)],
  [(34, 65), (57, 1)],
  [(65, 55)],
  [(62, 64), (144, 1)],
  [(17, 1), (59, 45)],
  [(2, 1), (3, 35)],
  [(28, 45), (35, 1)],
  [(29, 1), (39, 53)],
  [(1, 38)],
  [(3, 1), (61, 47)],
  [(6, 1), (31, 41)],
  [(1, 27), (2, 1)],
  [(33, 1), (55, 83)],
  [(14, 1), (28, 66)],
  [(55, 56)],
  [(3, 107), (109, 2)],
  [(3, 54), (125, 1)],
  [(3, 37)],
  [(2, 1), (3, 113)],
  [(3, 57), (62, 1)],
  [(35, 58)],
  [(11, 42), (14, 1)],
  [(3, 56), (11, 1)],
  [(8, 115)],
  [(32, 43)],
  [(3, 56), (56, 1)],
  [(3, 38)],
  [(4, 1), (8, 41)],
  [(3, 1), (29, 88)],
  [(2, 1), (3, 38)],
  [(55, 89)],
  [(4, 1), (34, 43)],
  [(55, 59)],
  [(8, 1), (26, 171)],
  [(26, 1), (57, 57)],
  [(3, 39)],
  [(5, 1), (8, 42)],
  [(8, 48), (29, 1)],
  [(8, 61)],
  [(11, 1), (31, 51)],
  [(8, 1), (36, 39)],
  [(27, 1), (28, 59)],
  [(28, 2), (33, 58)],
  [(16, 1), (76, 70)],
  [(1, 20)],
  [(29, 1), (33, 58)],
  [(4, 1), (28, 31)],
  [(8, 1), (78, 38)],
  [(25, 392)],
  [(1, 77), (3, 1)],
  [(5, 130)],
  [(1, 54), (8, 1)],
  [(25, 194)],
  [(1, 43)],
  [(2, 1), (5, 75)],
  [(2, 1), (3, 62)],
  [(25, 128)],
  [(3, 1), (49, 53)],
  [(1, 80)],
  [(1, 65), (3, 1)],
  [(25, 98), (51, 1)],
  [(1, 48), (5, 1)],
  [(1, 44)],
  [(1, 1), (34, 55)],
  [(25, 77), (27, 1)],
  [(3, 1), (53, 64)],
  [(24, 64), (29, 1)],
  [(8, 1), (48, 63)],
  [(5, 136)],
  [(24, 66), (53, 1)],
  [(5, 98), (31, 1)],
  [(1, 45)],
  [(5, 78), (25, 2)],
  [(8, 1), (24, 132)],
  [(5, 67)],
  [(5, 1), (26, 78)],
  [(29, 1), (75, 65)],
  [(1, 1), (7, 64)],
  [(7, 104)],
  [(1, 50), (3, 1)],
  [(1, 46)],
  [(7, 59)],
  [(3, 67), (5, 1)],
  [(46, 137)],
  [(7, 1), (92, 50)],
  [(23, 2), (46, 79)],
  [(3, 44), (5, 1)],
  [(5, 1), (49, 39)],
  [(25, 212)],
  [(1, 47)],
  [(5, 83), (25, 1)],
  [(1, 1), (7, 82)],
  [(25, 140)],
  [(8, 1), (9, 45)],
  [(5, 58), (24, 1)],
  [(3, 45), (5, 1)],
  [(25, 104)],
  [(49, 83)],
  [(1, 48)],
  [(2, 1), (51, 70)],
  [(25, 86)],
  [(2, 1), (27, 46)],
  [(8, 1), (45, 46)],
  [(4, 1), (22, 208)],
  [(22, 71)],
  [(3, 1), (46, 59)],
  [(9, 46), (35, 1)],
  [(7, 47)],
  [(22, 110)],
  [(3, 1), (22, 53)],
  [(5, 73)],
  [(5, 1), (24, 71)],
  [(5, 61), (108, 1)],
  [(22, 71), (24, 1)],
  [(5, 53), (22, 1)],
  [(3, 70), (5, 1)],
  [(3, 48)],
  [(8, 1), (9, 46)],
  [(13, 1), (43, 88)],
  [(2, 1), (3, 48)],
  [(3, 1), (85, 62)],
  [(7, 54), (17, 1)],
  [(3, 48), (5, 1)],
  [(8, 1), (24, 72)],
  [(8, 1), (45, 47)],
  [(3, 49)],
  [(44, 55)],
  [(8, 1), (9, 47)],
  [(25, 152)],
  [(5, 1), (21, 148)],
  [(11, 1), (21, 74)],
  [(5, 1), (21, 49)],
  [(25, 113)],
  [(5, 1), (66, 73)],
  [(5, 50)],
  [(5, 1), (23, 87)],
  [(25, 87), (29, 1)],
  [(5, 1), (9, 48)],
  [(9, 1), (49, 65)],
  [(21, 76), (41, 1)],
  [(25, 77)],
  [(7, 1), (41, 56)],
  [(15, 1), (65, 64)],
  [(1, 24), (103, 1)],
  [(25, 63), (45, 1), (125, 1)],
  [(26, 1), (63, 49)],
  [(5, 1), (45, 49)],
  [(3, 1), (89, 31)],
  [(2, 490)],
  [(2, 163)],
  [(2, 96), (5, 1)],
  [(2, 1), (4, 96)],
  [(1, 54)],
  [(2, 237), (101, 1)],
  [(2, 121)],
  [(2, 79), (3, 1)],
  [(1, 1), (4, 67)],
  [(6, 1), (59, 67)],
  [(2, 166)],
  [(1, 1), (2, 98)],
  [(2, 69), (5, 1)],
  [(1, 55)],
  [(8, 1), (195, 81)],
  [(2, 120), (47, 1)],
  [(2, 82)],
  [(6, 80), (59, 1)],
  [(2, 1), (195, 160)],
  [(6, 1), (58, 80)],
  [(6, 1), (25, 125)],
  [(2, 1), (192, 83)],
  [(1, 56)],
  [(6, 1), (44, 61)],
  [(21, 2), (25, 98)],
  [(4, 167)],
  [(4, 70), (25, 1)],
  [(19, 98), (63, 1)],
  [(4, 83)],
  [(19, 1), (38, 98)],
  [(4, 101), (27, 1)],
  [(1, 57)],
  [(25, 72), (188, 1)],
  [(188, 73)],
  [(2, 1), (3, 55)],
  [(6, 83), (23, 1)],
  [(2, 1), (75, 83)],
  [(3, 1), (19, 83)],
  [(19, 71), (45, 1)],
  [(39, 82), (59, 1)],
  [(1, 58)],
  [(1, 1), (61, 73)],
  [(5, 52)],
  [(2, 1), (21, 56)],
  [(25, 50), (45, 1)],
  [(8, 1), (189, 56)],
  [(185, 172)],
  [(26, 1), (183, 168)],
  [(44, 1), (75, 84)],
  [(19, 57)],
  [(2, 265)],
  [(2, 129), (11, 1)],
  [(2, 88)],
  [(2, 2), (4, 73)],
  [(2, 51), (5, 1)],
  [(2, 175)],
  [(2, 103), (9, 1)],
  [(2, 73), (6, 1)],
  [(2, 58)],
  [(9, 1), (179, 64)],
  [(2, 133), (75, 1)],
  [(2, 87), (5, 1)],
  [(2, 67)],
  [(21, 1), (178, 65)],
  [(25, 89)],
  [(2, 104), (16, 1)],
  [(2, 76)],
  [(2, 59)],
  [(3, 1), (25, 74)],
  [(9, 1), (58, 65)],
  [(193, 182)],
  [(1, 1), (193, 76)],
  [(175, 272)],
  [(7, 89), (18, 1)],
  [(2, 1), (23, 66)],
  [(4, 1), (176, 134)],
  [(2, 60)],
  [(52, 77)],
  [(2, 1), (35, 75)],
  [(19, 179)],
  [(19, 137), (69, 1)],
  [(21, 90), (26, 1)],
  [(55, 92)],
  [(69, 1), (194, 67)],
  [(175, 110)],
  [(2, 61)],
  [(7, 77), (171, 1)],
  [(3, 1), (53, 76)],
  [(2, 1), (24, 59)],
  [(17, 109)],
  [(17, 139), (39, 1)],
  [(21, 1), (22, 92)],
  [(2, 1), (186, 91)],
  [(17, 1), (27, 61)],
  [(1, 31)],
  [(2, 1), (34, 78)],
  [(17, 78), (185, 1)],
  [(2, 1), (186, 60)],
  [(24, 1), (184, 77)],
  [(167, 79)],
  [(2, 196)],
  [(1, 1), (2, 116)],
  [(5, 144), (17, 1)],
  [(1, 65)],
  [(5, 114), (25, 2)],
  [(1, 1), (2, 143)],
  [(2, 97)],
  [(5, 1), (33, 95)],
  [(2, 1), (165, 95)],
  [(2, 1), (69, 63)],
  [(2, 118), (33, 1)],
  [(2, 85)],
  [(1, 66)],
  [(17, 73), (18, 1)],
  [(5, 1), (165, 97)],
  [(2, 97), (18, 1)],
  [(2, 1), (195, 97)],
  [(18, 64), (26, 1)],
  [(34, 98)],
  [(17, 1), (18, 64)],
  [(5, 151)],
  [(1, 67)],
  [(5, 118), (21, 1)],
  [(2, 1), (161, 84)],
  [(5, 100)],
  [(16, 599)],
  [(2, 1), (5, 84)],
  [(1, 1), (16, 97)],
  [(5, 73), (48, 1)],
  [(8, 1), (159, 195)],
  [(1, 68)],
  [(8, 1), (81, 66)],
  [(16, 122)],
  [(158, 100), (174, 1)],
  [(65, 76)],
  [(6, 1), (32, 85)],
  [(175, 101)],
  [(173, 121)],
  [(8, 1), (174, 99)],
  [(8, 67)],
  [(175, 155)],
  [(5, 1), (161, 87)],
  [(5, 103)],
  [(2, 1), (47, 75)],
  [(5, 88)],
  [(16, 101), (18, 1)],
  [(155, 120), (172, 2)],
  [(5, 1), (62, 60)],
  [(5, 68)],
  [(17, 75), (47, 1)],
  [(154, 314)],
  [(2, 103), (51, 1)],
  [(16, 1), (31, 88)],
  [(8, 1), (17, 153)],
  [(2, 1), (63, 68)],
  [(2, 122), (46, 1), (168, 1)],
  [(2, 87), (5, 1)],
  [(2, 69)],
  [(2, 1), (169, 87)],
  [(17, 87), (158, 1)],
  [(2, 106)],
  [(2, 78), (5, 1)],
  [(5, 89), (31, 1)],
  [(1, 1), (151, 103)],
  [(5, 79)],
  [(2, 89), (154, 1)],
  [(2, 70)],
  [(2, 1), (3, 206)],
  [(5, 1), (15, 206)],
  [(2, 1), (3, 68)],
  [(2, 1), (3, 212)],
  [(3, 105), (17, 1)],
  [(2, 1), (3, 70)],
  [(17, 1), (18, 70)],
  [(5, 1), (15, 209)],
  [(2, 71)],
  [(15, 105), (179, 1)],
  [(2, 1), (3, 104)],
  [(59, 106)],
  [(8, 1), (9, 69)],
  [(5, 1), (15, 215)],
  [(3, 1), (31, 107)],
  [(5, 1), (15, 107)],
  [(47, 1), (147, 107)],
  [(3, 72)],
  [(18, 1), (146, 319)],
  [(35, 91), (162, 1)],
  [(3, 1), (146, 106)],
  [(15, 105), (175, 2)],
  [(2, 1), (16, 78)],
  [(29, 220)],
  [(32, 81), (44, 1)],
  [(145, 1), (175, 130)],
  [(1, 35), (23, 1)],
  [(15, 107), (16, 2)],
  [(16, 131)],
  [(2, 1), (15, 71)],
  [(23, 1), (33, 107)],
  [(145, 129), (149, 1)],
  [(29, 1), (159, 71)],
  [(143, 343)],
  [(2, 1), (3, 113)],
  [(1, 76)],
  [(8, 1), (144, 74)],
  [(3, 112), (5, 1)],
  [(142, 227)],
  [(17, 136)],
  [(58, 1), (143, 167)],
  [(2, 1), (3, 74)],
  [(16, 1), (158, 83)],
  [(2, 1), (141, 229)],
  [(1, 77)],
  [(31, 1), (142, 97)],
  [(17, 97), (24, 1)],
  [(143, 115)],
  [(1, 1), (14, 338)],
  [(14, 97), (45, 1)],
  [(2, 1), (3, 75)],
  [(14, 1), (195, 113)],
  [(14, 1), (28, 84)],
  [(1, 78)],
  [(43, 99), (143, 1)],
  [(5, 70)],
  [(14, 115), (18, 1)],
  [(25, 1), (155, 86)],
  [(28, 1), (152, 173)],
  [(2, 58)],
  [(152, 1), (153, 76)],
  [(44, 1), (165, 114)],
  [(7, 77)],
  [(137, 355)],
  [(152, 100), (171, 1)],
  [(41, 118)],
  [(14, 1), (137, 87)],
  [(15, 232), (56, 1)],
  [(3, 1), (166, 116)],
  [(14, 1), (15, 116)],
  [(3, 115), (14, 1)],
  [(3, 78)],
  [(29, 1), (149, 138)],
  [(5, 1), (15, 236)],
  [(2, 1), (3, 78)],
  [(15, 118), (155, 1)],
  [(7, 1), (14, 101)],
  [(148, 119)],
  [(7, 1), (136, 100)],
  [(15, 1), (137, 100)],
  [(3, 79)],
  [(15, 117), (134, 1)],
  [(29, 1), (147, 116)],
  [(4, 242)],
  [(4, 102), (14, 1)],
  [(6, 1), (16, 89)],
  [(4, 119), (27, 1)],
  [(15, 118), (28, 2)],
  [(4, 142), (16, 1)],
  [(2, 80)],
  [(3, 1), (16, 101)],
  [(4, 88), (7, 1)],
  [(2, 1), (29, 117)],
  [(15, 1), (145, 182)],
  [(15, 1), (41, 103)],
  [(2, 1), (15, 80)],
  [(8, 1), (27, 80)],
  [(8, 1), (55, 90)],
  [(2, 81)],
  [(17, 1), (132, 120)],
  [(3, 2), (133, 143)],
  [(2, 1), (3, 79)],
  [(19, 1), (29, 89)],
  [(13, 371)],
  [(131, 247)],
  [(3, 1), (131, 91)],
  [(17, 1), (144, 81)],
  [(3, 82)],
  [(4, 182), (144, 1)],
  [(4, 2), (129, 120)],
  [(13, 245)],
  [(4, 103), (145, 1)],
  [(8, 1), (9, 80)],
  [(4, 125)],
  [(26, 1), (141, 123)],
  [(5, 1), (155, 105)],
  [(4, 83)],
  [(55, 1), (143, 92)],
  [(26, 105), (32, 1)],
  [(14, 124)],
  [(6, 1), (13, 104)],
  [(65, 1), (165, 122)],
  [(9, 1), (127, 122)],
  [(14, 1), (38, 150)],
  [(143, 1), (153, 83)],
  [(1, 42)],
  [(14, 151)],
  [(14, 1), (165, 124)],
  [(14, 124), (18, 1)],
  [(39, 1), (142, 74)],
  [(3, 1), (133, 92)],
  [(14, 1), (39, 82)],
  [(89, 1), (189, 82)],
  [(125, 784)],
  [(1, 87)],
  [(5, 155), (25, 1)],
  [(2, 1), (137, 192)],
  [(25, 260)],
  [(4, 110), (126, 1)],
  [(5, 110), (25, 1)],
  [(2, 1), (3, 85)],
  [(125, 388)],
  [(3, 1), (136, 95)],
  [(1, 88)],
  [(1, 78), (2, 1)],
  [(25, 158)],
  [(1, 64), (7, 1)],
  [(8, 1), (15, 129)],
  [(2, 1), (14, 111)],
  [(125, 262)],
  [(6, 1), (136, 110)],
  [(125, 1), (135, 86)],
  [(16, 87)],
  [(5, 160)],
  [(3, 1), (134, 112)],
  [(5, 133)],
  [(27, 87), (44, 1)],
  [(125, 199)],
  [(1, 1), (4, 130)],
  [(4, 1), (5, 98)],
  [(26, 1), (63, 87)],
  [(4, 88)],
  [(169, 113)],
  [(5, 1), (147, 133)],
  [(2, 1), (123, 88)],
  [(5, 1), (125, 159)],
  [(137, 79), (147, 1)],
  [(3, 88), (5, 1)],
  [(12, 264), (26, 1)],
  [(12, 132), (17, 1)],
  [(3, 89)],
  [(24, 132), (179, 1)],
  [(3, 1), (49, 98)],
  [(25, 272)],
  [(5, 1), (132, 134)],
  [(12, 134), (155, 1)],
  [(12, 1), (121, 134)],
  [(25, 203)],
  [(12, 134), (38, 1)],
  [(5, 90)],
  [(13, 199), (49, 1)],
  [(13, 1), (25, 160)],
  [(39, 1), (119, 133)],
  [(12, 273), (26, 1)],
  [(12, 135), (26, 1)],
  [(25, 137)],
  [(17, 1), (27, 90)],
  [(13, 164)],
  [(2, 91)],
  [(4, 1), (25, 115)],
  [(13, 101), (153, 1)],
  [(14, 136)],
  [(6, 1), (119, 100)],
  [(35, 208)],
  [(12, 1), (151, 137)],
  [(2, 1), (5, 102)],
  [(27, 91), (35, 1)],
  [(5, 92)],
  [(12, 1), (14, 163)],
  [(35, 118)],
  [(2, 1), (3, 90)],
  [(15, 136), (128, 1)],
  [(35, 1), (129, 135)],
  [(23, 280)],
  [(6, 1), (23, 103)],
  [(13, 1), (46, 103)],
  [(7, 93)],
  [(15, 1), (23, 166)],
  [(24, 277), (128, 1)],
  [(137, 139)],
  [(13, 119)],
  [(4, 74), (9, 1)],
  [(8, 1), (57, 91)],
  [(125, 424)],
  [(125, 1), (126, 93)],
  [(5, 94)],
  [(34, 119), (57, 1)],
  [(25, 166), (125, 2)],
  [(6, 1), (26, 139)],
  [(35, 166), (114, 2)],
  [(23, 119), (115, 1)],
  [(125, 280)],
  [(8, 1), (9, 92)],
  [(118, 107)],
  [(1, 46), (19, 1)],
  [(25, 122)],
  [(56, 1), (112, 105)],
  [(113, 142)],
  [(14, 1), (114, 140)],
  [(47, 1), (125, 210)],
  [(23, 1), (123, 93)],
  [(15, 1), (145, 119)],
  [(19, 1), (89, 83)],
  [(1, 98)],
  [(2, 1), (111, 290)],
  [(5, 1), (111, 145)],
  [(111, 1), (134, 145)],
  [(125, 174), (155, 1)],
  [(122, 124), (126, 1)],
  [(2, 1), (117, 96)],
  [(5, 1), (116, 78)],
  [(4, 1), (125, 86)],
  [(1, 47), (21, 1)],
  [(11, 445)],
  [(2, 1), (11, 219)],
  [(11, 148)],
  [(11, 109), (24, 1)],
  [(22, 1), (23, 125)],
  [(22, 146), (114, 1)],
  [(35, 1), (45, 97)],
  [(12, 145), (23, 1)],
  [(12, 98)],
  [(11, 1), (37, 87)],
  [(11, 223), (12, 1)],
  [(11, 148), (12, 1)],
  [(11, 1), (141, 148)],
  [(11, 88), (12, 1)],
  [(13, 149)],
  [(8, 1), (12, 294)],
  [(12, 147), (35, 1)],
  [(12, 99)],
  [(25, 126), (125, 1)],
  [(8, 1), (108, 97)],
  [(11, 151)],
  [(11, 2), (13, 127)],
  [(25, 113)],
  [(1, 1), (11, 74)],
  [(15, 148), (118, 2)],
  [(12, 148), (14, 1)],
  [(12, 100)],
  [(1, 1), (46, 88)],
  [(14, 1), (129, 148)],
  [(8, 1), (108, 98)],
  [(11, 1), (15, 151)],
  [(11, 1), (32, 129)],
  [(5, 1), (12, 100)],
  [(14, 112), (15, 1)],
  [(35, 91)],
  [(12, 101)],
  [(12, 1), (35, 112)],
  [(13, 112), (109, 1)],
  [(5, 1), (15, 99)],
  [(117, 1), (137, 112)],
  [(12, 1), (116, 229)],
  [(2, 1), (12, 101)],
  [(18, 1), (35, 82)],
  [(14, 1), (21, 151)],
  [(13, 102)],
  [(22, 227), (108, 1)],
  [(15, 1), (22, 113)],
  [(2, 1), (23, 150)],
  [(115, 1), (119, 113)],
  [(17, 1), (117, 100)],
  [(125, 310)],
  [(5, 1), (23, 114)],
  [(26, 1), (105, 306)],
  [(21, 103)],
  [(105, 153), (125, 1)],
  [(14, 1), (114, 305)],
  [(2, 1), (105, 101)],
  [(106, 91), (109, 1)],
  [(125, 228), (155, 1)],
  [(29, 1), (129, 101)],
  [(23, 1), (33, 155)],
  [(24, 1), (31, 185)],
  [(21, 104)],
  [(24, 1), (107, 115)],
  [(25, 1), (115, 184)],
  [(12, 1), (32, 154)],
  [(12, 1), (125, 184)],
  [(113, 133)],
  [(35, 1), (45, 102)],
  [(14, 1), (138, 76)],
  [(35, 1), (145, 117)],
  [(21, 105)],
  [(5, 1), (105, 155)],
  [(17, 1), (117, 103)],
  [(125, 157)],
  [(32, 1), (132, 155)],
  [(42, 1), (142, 116)],
  [(23, 1), (123, 103)],
  [(65, 1), (125, 84)],
  [(8, 1), (109, 54)],
  [(1, 53)],
  [(11, 1), (111, 314)],
  [(111, 157), (122, 1)],
  [(11, 1), (111, 104)],
  [(115, 95)],
  [(112, 85), (118, 1)],
  [(122, 79)],
  [(6, 1), (133, 71)],
  [(8, 1), (145, 54)],
  [(1, 35)]
]

private def certificate (n : ℕ) : List (ℕ × ℕ) := certificateData[n]?.getD []

private def certificateSum (n : ℕ) (cs : List (ℕ × ℕ)) : ℕ :=
  (cs.map (fun jc => jc.2 * digitSum (n * jc.1))).sum

private def checkCertificate (n : ℕ) (cs : List (ℕ × ℕ)) : Bool :=
  decide (2 * digitSum n + certificateSum n cs = n)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction checks the supplied decimal-block certificate at every small index.
private theorem certificates_checked : ∀ n : Fin 1000,
    n.val < 10 ∨ n.val = 11 ∨ n.val = 17 ∨ n.val = 19 ∨
      checkCertificate n.val (certificate n.val) = true := by
  decide +kernel

private theorem certificate_blocks (n : ℕ) (cs : List (ℕ × ℕ)) :
    ∃ bs : List ℕ, (∀ y ∈ bs, n ∣ y) ∧
      (bs.map digitSum).sum = certificateSum n cs := by
  refine ⟨cs.flatMap (fun jc => List.replicate jc.2 (n * jc.1)), ?_, ?_⟩
  · intro y hy
    obtain ⟨jc,hjc,hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨_,he⟩ := List.mem_replicate.mp hy
    rw [he]
    exact dvd_mul_right n _
  · change ((cs.flatMap (fun jc => List.replicate jc.2 (n * jc.1))).map digitSum).sum =
      (cs.map (fun jc => jc.2 * digitSum (n * jc.1))).sum
    induction cs with
    | nil => rfl
    | cons jc cs ih =>
      simpa [List.map_append, List.map_replicate, List.sum_replicate, smul_eq_mul] using
        congrArg (fun t => jc.2 * digitSum (n * jc.1) + t) ih

private theorem certificate_sound (n : ℕ) (cs : List (ℕ × ℕ)) (hn : 0 < n)
    (hc : checkCertificate n cs = true) : Admissible n := by
  have he : 2 * digitSum n + certificateSum n cs = n := of_decide_eq_true hc
  obtain ⟨bs,hb,hs⟩ := certificate_blocks n cs
  exact from_blocks n hn bs hb (by omega)

private theorem admissible_small (n : ℕ) (hn : 1 ≤ n) (hlt : n < 1000)
    (h11 : n ≠ 11) (h17 : n ≠ 17) (h19 : n ≠ 19) : Admissible n := by
  by_cases hsmall : n < 10
  · refine ⟨n, by omega, dvd_refl n, ?_, begins_self n, ?_⟩
    · simp only [digitSum, Nat.digits_of_lt 10 n (by omega) hsmall, List.sum_singleton]
    · exact Nat.mod_eq_of_lt (Nat.lt_base_pow_length_digits (by norm_num))
  · have hc := certificates_checked ⟨n,hlt⟩
    simp only at hc
    have he : checkCertificate n (certificate n) = true := by
      rcases hc with h | h | h | h | h
      · exact False.elim (hsmall h)
      · exact False.elim (h11 h)
      · exact False.elim (h17 h)
      · exact False.elim (h19 h)
      · exact h
    exact certificate_sound n (certificate n) (by omega) he

/-- Complete existence classification, with overlapping decimal ends allowed. -/
private theorem classification (n : ℕ) (hn : 1 ≤ n) :
    Admissible n ↔ n ≠ 11 ∧ n ≠ 17 ∧ n ≠ 19 := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · rintro rfl; exact not_admissible_eleven h
    · rintro rfl; exact not_admissible_seventeen h
    · rintro rfl; exact not_admissible_nineteen h
  · rintro ⟨h11,h17,h19⟩
    by_cases h : 1000 ≤ n
    · exact admissible_tail n h
    · exact admissible_small n hn (by omega) h11 h17 h19

/-- Murthy's whole least-or-zero assertion for OEIS A077739. -/
theorem result : claim := by
  intro n hn
  rw [a_zero_iff, classification n hn]
  omega

#check @classification
#check @result
#print axioms result
#print axioms a_zero_iff
#print axioms admissible_tail
#print axioms not_admissible_eleven
#print axioms not_admissible_seventeen
#print axioms not_admissible_nineteen
end D5.S1.Digit.Admissibility.MurthyA077739Classification
