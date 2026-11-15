/- GID: D5/S1/Digit/Admissibility/MurthyA077739Classification
   generality: I
   mirror-B: D5/B/S1/Digit/Admissibility/MurthyA077739Classification
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S1/Digit/Admissibility/MurthyA077739Classification.result; instance=D5/S1/Digit/Admissibility/MurthyA077739Classification.certificateData; result=D5/S1/Digit/Admissibility/MurthyA077739Classification.result
   digest: The complete unbounded existence and least-or-zero classification for Murthy A077739. -/
import Mathlib.Data.Nat.Digits.Div
import D5.S1.Digit.Admissibility.MurthyA077739CertificateLow
import D5.S1.Digit.Admissibility.MurthyA077739CertificateHigh
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

/-! Decimal blocks and the exact unbounded source predicate.

Generality I: the decimal classification consumes concrete certificate rows below 1000.
The symbolic tail and the final assertion remain unbounded in n and witness length;
no classification for arbitrary numeral bases is asserted.
-/

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
  simpa [digitSum, width, Nat.mul_comm] using
    List.sum_le_length_nsmul (Nat.digits 10 n) 9
      (fun x hx => Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hx))

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

/-- Ordered certificate rows for all indices below one thousand. -/
private def certificateData : Array (List (ℕ × ℕ)) :=
  MurthyA077739CertificateLow.entries ++ MurthyA077739CertificateHigh.entries

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
