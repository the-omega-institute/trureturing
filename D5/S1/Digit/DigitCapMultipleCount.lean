/- GID: D5/S1/Digit/DigitCapMultipleCount
   generality: I
   mirror-B: D5/B/S1/Digit/DigitCapMultipleCount
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: With digit cap a*ell-1 the count of n is the sum of cap a-1 counts up to n/ell. -/

import D5.S1.Digit.DigitCapQuotientBound

/-! # Digit caps one below a multiple of the radix

For a radix `ell ≥ 2` and `a ≥ 1`, every digit `d ≤ a * ell - 1` splits uniquely as
`d = ell * q + r` with `q ≤ a - 1` and `r < ell`. The remainders form the ordinary radix
expansion of `n - ell * t`, where `t` is the weight of the quotients, so
`b(a * ell - 1, ell, n) = ∑_{t ≤ n / ell} b(a - 1, ell, t)`.
-/

set_option autoImplicit false

namespace D5.S1.Digit.DigitCapMultipleCount

open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open scoped BigOperators

noncomputable section

private lemma weight_add (ell : ℕ) (x y : ℕ →₀ ℕ) :
    weight ell (x + y) = weight ell x + weight ell y := by
  unfold weight
  exact Finsupp.sum_add_index' (by simp) (by intros; ring)

private lemma weight_smul (ell c : ℕ) (x : ℕ →₀ ℕ) : weight ell (c • x) = c * weight ell x := by
  unfold weight
  rw [Finsupp.sum_smul_index (by simp), Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro i _
  ring

/-- Every natural number has exactly one radix expansion with digits below the radix: at most
one by the quotient-digit bound with `q = 1`, at least one by `count_positive`. -/
lemma count_standard (ell R : ℕ) (hell : 2 ≤ ell) : count (ell - 1) ell R = 1 := by
  have hR : R < ell ^ (R + 1) :=
    (Nat.lt_pow_self (by omega)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hle := DigitCapQuotientBound.count_le_pow ell 1 R (ell - 1) R hell le_rfl (by omega) hR
  have hpos := count_positive (ell - 1) ell R hell le_rfl
  rw [one_pow] at hle
  omega

private lemma standard_unique {ell : ℕ} (hell : 2 ≤ ell) (R : ℕ) (x y : ℕ →₀ ℕ)
    (hx : ∀ i, x i < ell) (hy : ∀ i, y i < ell) (hxw : weight ell x = R)
    (hyw : weight ell y = R) : x = y := by
  have hsub := (Nat.card_eq_one_iff_unique.mp (count_standard ell R hell)).1
  have := hsub.elim ⟨x, fun i => by have := hx i; omega, hxw⟩
    ⟨y, fun i => by have := hy i; omega, hyw⟩
  exact congrArg Subtype.val this

private lemma standard_exists {ell : ℕ} (hell : 2 ≤ ell) (R : ℕ) :
    ∃ x : ℕ →₀ ℕ, (∀ i, x i ≤ ell - 1) ∧ weight ell x = R := by
  have hcount := count_positive (ell - 1) ell R hell le_rfl
  have := partitions_finite (ell - 1) ell R hell
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.mp hcount).1
  exact ⟨x, hx⟩

/-- The radix expansion of `R` with digits below `ell`. -/
private def std {ell : ℕ} (hell : 2 ≤ ell) (R : ℕ) : ℕ →₀ ℕ :=
  Classical.choose (standard_exists hell R)

private lemma std_spec {ell : ℕ} (hell : 2 ≤ ell) (R : ℕ) :
    (∀ i, std hell R i < ell) ∧ weight ell (std hell R) = R := by
  obtain ⟨h1, h2⟩ := Classical.choose_spec (standard_exists hell R)
  exact ⟨fun i => by have := h1 i; unfold std; omega, h2⟩

/-- Pointwise quotients by the radix. -/
private def quot (ell : ℕ) (d : ℕ →₀ ℕ) : ℕ →₀ ℕ := d.mapRange (· / ell) (Nat.zero_div ell)

/-- Pointwise remainders modulo the radix. -/
private def rem (ell : ℕ) (d : ℕ →₀ ℕ) : ℕ →₀ ℕ := d.mapRange (· % ell) (Nat.zero_mod ell)

private lemma split (ell : ℕ) (d : ℕ →₀ ℕ) : ell • quot ell d + rem ell d = d := by
  ext i
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, quot, rem,
    Finsupp.mapRange_apply]
  exact Nat.div_add_mod (d i) ell

private lemma weight_split (ell : ℕ) (d : ℕ →₀ ℕ) :
    weight ell d = ell * weight ell (quot ell d) + weight ell (rem ell d) := by
  conv_lhs => rw [← split ell d]
  rw [weight_add, weight_smul]

private lemma quot_combine {ell : ℕ} (hell : 0 < ell) (q s : ℕ →₀ ℕ) (hs : ∀ i, s i < ell) :
    quot ell (ell • q + s) = q := by
  ext i
  simp only [quot, Finsupp.mapRange_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Nat.mul_add_div hell, Nat.div_eq_of_lt (hs i), add_zero]

private lemma cap_split {ell a : ℕ} (ha : 1 ≤ a) : ell * (a - 1) + (ell - 1) = a * ell - 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rcases Nat.eq_zero_or_pos ell with h | h
  · subst h; simp
  · rw [Nat.add_sub_cancel, show (b + 1) * ell = ell * b + ell by ring]
    omega

/-- The weight of the quotient digits, as an index in `0, …, n / ell`. -/
private def fiberIndex {ell a n : ℕ} (hell : 2 ≤ ell) (d : Partitions (a * ell - 1) ell n) :
    Fin (n / ell + 1) :=
  ⟨weight ell (quot ell d.val), by
    have h := weight_split ell d.val
    rw [d.property.2] at h
    have : weight ell (quot ell d.val) ≤ n / ell :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; omega)
    omega⟩

/-- Each fiber of `fiberIndex` is in bijection with the cap-`a - 1` representations of `t`. -/
private def fiberEquiv {ell a n : ℕ} (hell : 2 ≤ ell) (ha : 1 ≤ a) (t : Fin (n / ell + 1)) :
    {d : Partitions (a * ell - 1) ell n // fiberIndex hell d = t} ≃
      Partitions (a - 1) ell t where
  toFun d := ⟨quot ell d.1.val, fun i => by
      have h1 := d.1.property.1 i
      have hlt : d.1.val i < a * ell := by
        have : 1 ≤ a * ell := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega
      have := (Nat.div_lt_iff_lt_mul (by omega)).mpr hlt
      simp only [quot, Finsupp.mapRange_apply]
      omega,
    by have := congrArg Fin.val d.2; exact this⟩
  invFun q := ⟨⟨ell • q.val + std hell (n - ell * t), fun i => by
      have hq := q.property.1 i
      have hs := (std_spec hell (n - ell * t)).1 i
      have hm : ell * q.val i ≤ ell * (a - 1) := Nat.mul_le_mul_left ell hq
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      have := cap_split (ell := ell) ha
      omega,
    by
      have ht : ell * (t : ℕ) ≤ n := by
        have := t.isLt
        have h2 : (t : ℕ) ≤ n / ell := by omega
        have := (Nat.le_div_iff_mul_le (by omega)).mp h2
        rw [mul_comm]; exact this
      rw [weight_add, weight_smul, q.property.2, (std_spec hell (n - ell * t)).2]
      omega⟩,
    by
      apply Fin.ext
      simp only [fiberIndex]
      rw [quot_combine (by omega) _ _ (std_spec hell _).1, q.property.2]⟩
  left_inv d := by
    obtain ⟨⟨d, hd⟩, hdt⟩ := d
    apply Subtype.ext
    apply Subtype.ext
    simp only
    have hw : weight ell (quot ell d) = t := congrArg Fin.val hdt
    have hr : std hell (n - ell * t) = rem ell d := by
      apply standard_unique hell (n - ell * t) _ _ (std_spec hell _).1
      · intro i
        simp only [rem, Finsupp.mapRange_apply]
        exact Nat.mod_lt _ (by omega)
      · exact (std_spec hell _).2
      · have h := weight_split ell d
        rw [hd.2, hw] at h
        omega
    rw [hr, split]
  right_inv q := by
    apply Subtype.ext
    simp only
    exact quot_combine (by omega) _ _ (std_spec hell _).1

/-- For a radix `ell ≥ 2` and `a ≥ 1`,
`b(a * ell - 1, ell, n) = ∑_{t = 0}^{⌊n / ell⌋} b(a - 1, ell, t)`. -/
theorem count_multiple (ell a n : ℕ) (hell : 2 ≤ ell) (ha : 1 ≤ a) :
    count (a * ell - 1) ell n = ∑ t ∈ Finset.range (n / ell + 1), count (a - 1) ell t := by
  classical
  have := partitions_finite (a * ell - 1) ell n hell
  have e := (Equiv.sigmaFiberEquiv (fiberIndex (a := a) (n := n) hell)).symm
  rw [count, Nat.card_congr e, Nat.card_sigma,
    ← Fin.sum_univ_eq_sum_range (fun t => count (a - 1) ell t)]
  apply Finset.sum_congr rfl
  intro t _
  exact Nat.card_congr (fiberEquiv hell ha t)

/-- With cap `ell ^ 2 - 1` every `n` has exactly `⌊n / ell⌋ + 1` representations. -/
theorem count_square_sub_one (ell n : ℕ) (hell : 2 ≤ ell) :
    count (ell ^ 2 - 1) ell n = n / ell + 1 := by
  rw [show ell ^ 2 - 1 = ell * ell - 1 by ring_nf, count_multiple ell ell n hell (by omega)]
  simp [count_standard ell _ hell]

/-- For `a ≥ 1` the counts with cap `a * ell - 1` are nondecreasing in `n`; for `a ≥ 2` they
are not constant, since the count at `ell` exceeds the count at `0`. -/
theorem count_multiple_mono (ell a : ℕ) (hell : 2 ≤ ell) (ha : 1 ≤ a) :
    Monotone (count (a * ell - 1) ell) ∧
    (2 ≤ a → count (a * ell - 1) ell 0 < count (a * ell - 1) ell ell) := by
  refine ⟨fun n n' hnn => ?_, fun ha2 => ?_⟩
  · rw [count_multiple ell a n hell ha, count_multiple ell a n' hell ha]
    apply Finset.sum_le_sum_of_subset
    intro t ht
    simp only [Finset.mem_range] at ht ⊢
    have := Nat.div_le_div_right (c := ell) hnn
    omega
  · rw [count_multiple ell a 0 hell ha, count_multiple ell a ell hell ha,
      Nat.zero_div, zero_add, Nat.div_self (by omega), Finset.sum_range_succ (n := 1)]
    have h1 : 0 < count (a - 1) ell 1 := by
      have := partitions_finite (a - 1) ell 1 hell
      have hp : Nonempty (Partitions (a - 1) ell 1) := ⟨⟨Finsupp.single 0 1, fun i => by
          rw [Finsupp.single_apply]
          split_ifs <;> omega,
        by simp [weight]⟩⟩
      exact Nat.card_pos
    omega

end

end D5.S1.Digit.DigitCapMultipleCount
