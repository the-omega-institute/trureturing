/- GID: D5/S3/Factorization/PrimeExponentRecordLimitOne
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimeExponentRecordLimitOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-exponent records near one are powers of two or three times a positive power. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Prime-exponent record limit at one

OEIS A384669 (Hal M. Switkay, 2025-06-06) defines `f x n` by summing the
`x`-th powers of the exponents in the prime factorization of `n`. It conjectures
that, as `x` approaches one from the left, the strict record set becomes OEIS
A029744 without `3`. The latter entry describes the numbers `2^k` and
`3 * 2^k`.

The anchor below proves the honest pointwise eventual formulation: for each
fixed positive `n`, some left neighborhood of one decides record membership.
It does not assert a uniform neighborhood or a sequence-level notion of limit.
The tie for `3 * 2^k` is broken using Mathlib's
`Real.strictConcaveOn_rpow`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.Factorization.PrimeExponentRecordLimitOne

/-- The A384669 score: the sum of the `x`-th powers of the nonzero prime exponents. -/
def f (x : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, ((n.factorization p : ℝ)) ^ x

/-- A positive integer is a strict record when its score beats every positive predecessor. -/
def StrictRecord (x : ℝ) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → f x m < f x n

private theorem f_eq_factorization_sum (x : ℝ) (n : ℕ) :
    f x n = n.factorization.sum (fun _ e => (e : ℝ) ^ x) := by
  simp [f, Finsupp.sum, Nat.support_factorization]

private theorem continuousAt_f (n : ℕ) :
    ContinuousAt (fun x : ℝ => f x n) 1 := by
  simp_rw [f_eq_factorization_sum]
  unfold Finsupp.sum
  apply (continuous_finsetSum _ ?_).continuousAt
  intro p hp
  apply Real.continuous_const_rpow
  exact_mod_cast (Finsupp.mem_support_iff.mp hp)

private lemma eventually_pos_left_of_continuousAt {g : ℝ → ℝ} (hg : ContinuousAt g 1)
    (hpos : 0 < g 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ x : ℝ, 1 - δ < x → x < 1 → 0 < g x := by
  have hmem : g ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds (1 : ℝ) :=
    hg.preimage_mem_nhds (Ioi_mem_nhds hpos)
  rcases (Metric.mem_nhds_iff.mp hmem) with ⟨ε, hε, hball⟩
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ1 : δ < 1 := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro x hleft hright
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  rw [abs_lt]
  constructor <;> linarith [min_le_left (ε / 2) (1 / 2)]

/-- At `x = 1`, the score is Mathlib's prime-factor count with multiplicity. -/
theorem f_one (n : ℕ) : f 1 n = (ArithmeticFunction.cardFactors n : ℝ) := by
  rw [f_eq_factorization_sum]
  simp [ArithmeticFunction.cardFactors_eq_sum_factorization]

private theorem f_one_eq_omega (n : ℕ) : f 1 n = (n.primeFactorsList.length : ℝ) := by
  rw [f_one]
  simp [ArithmeticFunction.cardFactors_apply]

private theorem f_two_pow (x : ℝ) (hx : 0 < x) (k : ℕ) :
    f x (2 ^ k) = (k : ℝ) ^ x := by
  rw [f_eq_factorization_sum, Nat.factorization_pow, Nat.Prime.factorization Nat.prime_two]
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (by simp [hx.ne'])]
  simp [Finsupp.smul_single]

private theorem f_three_two_pow (x : ℝ) (hx : 0 < x) (k : ℕ) :
    f x (3 * 2 ^ k) = (1 : ℝ) ^ x + (k : ℝ) ^ x := by
  rw [f_eq_factorization_sum, Nat.factorization_mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    Nat.Prime.factorization Nat.prime_three, Nat.factorization_pow,
    Nat.Prime.factorization Nat.prime_two]
  rw [Finsupp.sum_of_support_subset _
    (Finsupp.support_add.trans (Finset.union_subset_union Finsupp.support_single_subset
      Finsupp.support_smul)) _ (by simp [hx.ne'])]
  simp [Finsupp.smul_single]

example : f (1 / 2) 12 = (2 : ℝ) ^ (1 / 2 : ℝ) + 1 := by
  simpa [add_comm] using (f_three_two_pow (1 / 2 : ℝ) (by norm_num) 2)

set_option maxRecDepth 100000 in
example : f (1 / 2) 30 = 3 := by
  have hfac : (30 : ℕ).factorization =
      Finsupp.single 2 1 + Finsupp.single 3 1 + Finsupp.single 5 1 := by
    rw [show (30 : ℕ) = (2 * 3) * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization Nat.prime_two,
      Nat.Prime.factorization Nat.prime_three,
      Nat.Prime.factorization Nat.prime_five]
  rw [f_eq_factorization_sum, hfac]
  rw [Finsupp.sum_of_support_subset _
    (Finsupp.support_add.trans (Finset.union_subset_union
      (Finsupp.support_add.trans (Finset.union_subset_union Finsupp.support_single_subset
        Finsupp.support_single_subset)) Finsupp.support_single_subset)) _ (by simp)]
  norm_num

example : f (1 / 2) 32 = (5 : ℝ) ^ (1 / 2 : ℝ) := by
  simpa using (f_two_pow (1 / 2 : ℝ) (by norm_num) 5)

private lemma odd_prime_three_le {p : ℕ} (hp : Nat.Prime p) (ho : Odd p) : 3 ≤ p := by
  rcases ho with ⟨t, ht⟩
  have hpge : 2 ≤ p := hp.two_le
  omega

lemma odd_part_lower (m : ℕ) (hm0 : m ≠ 0) (hodd : Odd m) :
    3 ^ m.primeFactorsList.length ≤ m := by
  calc
    3 ^ m.primeFactorsList.length ≤ m.primeFactorsList.prod := by
      apply List.pow_card_le_prod
      intro p hp
      apply odd_prime_three_le (Nat.prime_of_mem_primeFactorsList hp)
      have hpd : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
      by_contra hnot
      have hp2 : p = 2 :=
        ((Nat.prime_of_mem_primeFactorsList hp).eq_two_or_odd').resolve_right hnot
      subst p
      obtain ⟨c, hc⟩ := hpd
      rcases hodd with ⟨t, ht⟩
      omega
    _ = m := Nat.prod_primeFactorsList hm0

private lemma two_pow_succ_lt_three_pow {r : ℕ} (hr : 2 ≤ r) :
    2 ^ (r + 1) < 3 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      calc
        2 ^ (r.succ + 1) = 2 * 2 ^ (r + 1) := by
          simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.pow_succ, mul_comm]
        _ < 2 * 3 ^ r := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ ≤ 3 * 3 ^ r := Nat.mul_le_mul_right _ (by norm_num)
        _ = 3 ^ r.succ := by simp [Nat.pow_succ, Nat.succ_eq_add_one, mul_comm]

private theorem gap_odd {m : ℕ} (hm0 : m ≠ 0) (hodd : Odd m)
    (hm1 : m ≠ 1) (hm3 : m ≠ 3) :
    2 ^ (ArithmeticFunction.cardFactors m + 1) < m := by
  let r := m.primeFactorsList.length
  have hrΩ : ArithmeticFunction.cardFactors m = r := by
    simp [r, ArithmeticFunction.cardFactors_apply]
  rw [hrΩ]
  have hr0 : 0 < r := by
    by_contra h
    have hz : r = 0 := Nat.eq_zero_of_not_pos h
    have hnil : m.primeFactorsList = [] := by simpa [r] using hz
    have hm : m = 1 := by
      have := (Nat.primeFactorsList_eq_nil m).mp hnil
      exact this.resolve_left hm0
    exact hm1 hm
  rcases Nat.eq_zero_or_pos (r - 1) with hrsub | hrsub
  · have hr1 : r = 1 := by omega
    have hprime : Nat.Prime m := by
      apply (ArithmeticFunction.cardFactors_eq_one_iff_prime).mp
      simpa [hr1] using hrΩ
    have hmge : 5 ≤ m := by
      have hmge3 : 3 ≤ m := odd_prime_three_le hprime hodd
      have hmne3 : m ≠ 3 := hm3
      rcases hodd with ⟨t, ht⟩
      omega
    simpa [hr1] using (show 4 < m by omega)
  · have hr2 : 2 ≤ r := by omega
    exact (two_pow_succ_lt_three_pow hr2).trans_le (odd_part_lower m hm0 hodd)

/-- A nonzero number outside the candidate family exceeds a power of two with one more factor. -/
theorem gap_lemma {n : ℕ} (hn0 : n ≠ 0)
    (hnot_two : ∀ k : ℕ, n ≠ 2 ^ k)
    (hnot_three_two : ∀ k : ℕ, n ≠ 3 * 2 ^ k) :
    2 ^ (ArithmeticFunction.cardFactors n + 1) < n := by
  obtain ⟨a, m, hmodd, hdecomp⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  by_cases hm1 : m = 1
  · subst m
    exact (hnot_two a) (by simp [hdecomp]) |>.elim
  by_cases hm3 : m = 3
  · subst m
    exact (hnot_three_two a) (by simp [hdecomp, mul_comm]) |>.elim
  have hfac : ArithmeticFunction.cardFactors n =
      a + ArithmeticFunction.cardFactors m := by
    rw [hdecomp, ArithmeticFunction.cardFactors_mul]
    · simp [ArithmeticFunction.cardFactors_pow,
        ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]
    · positivity
    · exact hmodd.pos.ne'
  have hoddgap := gap_odd (m := m) hmodd.pos.ne' hmodd hm1 hm3
  rw [hfac, show a + ArithmeticFunction.cardFactors m + 1 =
    a + (ArithmeticFunction.cardFactors m + 1) by omega, Nat.pow_add]
  have hpowpos : 0 < 2 ^ a := by positivity
  simpa [hdecomp] using (Nat.mul_lt_mul_left hpowpos).mpr hoddgap

private lemma two_pow_cardFactors_le {m : ℕ} (hm0 : m ≠ 0) :
    2 ^ ArithmeticFunction.cardFactors m ≤ m := by
  have hlist : 2 ^ m.primeFactorsList.length ≤ m.primeFactorsList.prod := by
    apply List.pow_card_le_prod
    intro p hp
    exact (Nat.prime_of_mem_primeFactorsList hp).two_le
  simpa [ArithmeticFunction.cardFactors_apply] using
    hlist.trans_eq (Nat.prod_primeFactorsList hm0)

private lemma cardFactors_lt_of_lt_two_pow {m k : ℕ} (hm0 : m ≠ 0) (hmlt : m < 2 ^ k) :
    ArithmeticFunction.cardFactors m < k := by
  by_contra h
  have hkm : k ≤ ArithmeticFunction.cardFactors m := Nat.le_of_not_gt h
  have hpow : 2 ^ k ≤ 2 ^ ArithmeticFunction.cardFactors m :=
    Nat.pow_le_pow_right (by norm_num) hkm
  exact (not_lt_of_ge (hpow.trans (two_pow_cardFactors_le hm0))) hmlt

private lemma f_lt_on_ball {a b : ℕ} (hab : f 1 a < f 1 b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, dist x 1 < ε → f x a < f x b := by
  have hpos : 0 < (fun x : ℝ => f x b - f x a) 1 := sub_pos.mpr hab
  have hmem : (fun x : ℝ => f x b - f x a) ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds (1 : ℝ) :=
    ((continuousAt_f b).sub (continuousAt_f a)).preimage_mem_nhds (Ioi_mem_nhds hpos)
  rcases (Metric.mem_nhds_iff.mp hmem) with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx
  exact sub_pos.mp (hball (by exact Metric.mem_ball.mpr hx))

/-- Each power of two is a strict record throughout some left neighborhood of one. -/
theorem eventually_two_pow_record (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ x : ℝ, 1 - δ < x → x < 1 → StrictRecord x (2 ^ k) := by
  by_cases hk : k = 0
  · subst k
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro x _ _
    refine ⟨by norm_num, ?_⟩
    intro m hm1 hmlt
    omega
  have hnpos : 0 < 2 ^ k := by positivity
  let I : Finset ℕ := Finset.Ico 1 (2 ^ k)
  have hEach : ∀ m ∈ I, ∀ᶠ x : ℝ in nhds 1, f x m < f x (2 ^ k) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    have hmlt : m < 2 ^ k := (Finset.mem_Ico.mp hm).2
    have hΩ : ArithmeticFunction.cardFactors m < k :=
      cardFactors_lt_of_lt_two_pow (by omega) hmlt
    have hbase : f 1 m < f 1 (2 ^ k) := by
      rw [f_one, f_one, ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two]
      exact_mod_cast hΩ
    rcases f_lt_on_ball hbase with ⟨ε, hε, hεlt⟩
    exact (Metric.mem_nhds_iff.mpr ⟨ε, hε, by
      intro y hy
      exact hεlt y (Metric.mem_ball.mp hy)⟩)
  have hAll : ∀ᶠ x : ℝ in nhds 1, ∀ m ∈ I, f x m < f x (2 ^ k) :=
    (Finset.eventually_all I).2 hEach
  rcases (Metric.mem_nhds_iff.mp hAll) with ⟨ε, hε, hεball⟩
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro x hleft hright
  have hxball : x ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left (ε / 2) (1 / 2)]
  have hxall := hεball hxball
  have hn_one : 1 ≤ 2 ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  refine ⟨hn_one, ?_⟩
  intro m hm1 hmlt
  apply hxall m
  exact Finset.mem_Ico.mpr ⟨hm1, hmlt⟩

/-- A positive integer covered by the gap lemma eventually fails to be a strict record. -/
theorem eventually_not_record_of_gap {n : ℕ} (hn0 : n ≠ 0)
    (hnot_two : ∀ k : ℕ, n ≠ 2 ^ k)
    (hnot_three_two : ∀ k : ℕ, n ≠ 3 * 2 ^ k) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ x : ℝ, 1 - δ < x → x < 1 → ¬StrictRecord x n := by
  have hgap := gap_lemma hn0 hnot_two hnot_three_two
  let q : ℕ := 2 ^ (ArithmeticFunction.cardFactors n + 1)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hq_lt : q < n := by simpa [q] using hgap
  have hbase : f 1 n < f 1 q := by
    rw [f_one, f_one, ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two]
    norm_num
  rcases f_lt_on_ball hbase with ⟨ε, hε, hεlt⟩
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by dsimp [δ]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro x hleft hright hrec
  have hq_one : 1 ≤ q := by
    dsimp [q]
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hdist : dist x 1 < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left (ε / 2) (1 / 2)]
  have hbad := hrec.2 q hq_one hq_lt
  exact (not_lt_of_ge (le_of_lt (hεlt x hdist))) hbad

private lemma canonical_of_not_gap {m : ℕ} (hm0 : m ≠ 0)
    (hgap : ¬2 ^ (ArithmeticFunction.cardFactors m + 1) < m) :
    (∃ a : ℕ, m = 2 ^ a) ∨ ∃ a : ℕ, m = 3 * 2 ^ a := by
  by_contra h
  push Not at h
  exact hgap (gap_lemma hm0 h.1 h.2)

private lemma same_omega_lt_three_two {m k : ℕ} (hm0 : m ≠ 0)
    (hm_lt : m < 3 * 2 ^ k)
    (hm_omega : ArithmeticFunction.cardFactors m = k + 1) :
    m = 2 ^ (k + 1) := by
  have hnotgap : ¬2 ^ (ArithmeticFunction.cardFactors m + 1) < m := by
    rw [hm_omega]
    intro h
    have hpow : 4 * 2 ^ k < m := by
      norm_num [Nat.pow_add] at h ⊢
      omega
    have hpos : 0 < 2 ^ k := by positivity
    nlinarith [hm_lt, hpow]
  have hcan := canonical_of_not_gap hm0 hnotgap
  rcases hcan with hpow | hthree
  · rcases hpow with ⟨a, ha⟩
    subst m
    have ha : a = k + 1 := by
      simpa [ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two] using hm_omega
    subst a
    rfl
  · rcases hthree with ⟨a, ha⟩
    subst m
    have ha : a = k := by
      have hfac : ArithmeticFunction.cardFactors (3 * 2 ^ a) = a + 1 := by
        rw [ArithmeticFunction.cardFactors_mul (by norm_num) (pow_ne_zero _ (by norm_num))]
        simp [ArithmeticFunction.cardFactors_pow,
          ArithmeticFunction.cardFactors_apply_prime Nat.prime_two,
          ArithmeticFunction.cardFactors_apply_prime Nat.prime_three, Nat.add_comm]
      omega
    subst a
    omega

/-- Strict subadditivity of real powers on the positive integers when `0 < x < 1`. -/
theorem strict_subadditive_rpow {k : ℕ} (hk : 0 < k) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (k + 1 : ℝ) ^ x < (k : ℝ) ^ x + 1 := by
  have hc := (Real.strictConcaveOn_rpow hx0 hx1).2
  have h := hc (x := (k + 1 : ℝ)) (show (0 : ℝ) ≤ k + 1 by positivity)
    (y := (0 : ℝ)) (by norm_num) (show (k + 1 : ℝ) ≠ 0 by positivity)
    (a := (k : ℝ) / (k + 1)) (b := (1 : ℝ) / (k + 1))
    (by positivity) (by positivity) (by field_simp)
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h
  have harg : (k : ℝ) / (k + 1) * (k + 1) = (k : ℝ) := by
    field_simp
  simp only [Real.zero_rpow hx0.ne', mul_zero, add_zero] at h
  rw [harg] at h
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hscale : 0 < (k + 1 : ℝ) := by positivity
  have h' : (k : ℝ) * ((k + 1 : ℝ) ^ x) < (k : ℝ) ^ x * (k + 1) := by
    calc
      (k : ℝ) * ((k + 1 : ℝ) ^ x) =
          ((k : ℝ) * ((k + 1 : ℝ) ^ x) / (k + 1)) * (k + 1) := by field_simp
      _ < (k : ℝ) ^ x * (k + 1) := by
        have := mul_lt_mul_of_pos_right h hscale
        calc
          ((k : ℝ) * ((k + 1 : ℝ) ^ x) / (k + 1)) * (k + 1) =
              ((k : ℝ) / (k + 1) * ((k + 1 : ℝ) ^ x)) * (k + 1) := by ring
          _ < (k : ℝ) ^ x * (k + 1) := this
  have hpow : (k : ℝ) ^ (x - 1) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (show 1 ≤ k by omega)
    · linarith
  rw [Real.rpow_sub_one (by exact_mod_cast (show k ≠ 0 by omega))] at hpow
  calc
    (k + 1 : ℝ) ^ x < (k : ℝ) ^ x * (k + 1) / k := by
      apply (lt_div_iff₀ hkpos).2
      nlinarith [h']
    _ = (k : ℝ) ^ x + (k : ℝ) ^ x / k := by field_simp
    _ ≤ (k : ℝ) ^ x + 1 := by simpa [add_comm] using add_le_add_left hpow ((k : ℝ) ^ x)

private lemma cardFactors_le_of_lt_three_two {m k : ℕ} (hm0 : m ≠ 0)
    (hm_lt : m < 3 * 2 ^ k) : ArithmeticFunction.cardFactors m ≤ k + 1 := by
  by_contra h
  have hkm : k + 2 ≤ ArithmeticFunction.cardFactors m := by omega
  have hpow : 2 ^ (k + 2) ≤ 2 ^ ArithmeticFunction.cardFactors m :=
    Nat.pow_le_pow_right (by norm_num) hkm
  have hpowm : 2 ^ (k + 2) ≤ m := hpow.trans (two_pow_cardFactors_le hm0)
  have hupper : m < 2 ^ (k + 2) := by
    have hpos : 0 < 2 ^ k := by positivity
    have hlt : 3 * 2 ^ k < 4 * 2 ^ k := by nlinarith
    calc
      m < 3 * 2 ^ k := hm_lt
      _ < 4 * 2 ^ k := hlt
      _ = 2 ^ (k + 2) := by
        norm_num [Nat.pow_add]
        omega
  exact (not_lt_of_ge hpowm) hupper

/-- Three is never a strict record at a positive exponent because it ties with two. -/
theorem not_record_three : ∀ x : ℝ, 0 < x → ¬StrictRecord x 3 := by
  intro x hx hrec
  have hbad := hrec.2 2 (by norm_num) (by norm_num)
  have heq : f x 2 = f x 3 := by
    calc
      f x 2 = (1 : ℝ) ^ x := by simpa using (f_two_pow x hx 1)
      _ = f x 3 := by
        simpa [Real.zero_rpow hx.ne'] using (f_three_two_pow x hx 0).symm
  exact (ne_of_lt hbad) heq

/-- Three times a positive power of two is a strict record near one from the left. -/
theorem eventually_three_two_record {k : ℕ} (hk : 0 < k) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ x : ℝ, 1 - δ < x → x < 1 → StrictRecord x (3 * 2 ^ k) := by
  let n : ℕ := 3 * 2 ^ k
  have hnpos : 0 < n := by dsimp [n]; positivity
  have hΩn : ArithmeticFunction.cardFactors n = k + 1 := by
    dsimp [n]
    rw [ArithmeticFunction.cardFactors_mul (by norm_num) (pow_ne_zero _ (by norm_num))]
    simp [ArithmeticFunction.cardFactors_pow,
      ArithmeticFunction.cardFactors_apply_prime Nat.prime_two,
      ArithmeticFunction.cardFactors_apply_prime Nat.prime_three, Nat.add_comm]
  let I : Finset ℕ := Finset.Ico 1 n
  have hEach : ∀ m ∈ I, ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1),
      f x m < f x n := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    have hmlt : m < n := (Finset.mem_Ico.mp hm).2
    have hm0 : m ≠ 0 := by omega
    have hΩle : ArithmeticFunction.cardFactors m ≤ k + 1 :=
      cardFactors_le_of_lt_three_two hm0 (by simpa [n] using hmlt)
    by_cases hΩlt : ArithmeticFunction.cardFactors m < k + 1
    · have hbase : f 1 m < f 1 n := by
        rw [f_one, f_one, hΩn]
        exact_mod_cast hΩlt
      rcases f_lt_on_ball hbase with ⟨ε, hε, hεlt⟩
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Metric.mem_nhds_iff.mpr ⟨ε, hε, by
          intro y hy
          exact hεlt y (Metric.mem_ball.mp hy)⟩)
    · have hΩeq : ArithmeticFunction.cardFactors m = k + 1 := by omega
      have hm_eq : m = 2 ^ (k + 1) :=
        same_omega_lt_three_two hm0 (by simpa [n] using hmlt) hΩeq
      apply eventually_nhdsWithin_iff.mpr
      filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx0
      intro hx
      have hxlt : x < 1 := hx
      rw [hm_eq]
      dsimp [n]
      rw [f_two_pow x hx0, f_three_two_pow x hx0 k]
      simp only [Real.one_rpow]
      simpa [Nat.cast_add, add_comm] using strict_subadditive_rpow hk hx0 hxlt
  have hAll : ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1), ∀ m ∈ I, f x m < f x n :=
    (Finset.eventually_all I).2 hEach
  have hAll' : ∀ᶠ x : ℝ in nhds 1,
      x ∈ Set.Iio 1 → ∀ m ∈ I, f x m < f x n :=
    eventually_nhdsWithin_iff.mp hAll
  rcases (Metric.mem_nhds_iff.mp hAll') with ⟨ε, hε, hεball⟩
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by dsimp [δ]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro x hleft hright
  have hxball : x ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left (ε / 2) (1 / 2)]
  have hxall := hεball hxball (by exact hright)
  have hn_one : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by dsimp [n]; positivity)
  refine ⟨hn_one, ?_⟩
  intro m hm1 hmlt
  apply hxall m
  exact Finset.mem_Ico.mpr ⟨hm1, by simpa [n] using hmlt⟩

/-- The A029744 candidate family with the exceptional term `3` removed. -/
def Candidate (n : ℕ) : Prop :=
  (∃ k : ℕ, n = 2 ^ k) ∨ ∃ k : ℕ, 1 ≤ k ∧ n = 3 * 2 ^ k

/-- The A384669 endpoint conjecture at one, in its pointwise eventual formulation. -/
theorem a384669_endpoint_limit_one {n : ℕ} (hn : 1 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ x : ℝ, 1 - δ < x → x < 1 →
        (StrictRecord x n ↔
          (∃ k : ℕ, n = 2 ^ k) ∨ ∃ k : ℕ, 1 ≤ k ∧ n = 3 * 2 ^ k) := by
  by_cases hp : ∃ k : ℕ, n = 2 ^ k
  · rcases hp with ⟨k, hk⟩
    rcases eventually_two_pow_record k with ⟨δ, hδ, hδ1, hrec⟩
    refine ⟨δ, hδ, hδ1, ?_⟩
    intro x hleft hright
    have hr : StrictRecord x (2 ^ k) := hrec x hleft hright
    constructor
    · intro _
      exact Or.inl ⟨k, hk⟩
    · intro _
      simpa [hk] using hr
  · by_cases h3p : ∃ k : ℕ, 1 ≤ k ∧ n = 3 * 2 ^ k
    · rcases h3p with ⟨k, hkpos, hk⟩
      rcases eventually_three_two_record hkpos with ⟨δ, hδ, hδ1, hrec⟩
      refine ⟨δ, hδ, hδ1, ?_⟩
      intro x hleft hright
      have hr : StrictRecord x (3 * 2 ^ k) := hrec x hleft hright
      constructor
      · intro _
        exact Or.inr ⟨k, hkpos, hk⟩
      · intro _
        simpa [hk] using hr
    · by_cases hn3 : n = 3
      · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
        intro x hleft hright
        have hxpos : 0 < x := by linarith
        have hnr : ¬StrictRecord x n := by
          simpa [hn3] using not_record_three x hxpos
        have hcfalse : ¬((∃ k : ℕ, n = 2 ^ k) ∨
            ∃ k : ℕ, 1 ≤ k ∧ n = 3 * 2 ^ k) := by
          intro hc
          rcases hc with hc | hc
          · exact hp hc
          · exact h3p hc
        constructor
        · intro hs
          exact (hnr hs).elim
        · intro hc
          exact (hcfalse hc).elim
      · have hn0 : n ≠ 0 := by omega
        have hnot_two : ∀ k : ℕ, n ≠ 2 ^ k := by
          intro k hk
          exact hp ⟨k, hk⟩
        have hnot_three_two : ∀ k : ℕ, n ≠ 3 * 2 ^ k := by
          intro k hk
          by_cases hk0 : k = 0
          · apply hn3
            simpa [hk0] using hk
          · apply h3p
            exact ⟨k, Nat.one_le_iff_ne_zero.mpr hk0, hk⟩
        rcases eventually_not_record_of_gap hn0 hnot_two hnot_three_two with
          ⟨δ, hδ, hδ1, hnr⟩
        refine ⟨δ, hδ, hδ1, ?_⟩
        intro x hleft hright
        have hnr' : ¬StrictRecord x n := hnr x hleft hright
        have hcfalse : ¬((∃ k : ℕ, n = 2 ^ k) ∨
            ∃ k : ℕ, 1 ≤ k ∧ n = 3 * 2 ^ k) := by
          intro hc
          rcases hc with hc | hc
          · exact hp hc
          · exact h3p hc
        constructor
        · intro hs
          exact (hnr' hs).elim
        · intro hc
          exact (hcfalse hc).elim

example : f 1 12 = 3 := by
  rw [show (12 : ℕ) = 3 * 2 ^ 2 by norm_num, f_three_two_pow 1 (by norm_num) 2]
  norm_num

example : ¬Candidate 5 := by
  intro h
  rcases h with ⟨k, hk⟩ | ⟨k, hkpos, hk⟩
  · cases k with
    | zero => norm_num at hk
    | succ k =>
      have hmod := congrArg (fun n : ℕ => n % 2) hk
      norm_num [Nat.pow_succ] at hmod
  · cases k with
    | zero => omega
    | succ k =>
      have hmod := congrArg (fun n : ℕ => n % 2) hk
      norm_num [Nat.pow_succ, Nat.mul_mod] at hmod

example : Candidate 6 := by
  exact Or.inr ⟨1, by norm_num, by norm_num⟩

#print axioms f_one
#print axioms gap_lemma
#print axioms eventually_not_record_of_gap
#print axioms eventually_two_pow_record
#print axioms eventually_three_two_record
#print axioms strict_subadditive_rpow
#print axioms not_record_three
#print axioms a384669_endpoint_limit_one

end D5.S3.Factorization.PrimeExponentRecordLimitOne
