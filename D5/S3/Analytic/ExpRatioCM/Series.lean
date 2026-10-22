/- GID: D5/S3/Analytic/ExpRatioCM/Series
   generality: G
   mirror-B: D5/B/S3/Analytic/ExpRatioCM/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries, mathlib/module/Mathlib.Analysis.SpecificLimits.Normed, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exponential moment expansions and consecutive signed derivative quotient coefficients. -/

import D5.S3.Analytic.ExpRatioCM.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped BigOperators Topology
open Filter Set
open D5.S3.Analytic.ExpRatioCM.Defs
namespace D5.S3.Analytic.ExpRatioCM.Series

/-- Iteration of signed derivatives respects addition of the derivative orders. -/
theorem iteratedDeriv_F (i k : ℕ) (t : ℝ) :
    iteratedDeriv k (F i) t = (-1) ^ k * F (i + k) t := by
  change iteratedDeriv k (fun x => (-1 : ℝ) ^ i *
    iteratedDeriv i (fun s : ℝ => 1 / (Real.exp s - 1)) x) t = _
  simp only [iteratedDeriv_const_mul_field, F, iteratedDeriv_eq_iterate]
  rw [← Function.iterate_add_apply]
  rw [show k + i = i + k by omega, pow_add]
  have h : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination (-( (-1 : ℝ) ^ i *
    (deriv^[i + k]) (fun s : ℝ => 1 / (Real.exp s - 1)) t)) * h

private lemma reciprocal_eq {t : ℝ} (ht : 0 < t) :
    1 / (1 - Real.exp (-t)) = 1 + 1 / (Real.exp t - 1) := by
  have he : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have h1 : Real.exp t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr ht))
  rw [Real.exp_neg]
  field_simp
  <;> ring

/-- The zeroth second-family function has one additional constant term. -/
theorem G_zero_eq {t : ℝ} (ht : 0 < t) : G 0 t = 1 + F 0 t := by
  simpa [G, F] using reciprocal_eq ht

/-- The positive-order signed derivative families agree on the positive half-line. -/
theorem G_eq_F {i : ℕ} (hi : 1 ≤ i) {t : ℝ} (ht : 0 < t) : G i t = F i t := by
  have he : (fun s : ℝ => 1 / (1 - Real.exp (-s))) =ᶠ[𝓝 t]
      (fun s => 1 + 1 / (Real.exp s - 1)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact reciprocal_eq hs
  rw [G, he.iteratedDeriv_eq i, iteratedDeriv_const_add (by omega : 0 < i), F]

/-- Smoothness of every first-family signed derivative on the positive half-line. -/
theorem contDiffOn_F (i : ℕ) : ContDiffOn ℝ ⊤ (F i) (Ioi 0) := by
  have hbase : ContDiffOn ℝ ⊤ (fun s : ℝ => 1 / (Real.exp s - 1)) (Ioi 0) := by
    apply contDiffOn_const.div (Real.contDiff_exp.contDiffOn.sub contDiffOn_const)
    intro x hx
    exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr hx))
  have hd (j : ℕ) : ContDiffOn ℝ ⊤
      (iteratedDeriv j (fun s : ℝ => 1 / (Real.exp s - 1))) (Ioi 0) := by
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by simp)
  exact contDiffOn_const.mul (hd i)

private def expMoment (i : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ i * Real.exp (-((n + 1 : ℕ) : ℝ) * t)

private lemma summable_expMoment (i : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ i *
      Real.exp (-((n + 1 : ℕ) : ℝ) * t)) := by
  have h := (Real.summable_pow_mul_exp_neg_nat_mul i ht).comp_injective
    (add_left_injective 1)
  convert h using 1
  ext n
  congr 2
  ring

private lemma hasDerivAt_expMoment (i : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (expMoment i) (-expMoment (i + 1) t) t := by
  let d : ℕ → ℝ → ℝ := fun n x =>
    -(((n + 1 : ℕ) : ℝ) ^ (i + 1) * Real.exp (-((n + 1 : ℕ) : ℝ) * x))
  have hd (n : ℕ) (x : ℝ) : HasDerivAt
      (fun x : ℝ => ((n + 1 : ℕ) : ℝ) ^ i *
        Real.exp (-((n + 1 : ℕ) : ℝ) * x)) (d n x) x := by
    convert (((hasDerivAt_id x).const_mul (-((n + 1 : ℕ) : ℝ))).exp.const_mul
      (((n + 1 : ℕ) : ℝ) ^ i)) using 1 <;> dsimp [d] <;> ring
  have h := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (i + 1) *
      Real.exp (-((n + 1 : ℕ) : ℝ) * (t / 2)))
    (t := Ioi (t / 2)) (y₀ := t) (y := t)
    (summable_expMoment (i + 1) (by linarith : 0 < t / 2)) isOpen_Ioi
    (convex_Ioi (t / 2)).isPreconnected (fun n x _ => hd n x)
    (fun n x hx => ?_) (by simpa using (show t / 2 < t by linarith))
    (summable_expMoment i ht) (by simpa using (show t / 2 < t by linarith))
  · convert h using 1 <;> first | rfl | simp only [expMoment, d, tsum_neg]
  · dsimp [d]
    rw [abs_neg, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (le_of_lt hx) (neg_nonpos.mpr (Nat.cast_nonneg _))

private lemma expMoment_zero {t : ℝ} (ht : 0 < t) :
    expMoment 0 t = 1 / (Real.exp t - 1) := by
  have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := (hasSum_geometric_of_lt_one (Real.exp_nonneg (-t)) he).mul_left
    (Real.exp (-t))
  have hexp (n : ℕ) : Real.exp (-((n + 1 : ℕ) : ℝ) * t) =
      Real.exp (-t) * Real.exp (-t) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  simp only [expMoment, pow_zero, one_mul, hexp]
  rw [hs.tsum_eq, Real.exp_neg]
  have hne : Real.exp t - 1 ≠ 0 := sub_ne_zero.mpr
    (ne_of_gt (Real.one_lt_exp_iff.mpr ht))
  field_simp
  <;> ring

/-- The signed derivatives are polynomially weighted exponential sums. -/
theorem F_eq_tsum (i : ℕ) {t : ℝ} (ht : 0 < t) :
    F i t = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ i *
      Real.exp (-((n + 1 : ℕ) : ℝ) * t) := by
  change F i t = expMoment i t
  induction i generalizing t with
  | zero => simpa [F] using (expMoment_zero ht).symm
  | succ i ih =>
    have he : F i =ᶠ[𝓝 t] expMoment i := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact ih hx
    have hd := (he.deriv_eq).trans (hasDerivAt_expMoment i ht).deriv
    have hf := iteratedDeriv_F i 1 t
    simp only [iteratedDeriv_one, pow_one, neg_mul, one_mul] at hf
    linarith

/-- All the exponential moments are strictly positive on the positive half-line. -/
theorem F_pos (i : ℕ) {t : ℝ} (ht : 0 < t) : 0 < F i t := by
  rw [F_eq_tsum i ht]
  exact (summable_expMoment i ht).tsum_pos (fun n => by positivity) 0 (by positivity)

/-- All first-family consecutive ratios are smooth on the positive half-line. -/
theorem contDiffOn_ratioF (i : ℕ) : ContDiffOn ℝ ⊤ (ratioF i) (Ioi 0) := by
  exact (contDiffOn_F (i + 1)).div (contDiffOn_F i) (fun x hx => (F_pos i hx).ne')

/-- The two consecutive ratios coincide for positive indices. -/
theorem ratioG_eq_ratioF {i : ℕ} (hi : 1 ≤ i) {t : ℝ} (ht : 0 < t) :
    ratioG i t = ratioF i t := by
  simp only [ratioG, ratioF, G_eq_F hi ht, G_eq_F (by omega : 1 ≤ i + 1) ht]

/-- All second-family consecutive ratios are smooth on the positive half-line. -/
theorem contDiffOn_ratioG (i : ℕ) : ContDiffOn ℝ ⊤ (ratioG i) (Ioi 0) := by
  have hg (j : ℕ) : ContDiffOn ℝ ⊤ (G j) (Ioi 0) := by
    cases j with
    | zero =>
      exact (contDiffOn_const.add (contDiffOn_F 0)).congr (fun x hx => G_zero_eq hx)
    | succ j =>
      exact (contDiffOn_F (j + 1)).congr (fun x hx => G_eq_F (by omega) hx)
  exact (hg (i + 1)).div (hg i) (by
    intro x hx
    cases i with
    | zero => rw [G_zero_eq hx]; linarith [F_pos 0 hx]
    | succ i => rw [G_eq_F (by omega : 1 ≤ i + 1) hx]; exact (F_pos _ hx).ne')

/-- Coefficients of the quotient of consecutive exponential moment series. -/
def quotCoeff (i : ℕ) (n : ℕ) : ℝ :=
  if _hn : n = 0 then 1 else
    ((n + 1 : ℕ) : ℝ) ^ (i + 1) -
      ∑ j ∈ Finset.range n, ((j + 2 : ℕ) : ℝ) ^ i * quotCoeff i (n - 1 - j)
termination_by n

private lemma quotCoeff_zero (i : ℕ) : quotCoeff i 0 = 1 := by
  rw [quotCoeff]; simp

private lemma quotCoeff_succ (i n : ℕ) :
    quotCoeff i (n + 1) = ((n + 2 : ℕ) : ℝ) ^ (i + 1) -
      ∑ j ∈ Finset.range (n + 1), ((j + 2 : ℕ) : ℝ) ^ i * quotCoeff i (n - j) := by
  rw [quotCoeff]
  simp [add_assoc]

private lemma quotCoeff_one (i : ℕ) : quotCoeff i 1 = (2 : ℝ) ^ i := by
  rw [quotCoeff_succ i 0]
  simp [quotCoeff_zero, pow_succ]
  ring

/-- The second quotient coefficient is the difference of two exponential sequences. -/
theorem quotCoeff_two (i : ℕ) : quotCoeff i 2 = 2 * (3 : ℝ) ^ i - (4 : ℝ) ^ i := by
  rw [quotCoeff_succ i 1]
  simp [Finset.sum_range_succ, quotCoeff_zero, quotCoeff_one, pow_succ]
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  ring

private lemma moment_coefficient_le (i n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ i ≤ ((2 : ℝ) ^ i) ^ n := by
  have hn : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    simpa only [mul_one, Nat.cast_add, Nat.cast_one, add_comm, show (1 : ℝ) + 1 = 2 by norm_num] using (one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1) n)
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ)) hn i
  calc
    _ ≤ ((2 : ℝ) ^ n) ^ i := h
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

private lemma scaled_power (A B : ℝ) (hB : B ≠ 0) (n j : ℕ) (hj : j ≤ n) :
    A ^ j * B ^ (n - j) = B ^ n * (A / B) ^ j := by
  rw [div_pow, pow_sub₀ B hB hj]
  field_simp

/-- A geometric bound for every quotient coefficient. -/
theorem abs_quotCoeff_le (i n : ℕ) : |quotCoeff i n| ≤ ((2 : ℝ) ^ (i + 2)) ^ n := by
  let B : ℝ := (2 : ℝ) ^ (i + 2)
  have hB : 0 < B := by dsimp [B]; positivity
  have hrat : (2 : ℝ) ^ i / B = 1 / 4 := by dsimp [B]; rw [pow_add]; norm_num; field_simp
  have hrat' : (2 : ℝ) ^ (i + 1) / B = 1 / 2 := by
    dsimp [B]
    simp only [pow_succ]
    field_simp
    <;> ring
  change |quotCoeff i n| ≤ B ^ n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [quotCoeff_zero]
    | succ n =>
      rw [quotCoeff_succ]
      calc
        |((n + 2 : ℕ) : ℝ) ^ (i + 1) -
            ∑ j ∈ Finset.range (n + 1), ((j + 2 : ℕ) : ℝ) ^ i * quotCoeff i (n - j)|
          ≤ ((n + 2 : ℕ) : ℝ) ^ (i + 1) +
            ∑ j ∈ Finset.range (n + 1), ((j + 2 : ℕ) : ℝ) ^ i * |quotCoeff i (n - j)| := by
              exact (abs_sub _ _).trans (add_le_add
                (le_of_eq (abs_of_nonneg (by positivity)))
                ((Finset.abs_sum_le_sum_abs _ _).trans_eq (by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [abs_mul, abs_of_nonneg (by positivity)])))
        _ ≤ B ^ (n + 1) * (1 / 2 : ℝ) ^ (n + 1) +
            ∑ j ∈ Finset.range (n + 1), B ^ (n + 1) * (1 / 4 : ℝ) ^ (j + 1) := by
              apply add_le_add
              · calc
                  _ ≤ ((2 : ℝ) ^ (i + 1)) ^ (n + 1) := by
                    simpa [Nat.add_assoc] using moment_coefficient_le (i + 1) (n + 1)
                  _ = _ := by
                    simpa [hrat'] using scaled_power ((2 : ℝ) ^ (i + 1)) B hB.ne' (n + 1) (n + 1) le_rfl
              · apply Finset.sum_le_sum
                intro j hj
                have hjn : j ≤ n := by simpa using hj
                calc
                  _ ≤ (((2 : ℝ) ^ i) ^ (j + 1)) * B ^ (n - j) :=
                    mul_le_mul (by simpa [Nat.add_assoc] using moment_coefficient_le i (j + 1))
                      (ih (n - j) (by omega)) (abs_nonneg _) (by positivity)
                  _ = _ := by
                    simpa [hrat, show n + 1 - (j + 1) = n - j by omega] using
                      scaled_power ((2 : ℝ) ^ i) B hB.ne' (n + 1) (j + 1) (by omega)
        _ ≤ B ^ (n + 1) * (1 / 2) + B ^ (n + 1) * (1 / 3) := by
              rw [← Finset.mul_sum]
              apply add_le_add
              · apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
                  (by norm_num) (by omega : 1 ≤ n + 1)).trans_eq (pow_one _)
              · apply mul_le_mul_of_nonneg_left _ (by positivity)
                have hs := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
                  (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (1 / 4 : ℝ)
                have hh := hs.summable.sum_le_tsum (Finset.range (n + 1))
                  (fun j _ => by positivity)
                rw [hs.tsum_eq] at hh
                norm_num at hh
                simpa only [pow_succ'] using hh
        _ ≤ B ^ (n + 1) := by nlinarith [pow_pos hB (n + 1)]

private def weightedSeries (b : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, b n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * t)

private lemma summable_weighted {b : ℕ → ℝ} {B : ℝ} (hB : 0 < B)
    (hb : ∀ n, |b n| ≤ B ^ n) (k : ℕ) {t : ℝ} (ht : Real.log B < t) :
    Summable (fun n : ℕ => ‖b n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * t)‖) := by
  have hr : B * Real.exp (-t) < 1 := by
    calc
      _ = Real.exp (Real.log B - t) := by rw [Real.exp_sub, Real.exp_log hB, Real.exp_neg]; rfl
      _ < 1 := Real.exp_lt_one_iff.mpr (sub_neg.mpr ht)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _
    (summable_pow_mul_geometric_of_norm_lt_one k (r := B * Real.exp (-t))
      (by simpa only [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < B * Real.exp (-t))] using hr))
  intro n
  simp only [norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ B ^ n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * t) := by gcongr; exact hb n
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      rw [show (n : ℝ) * (-t) = -(n : ℝ) * t by ring]
      ring

private lemma hasDerivAt_weighted {b : ℕ → ℝ} {B : ℝ} (hB : 0 < B)
    (hb : ∀ n, |b n| ≤ B ^ n) (k : ℕ) {t : ℝ} (ht : Real.log B < t) :
    HasDerivAt (weightedSeries b k) (-weightedSeries b (k + 1) t) t := by
  let a : ℝ := (Real.log B + t) / 2
  have ha : Real.log B < a := by dsimp [a]; linarith
  have hat : a < t := by dsimp [a]; linarith
  let d : ℕ → ℝ → ℝ := fun n x => -(b n * (n : ℝ) ^ (k + 1) * Real.exp (-(n : ℝ) * x))
  have hd (n : ℕ) (x : ℝ) : HasDerivAt
      (fun x : ℝ => b n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * x)) (d n x) x := by
    convert (((hasDerivAt_id x).const_mul (-(n : ℝ))).exp.const_mul
      (b n * (n : ℝ) ^ k)) using 1 <;> dsimp [d] <;> ring
  have h := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => ‖b n * (n : ℝ) ^ (k + 1) * Real.exp (-(n : ℝ) * a)‖)
    (t := Ioi a) (y₀ := t) (y := t) (summable_weighted hB hb (k + 1) ha)
    isOpen_Ioi (convex_Ioi a).isPreconnected (fun n x _ => hd n x)
    (fun n x hx => ?_) hat ((summable_weighted hB hb k ht).of_norm) hat
  · convert h using 1 <;> first | rfl | simp only [weightedSeries, d, tsum_neg]
  · dsimp [d]
    simp only [abs_neg, norm_neg, norm_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (le_of_lt hx) (neg_nonpos.mpr (Nat.cast_nonneg _))

private lemma iteratedDeriv_weighted {b : ℕ → ℝ} {B : ℝ} (hB : 0 < B)
    (hb : ∀ n, |b n| ≤ B ^ n) (k : ℕ) {t : ℝ} (ht : Real.log B < t) :
    iteratedDeriv k (weightedSeries b 0) t = (-1) ^ k * weightedSeries b k t := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (weightedSeries b 0) =ᶠ[𝓝 t]
        (fun x => (-1 : ℝ) ^ k * weightedSeries b k x) := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact ih hx
    rw [he.deriv_eq, ((hasDerivAt_weighted hB hb k ht).const_mul ((-1 : ℝ) ^ k)).deriv]
    simp only [pow_succ]
    ring

private lemma quotient_convolution (i n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ((j + 1 : ℕ) : ℝ) ^ i * quotCoeff i (n - j)) =
      ((n + 1 : ℕ) : ℝ) ^ (i + 1) := by
  cases n with
  | zero => simp [quotCoeff_zero]
  | succ n =>
    rw [Finset.sum_range_succ']
    have h := quotCoeff_succ i n
    simp only [Nat.add_sub_add_right, Nat.sub_zero, Nat.cast_one, one_pow, one_mul] at *
    simpa [Nat.add_assoc, add_assoc, add_comm, add_left_comm] using (eq_sub_iff_add_eq.mp h)

private def denominatorSeries (i : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ i * Real.exp (-(n : ℝ) * t)

private lemma denominator_term (i n : ℕ) (t : ℝ) :
    ((n + 1 : ℕ) : ℝ) ^ i * Real.exp (-(n : ℝ) * t) =
      Real.exp t * (((n + 1 : ℕ) : ℝ) ^ i * Real.exp (-((n + 1 : ℕ) : ℝ) * t)) := by
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  push_cast
  ring

private lemma summable_denominator (i : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ‖((n + 1 : ℕ) : ℝ) ^ i * Real.exp (-(n : ℝ) * t)‖) := by
  apply ((summable_expMoment i ht).mul_left (Real.exp t)).congr
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), denominator_term]

private lemma denominator_eq (i : ℕ) {t : ℝ} (ht : 0 < t) :
    denominatorSeries i t = Real.exp t * F i t := by
  simp_rw [denominatorSeries, denominator_term]
  rw [tsum_mul_left, ← F_eq_tsum i ht]

/-- On an explicit right half-line the quotient has its coefficient expansion. -/
theorem ratioF_eq_tsum (i : ℕ) {t : ℝ} (ht : Real.log ((2 : ℝ) ^ (i + 2)) < t) :
    ratioF i t = ∑' n : ℕ, quotCoeff i n * Real.exp (-(n : ℝ) * t) := by
  let B : ℝ := (2 : ℝ) ^ (i + 2)
  have hB : 0 < B := by dsimp [B]; positivity
  have ht0 : 0 < t := lt_of_le_of_lt (Real.log_nonneg (one_le_pow₀ (by norm_num))) ht
  have hb : ∀ n, |quotCoeff i n| ≤ B ^ n := abs_quotCoeff_le i
  have hs := summable_weighted hB hb 0 ht
  simp only [pow_zero, mul_one] at hs
  have hp := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (summable_denominator i ht0) hs
  have hc (n : ℕ) :
      (∑ j ∈ Finset.range (n + 1),
        (((j + 1 : ℕ) : ℝ) ^ i * Real.exp (-(j : ℝ) * t)) *
          (quotCoeff i (n - j) * Real.exp (-((n - j : ℕ) : ℝ) * t))) =
        ((n + 1 : ℕ) : ℝ) ^ (i + 1) * Real.exp (-(n : ℝ) * t) := by
    rw [← quotient_convolution i n, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using hj
    rw [mul_mul_mul_comm, ← Real.exp_add]
    rw [Nat.cast_sub hjn]
    congr 2
    ring
  simp_rw [hc] at hp
  change denominatorSeries i t * (∑' n : ℕ, quotCoeff i n * Real.exp (-(n : ℝ) * t)) =
    denominatorSeries (i + 1) t at hp
  rw [denominator_eq i ht0, denominator_eq (i + 1) ht0] at hp
  apply (div_eq_iff (F_pos i ht0).ne').2
  apply (mul_left_cancel₀ (Real.exp_pos t).ne')
  nlinarith [hp]

/-- Every positive-order signed derivative is the weighted quotient series. -/
theorem iteratedDeriv_ratioF (i k : ℕ) (hk : 1 ≤ k) {t : ℝ}
    (ht : Real.log ((2 : ℝ) ^ (i + 2)) < t) :
    (-1) ^ k * iteratedDeriv k (ratioF i) t =
      ∑' n : ℕ, quotCoeff i n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * t) := by
  have he : ratioF i =ᶠ[𝓝 t] weightedSeries (quotCoeff i) 0 := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    simpa only [weightedSeries, pow_zero, mul_one] using ratioF_eq_tsum i hx
  rw [he.iteratedDeriv_eq k, iteratedDeriv_weighted (by positivity : (0 : ℝ) < 2 ^ (i + 2))
    (abs_quotCoeff_le i) k ht]
  have hs : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  simpa only [← mul_assoc, hs, one_mul, weightedSeries]

end D5.S3.Analytic.ExpRatioCM.Series
