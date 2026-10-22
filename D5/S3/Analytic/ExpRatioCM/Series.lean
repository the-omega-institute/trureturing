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

end D5.S3.Analytic.ExpRatioCM.Series
