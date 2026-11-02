/- Uncompiled source preparation; internal part of the full original actual-K certificate.
No standalone helper admission is requested. -/
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

variable {I : Type u} [Fintype I]

/- Complete positive mixture. The range M is the head k=1,...,M, since
   the actual trivialCoeff index n represents k=n+1. -/
def rate (n : ℕ) : ℝ := 2 * ((n : ℝ) + 1) + 1 / 2
private def mixtureTerm (n : ℕ) (t : ℝ) : ℝ :=
  trivialCoeff n * Real.exp (-rate n * |t|)
private def headMass (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M, 2 * rate n * trivialCoeff n
private def headLoss (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M, 2 * rate n ^ 3 * trivialCoeff n

private lemma mixture_hasSum (t : ℝ) : HasSum (fun n => mixtureTerm n t) (P t) := by
  have h := (trivialT_summable (abs_nonneg t)).hasSum.mul_left (Real.exp (-|t| / 2))
  change HasSum (fun n => Real.exp (-|t| / 2) *
    (trivialCoeff n * Real.exp (-(2 * ((n : ℝ) + 1)) * |t|))) (P t) at h
  convert h using 1
  funext n
  dsimp [mixtureTerm, rate]
  calc
    _ = trivialCoeff n * Real.exp (-|t| / 2 + -(2 * ((n : ℝ) + 1)) * |t|) := by
      congr 2 <;> ring
    _ = _ := by rw [Real.exp_add]; ring

private lemma mixture_norm_summable (t : ℝ) : Summable (fun n => ‖mixtureTerm n t‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ trivialCoeff_hasSum.summable
  intro n
  have hn : 0 ≤ mixtureTerm n t :=
    mul_nonneg (trivialCoeff_nonneg n) (Real.exp_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact mul_le_of_le_one_right (trivialCoeff_nonneg n)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by dsimp [rate]; positivity)) (abs_nonneg t)))

private lemma quadratic_mixture_hasSum (x : I → ℝ) (a : I → ℂ) :
    HasSum (fun n => quadratic x a (mixtureTerm n)) (quadratic x a P) := by
  classical
  have h (i j : I) : HasSum
      (fun n => star (a i) * a j * (mixtureTerm n (x i - x j) : ℂ))
      (star (a i) * a j * (P (x i - x j) : ℂ)) :=
    (Complex.hasSum_ofReal.mpr (mixture_hasSum (x i - x j))).mul_left _
  exact hasSum_sum (fun i hi => hasSum_sum (fun j hj => h i j))

private lemma quadratic_mixture_abs (x : I → ℝ) (a : I → ℂ) :
    Summable (fun n => ‖quadratic x a (mixtureTerm n)‖) := by
  have h (i j : I) : Summable
      (fun n => ‖star (a i) * a j * (mixtureTerm n (x i - x j) : ℂ)‖) := by
    simpa only [norm_mul, Complex.norm_real] using
      (mixture_norm_summable (x i - x j)).mul_left (‖star (a i) * a j‖)
  have hsum := summable_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    summable_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) => h i j))
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hsum
  intro n
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => norm_sum_le _ _))

private lemma quadratic_mixture_nonneg (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (n : ℕ) : 0 ≤ (quadratic x a (mixtureTerm n)).re := by
  have hl : 0 < rate n := by dsimp [rate]; positivity
  have hdiam (i j : I) : |x i - x j| ≤ D :=
    abs_le.mpr ⟨by linarith [(hx i).1, (hx j).2], by linarith [(hx i).2, (hx j).1]⟩
  have h := exponential_prefix_coercivity x a ha (rate n) D hl hD hdiam
  have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
  have hq : 0 ≤ (quadratic x a (fun t => Real.exp (-rate n * |t|))).re := by
    exact le_trans (by positivity) h
  have hid : (quadratic x a (mixtureTerm n)).re = trivialCoeff n *
      (quadratic x a (fun t => Real.exp (-rate n * |t|))).re := by
    simp only [quadratic, mixtureTerm, Complex.ofReal_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sum_re,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hid]
  exact mul_nonneg (trivialCoeff_nonneg n) hq

private lemma head_below_full (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (M : ℕ) :
    (∑ n ∈ Finset.range M, (quadratic x a (mixtureTerm n)).re) ≤ (quadratic x a P).re := by
  have h := Complex.hasSum_re (quadratic_mixture_hasSum x a)
  have hs := (quadratic_mixture_abs x a).of_norm
  have hr := (Complex.hasSum_re hs.hasSum).summable
  rw [← h.tsum_eq]
  exact hr.sum_le_tsum (Finset.range M)
    (fun n hn => quadratic_mixture_nonneg D hD x a hx ha n)

private lemma head_mass_step (n : ℕ) :
    2 * rate n * trivialCoeff n =
      1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1) + 1) := by
  dsimp [rate, trivialCoeff]
  have h1 : 2 * ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : 2 * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

private lemma head_loss_step (n : ℕ) :
    2 * rate n ^ 3 * trivialCoeff n =
      4 * ((n : ℝ) + 1) + 1 + (2 * rate n * trivialCoeff n) / 4 := by
  dsimp [rate, trivialCoeff]
  have h1 : 2 * ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : 2 * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

private lemma head_mass_harmonic (M : ℕ) :
    headMass M = (harmonic (2 * M + 1) : ℝ) - 1 := by
  induction M with
  | zero => norm_num [headMass, harmonic]
  | succ M ih =>
    rw [headMass, Finset.sum_range_succ]
    change headMass M + 2 * rate M * trivialCoeff M = _
    rw [ih, head_mass_step]
    have hidx : 2 * (M + 1) + 1 = ((2 * M + 1) + 1) + 1 := by omega
    rw [hidx, harmonic_succ, harmonic_succ]
    push_cast
    ring

private lemma head_loss_exact (M : ℕ) :
    headLoss M = 2 * (M : ℝ) ^ 2 + 3 * M + headMass M / 4 := by
  induction M with
  | zero => simp [headLoss, headMass]
  | succ M ih =>
    rw [headLoss, Finset.sum_range_succ]
    change headLoss M + 2 * rate M ^ 3 * trivialCoeff M = _
    rw [ih, head_loss_step, headMass, Finset.sum_range_succ]
    change 2 * (M : ℝ) ^ 2 + 3 * M + headMass M / 4 +
        (4 * ((M : ℝ) + 1) + 1 + (2 * rate M * trivialCoeff M) / 4) = _
    push_cast
    ring

/-- Consumed finite-head application of the retained moment-exponential
theorem. The full tail is kept by an absolutely convergent positive series.
This is not asserted as a standalone content/admission endpoint. -/
private theorem complete_positive_mixture_head
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q) (M : ℕ)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (headMass M - D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) *
      (2 * (M : ℝ) ^ 2 + 3 * M + headMass M / 4)) * energy x a ≤
        (quadratic x a P).re := by
  classical
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have hterm (n : ℕ) :
      (2 * rate n * trivialCoeff n - D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) *
        (2 * rate n ^ 3 * trivialCoeff n)) * energy x a ≤
          (quadratic x a (mixtureTerm n)).re := by
    have h := D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.moment_exponential_prefix_coercivity
      D hD q hq (rate n) (by dsimp [rate]; positivity) x a hx hm
    have hscaled := mul_le_mul_of_nonneg_left h (trivialCoeff_nonneg n)
    have hquad : (quadratic x a (mixtureTerm n)).re = trivialCoeff n *
        (quadratic x a (fun t => Real.exp (-rate n * |t|))).re := by
      simp only [quadratic, mixtureTerm, Complex.ofReal_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sum_re,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hquad]
    convert hscaled using 1 <;> dsimp only [energy] <;> ring
  have hsum := Finset.sum_le_sum (s := Finset.range M) (fun n hn => hterm n)
  have hid : (∑ n ∈ Finset.range M,
      (2 * rate n * trivialCoeff n - D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) *
        (2 * rate n ^ 3 * trivialCoeff n)) * energy x a) =
      (headMass M - D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * headLoss M) * energy x a := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  rw [hid, head_loss_exact] at hsum
  exact hsum.trans (head_below_full D hD.le x a hx ha M)

private lemma head_mass_nonneg (M : ℕ) : 0 ≤ headMass M := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (by dsimp [rate]; positivity) (trivialCoeff_nonneg n)

private lemma head_mass_upper (M : ℕ) : headMass M ≤ 2 * M := by
  have hterm (n : ℕ) : 2 * rate n * trivialCoeff n ≤ 2 := by
    rw [head_mass_step]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 1 ≤ 2 * ((n : ℝ) + 1) := by linarith only [hn0]
    have h2 : 1 ≤ 2 * ((n : ℝ) + 1) + 1 := by linarith only [hn0]
    have hb1 := (div_le_one (by positivity : 0 < 2 * ((n : ℝ) + 1))).mpr h1
    have hb2 := (div_le_one (by positivity : 0 < 2 * ((n : ℝ) + 1) + 1)).mpr h2
    linarith
  have h := Finset.sum_le_sum (s := Finset.range M) (fun n hn => hterm n)
  simpa only [headMass, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using h

private lemma positive_mixture_coefficient (D : ℝ) (hD : 0 < D)
    (q : ℕ) (hq : 1 ≤ q) (hr : 8 ≤ (q : ℝ) / D) :
    Real.log ((q : ℝ) / D) - 1 ≤
      headMass ⌊(q : ℝ) / D⌋₊ - D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) *
        (2 * (⌊(q : ℝ) / D⌋₊ : ℝ) ^ 2 + 3 * ⌊(q : ℝ) / D⌋₊ +
          headMass ⌊(q : ℝ) / D⌋₊ / 4) := by
  let r : ℝ := (q : ℝ) / D
  let M : ℕ := ⌊r⌋₊
  let A : ℝ := headMass M
  let delta : ℝ := D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))
  have hr8 : 8 ≤ r := hr
  have hr0 : 0 < r := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hMr : (M : ℝ) ≤ r := Nat.floor_le hr0.le
  have hrM : r < (M : ℝ) + 1 := Nat.lt_floor_add_one r
  have hA0 : 0 ≤ A := head_mass_nonneg M
  have hAup : A ≤ 2 * M := head_mass_upper M
  have hAlow : Real.log (2 * r) - 1 ≤ A := by
    have hlog := Real.log_le_log (by positivity : 0 < 2 * r)
      (show 2 * r ≤ ((2 * M + 1 + 1 : ℕ) : ℝ) by push_cast; linarith)
    have hh : Real.log ((2 * M + 1 + 1 : ℕ) : ℝ) - 1 ≤ A := by
      dsimp only [A]
      rw [head_mass_harmonic M]
      exact sub_le_sub_right (log_add_one_le_harmonic (2 * M + 1)) 1
    linarith only [hlog, hh]
  have hdel0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdel : delta ≤ 1 / (4 * r ^ 2) := by
    have hden : 0 < 4 * (q : ℝ) * ((q : ℝ) + 1) := by positivity
    have hrden : 0 < 4 * r ^ 2 := by positivity
    apply (div_le_div_iff₀ hden hrden).mpr
    dsimp only [r]
    field_simp [hD.ne']
    nlinarith [sq_nonneg D]
  have hL0 : 0 ≤ 2 * (M : ℝ) ^ 2 + 3 * M + A / 4 := by positivity
  have hLup : 2 * (M : ℝ) ^ 2 + 3 * M + A / 4 ≤ 2 * r ^ 2 + (7 / 2) * r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hMr) (show 0 ≤ r + M by positivity)]
  have hpay : delta * (2 * (M : ℝ) ^ 2 + 3 * M + A / 4) ≤ 1 / 2 + 7 / (8 * r) := by
    calc
      _ ≤ (1 / (4 * r ^ 2)) * (2 * (M : ℝ) ^ 2 + 3 * M + A / 4) :=
        mul_le_mul_of_nonneg_right hdel hL0
      _ ≤ (1 / (4 * r ^ 2)) * (2 * r ^ 2 + (7 / 2) * r) :=
        mul_le_mul_of_nonneg_left hLup (by positivity)
      _ = _ := by field_simp; ring
  have hfrac : 7 / (8 * r) ≤ (7 / 64 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * r)).mpr
    linarith only [hr8]
  have hlogtwo : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog : Real.log (2 * r) = Real.log 2 + Real.log r :=
    Real.log_mul (by norm_num) hr0.ne'
  change Real.log r - 1 ≤ A - delta * (2 * (M : ℝ) ^ 2 + 3 * M + A / 4)
  linarith only [hAlow, hpay, hfrac, hlogtwo, hlog]

/-- A consumed quantitative application to the COMPLETE actual P, with
M=floor(q/D), exact A_M=H_(2M+1)-1, and exact finite-head loss. This
application is reuse-only, and is not a separate source-admission request. -/
theorem complete_positive_mixture_logarithmic
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q) (hr : 8 ≤ (q : ℝ) / D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (Real.log ((q : ℝ) / D) - 1) * energy x a ≤ (quadratic x a P).re := by
  have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
  exact (mul_le_mul_of_nonneg_right (positive_mixture_coefficient D hD q hq hr) hE).trans
    (complete_positive_mixture_head D hD q hq ⌊(q : ℝ) / D⌋₊ x a hx hm)

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
