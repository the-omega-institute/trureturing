/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete positive mixture logarithmic bound for the actual exponential rates. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentArithmetic
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalAngularResolvent
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

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

private lemma quadratic_mixture_scale (x : I → ℝ) (a : I → ℂ) (n : ℕ) :
    (quadratic x a (mixtureTerm n)).re = trivialCoeff n *
      (quadratic x a (fun t => Real.exp (-rate n * |t|))).re := by
  have he : quadratic x a (mixtureTerm n) = (trivialCoeff n : ℂ) *
      quadratic x a (fun t => Real.exp (-rate n * |t|)) := by
    simp only [quadratic, mixtureTerm, Complex.ofReal_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    using congrArg Complex.re he

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
  have hid := quadratic_mixture_scale x a n
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
    rw [hidx, harmonic_succ (2 * M + 1 + 1), harmonic_succ (2 * M + 1)]
    push_cast
    ring

private lemma head_loss_exact (M : ℕ) :
    headLoss M = 2 * (M : ℝ) ^ 2 + 3 * M + headMass M / 4 := by
  induction M with
  | zero => simp [headLoss, headMass]
  | succ M ih =>
    rw [headLoss, Finset.sum_range_succ]
    change headLoss M + 2 * rate M ^ 3 * trivialCoeff M = _
    rw [ih, head_loss_step]
    have hs : headMass (M + 1) = headMass M + 2 * rate M * trivialCoeff M := by
      exact Finset.sum_range_succ _ M
    rw [hs]
    change 2 * (M : ℝ) ^ 2 + 3 * M + headMass M / 4 +
        (4 * ((M : ℝ) + 1) + 1 + (2 * rate M * trivialCoeff M) / 4) = _
    push_cast
    ring

/-- Consumed finite-head application of the retained moment-exponential
theorem. The full tail is kept by an absolutely convergent positive series.
This is not asserted as a standalone content/admission endpoint. -/
theorem complete_positive_mixture_head
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
    have hquad := quadratic_mixture_scale x a n
    rw [hquad]
    convert hscaled using 1 <;> (try dsimp only [energy, quadratic]) <;> ring
  have hsum := Finset.sum_le_sum (s := Finset.range M) (fun n hn => hterm n)
  have hid : (∑ n ∈ Finset.range M,
      (2 * rate n * trivialCoeff n - D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) *
        (2 * rate n ^ 3 * trivialCoeff n)) * energy x a) =
      (headMass M - D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * headLoss M) * energy x a := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  rw [hid, head_loss_exact] at hsum
  exact hsum.trans (head_below_full D hD.le x a hx ha M)

/-! Finite-head form consuming the strengthened Gamma certificate. -/
theorem complete_positive_mixture_head_gamma
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q) (M m : ℕ) (hmpos : 1 ≤ m)
    (ham : D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) ≤ 1 / (m : ℝ))
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (∑ n ∈ Finset.range M,
      trivialCoeff n * (2 * rate n / (1 + rate n ^ 2 / (m : ℝ)))) * energy x a ≤
      (quadratic x a P).re := by
  classical
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have hfirst : ∑ i, a i * (x i : ℂ) = 0 := by simpa using hm 1 hq
  have hterm (n : ℕ) :
      (trivialCoeff n * (2 * rate n / (1 + rate n ^ 2 / (m : ℝ)))) * energy x a ≤
        (quadratic x a (mixtureTerm n)).re := by
    let lam : ℝ := rate n
    have hlam : 0 < lam := by dsimp [lam, rate]; positivity
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      exact_mod_cast (show 0 < m by omega)
    have hden : 0 < 1 + lam ^ 2 / (m : ℝ) := by positivity
    have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
    have hγ := D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_gamma_gap_coercivity
      D hD q hq lam hlam x a hx hm
    have hq0 := D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_kernel_nonneg
      D hD.le lam hlam x a hx
    have hbase : 2 * lam * energy x a ≤ (1 + lam ^ 2 / (m : ℝ)) *
        (∑ i, ∑ j, star (a i) * a j *
          (Real.exp (-lam * |x i - x j|) : ℂ)).re := by
      have hdenGap : 1 + lam ^ 2 *
          (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) ≤
          1 + lam ^ 2 / (m : ℝ) := by
        have hmulGap := mul_le_mul_of_nonneg_left ham (sq_nonneg lam)
        calc
          _ ≤ 1 + lam ^ 2 * (1 / (m : ℝ)) := by linarith
          _ = _ := by ring
      have hmul := mul_le_mul_of_nonneg_right hdenGap hq0
      have hγ' :
          (1 + lam ^ 2 * (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)))) *
              energy x a *
                (∑ i, ∑ j, star (a i) * a j *
                  (Real.exp (-lam * |x i - x j|) : ℂ)).re ≥
            2 * lam * (energy x a) ^ 2 := by
        simpa [energy, mul_assoc, mul_comm, mul_left_comm] using hγ
      by_cases hE0 : energy x a = 0
      · have hQ : 0 ≤
            (∑ i, ∑ j, star (a i) * a j *
              (Real.exp (-lam * |x i - x j|) : ℂ)).re := hq0
        nlinarith
      · have hEpos : 0 < energy x a :=
          lt_of_le_of_ne (integral_nonneg (fun _ => sq_nonneg _)) (Ne.symm hE0)
        have hmulE := mul_le_mul_of_nonneg_right hmul hE
        have hmulE' :
            (1 + lam ^ 2 * (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)))) *
                energy x a *
                  (∑ i, ∑ j, star (a i) * a j *
                    (Real.exp (-lam * |x i - x j|) : ℂ)).re ≤
              (1 + lam ^ 2 / (m : ℝ)) *
                energy x a *
                  (∑ i, ∑ j, star (a i) * a j *
                    (Real.exp (-lam * |x i - x j|) : ℂ)).re := by
          calc
            _ = (1 + lam ^ 2 * (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)))) *
                (∑ i, ∑ j, star (a i) * a j *
                  (Real.exp (-lam * |x i - x j|) : ℂ)).re * energy x a := by ring
            _ ≤ (1 + lam ^ 2 / (m : ℝ)) *
                (∑ i, ∑ j, star (a i) * a j *
                  (Real.exp (-lam * |x i - x j|) : ℂ)).re * energy x a := hmulE
            _ = _ := by ring
        have hchain := hγ'.trans hmulE'
        have hcancel :
            (2 * lam * energy x a) * energy x a ≤
              ((1 + lam ^ 2 / (m : ℝ)) *
                (∑ i, ∑ j, star (a i) * a j *
                  (Real.exp (-lam * |x i - x j|) : ℂ)).re) * energy x a := by
          calc
            _ = 2 * lam * (energy x a) ^ 2 := by ring
            _ ≤ _ := hchain
            _ = _ := by ring
        exact le_of_mul_le_mul_right hcancel hEpos
    have hquot : (2 * lam / (1 + lam ^ 2 / (m : ℝ))) * energy x a ≤
        (quadratic x a (fun t => Real.exp (-lam * |t|))).re := by
      calc
        _ = (2 * lam * energy x a) / (1 + lam ^ 2 / (m : ℝ)) := by ring
        _ ≤ _ := by
          apply (div_le_iff₀ hden).mpr
          convert hbase using 1 <;> dsimp only [quadratic] <;> ring
    have hscaled := mul_le_mul_of_nonneg_left hquot (trivialCoeff_nonneg n)
    have hquad := quadratic_mixture_scale x a n
    rw [hquad]
    convert hscaled using 1 <;> (try dsimp only [energy, lam]) <;> ring
  have hsum := Finset.sum_le_sum (s := Finset.range M) (fun n hn => hterm n)
  rw [← Finset.sum_mul] at hsum
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

/-- The complete multiplier of the literal positive kernel, with every actual rate. -/
def pMultiplier (ξ : ℝ) : ℝ :=
  ∑' n : ℕ, (2 * rate n * trivialCoeff n) * ξ ^ 2 / (rate n ^ 2 + ξ ^ 2)

private def pTerm (n : ℕ) (ξ : ℝ) : ℝ :=
  (2 * rate n * trivialCoeff n) * ξ ^ 2 / (rate n ^ 2 + ξ ^ 2)

private lemma pTerm_nonneg (n : ℕ) (ξ : ℝ) : 0 ≤ pTerm n ξ := by
  have hc := trivialCoeff_nonneg n
  dsimp [pTerm, rate]
  positivity

private lemma pTerm_summable (ξ : ℝ) : Summable (fun n => pTerm n ξ) := by
  apply Summable.of_nonneg_of_le (fun n => pTerm_nonneg n ξ) _
    (trivialCoeff_hasSum.summable.mul_right (ξ ^ 2))
  intro n
  have hr : 2 ≤ rate n := by dsimp [rate]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hd : 0 < rate n ^ 2 + ξ ^ 2 := by positivity
  apply (div_le_iff₀ hd).mpr
  have hrr : 2 * rate n ≤ rate n ^ 2 + ξ ^ 2 := by nlinarith [sq_nonneg ξ]
  have h := mul_le_mul_of_nonneg_right hrr
    (mul_nonneg (trivialCoeff_nonneg n) (sq_nonneg ξ))
  nlinarith only [h]

/- The comparison function is shifted before the integral test, so its entire
   half-line domain stays a positive distance from its pole. -/
private def logComparison (X u : ℝ) : ℝ := X ^ 2 / (u * (4 * u ^ 2 + X ^ 2))

private lemma logComparison_nonneg (X : ℝ) {u : ℝ} (hu : 0 < u) :
    0 ≤ logComparison X u := by dsimp [logComparison]; positivity

private lemma logComparison_antitone (X c : ℝ) (hc : 0 < c) :
    AntitoneOn (fun u => logComparison X (u + c)) (Ici 0) := by
  intro u hu v hv huv
  have hu' : 0 < u + c := by linarith [hu.out]
  have hv' : 0 < v + c := by linarith [hv.out]
  apply div_le_div_of_nonneg_left (sq_nonneg X) (by positivity :
    0 < (u + c) * (4 * (u + c) ^ 2 + X ^ 2))
  gcongr

private lemma logComparison_integral (X c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u => logComparison X (u + c)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, logComparison X (u + c)) =
        Real.log (1 + X ^ 2 / (4 * c ^ 2)) / 2 := by
  let F : ℝ → ℝ := fun u => -Real.log (1 + X ^ 2 / (4 * (u + c) ^ 2)) / 2
  have hd (u : ℝ) (hu : u ∈ Ici (0 : ℝ)) :
      HasDerivAt F (logComparison X (u + c)) u := by
    have huc : 0 < u + c := by linarith [hu.out]
    have hden : 4 * (u + c) ^ 2 ≠ 0 := by positivity
    have hlog : 1 + X ^ 2 / (4 * (u + c) ^ 2) ≠ 0 := by positivity
    have h := (((hasDerivAt_const u (X ^ 2)).div
      ((((hasDerivAt_id u).add_const c).pow 2).const_mul 4) hden).const_add 1).log hlog
    convert h.neg.div_const 2 using 1 <;>
      dsimp [F, logComparison] <;>
      field_simp [ne_of_gt huc] <;> ring
  have hn (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) : 0 ≤ logComparison X (u + c) :=
    logComparison_nonneg X (by linarith [hu.out])
  have hlim : Tendsto F atTop (𝓝 0) := by
    have ht : Tendsto (fun u : ℝ => 4 * (u + c) ^ 2) atTop atTop :=
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (tendsto_atTop_add_const_right atTop c tendsto_id)).const_mul_atTop (by norm_num)
    have hq : Tendsto (fun u : ℝ => 1 + X ^ 2 / (4 * (u + c) ^ 2)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.div_atTop ht).const_add 1
    have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hq
    simpa [F] using hl.neg.div_const 2
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn hlim, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hd hn hlim
  simpa [F, neg_div] using h

private lemma pTerm_comparison (n : ℕ) (ξ : ℝ) :
    logComparison |ξ| ((n : ℝ) + 3 / 2) ≤ pTerm n ξ ∧
      pTerm n ξ ≤ logComparison |ξ| ((n : ℝ) + 1) := by
  have hk : 0 < (n : ℝ) + 1 := by positivity
  have hks : 0 < (n : ℝ) + 3 / 2 := by positivity
  have hs := sq_nonneg ξ
  have hr : 0 < rate n := by dsimp [rate]; positivity
  dsimp [pTerm]
  rw [head_mass_step]
  dsimp [logComparison, rate]
  rw [sq_abs]
  constructor
  all_goals
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    field_simp
    apply sub_nonneg.mp
    ring_nf
    positivity

private lemma pMultiplier_integral_bounds (ξ : ℝ) :
    Real.log (1 + ξ ^ 2 / 9) / 2 ≤ pMultiplier ξ ∧
      pMultiplier ξ ≤ ξ ^ 2 / (4 + ξ ^ 2) + Real.log (1 + ξ ^ 2 / 4) / 2 := by
  have hi (c : ℝ) (hc : 0 < c) := logComparison_integral |ξ| c hc
  have ha (c : ℝ) (hc : 0 < c) := logComparison_antitone |ξ| c hc
  have hn (c : ℝ) (hc : 0 < c) (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
      0 ≤ logComparison |ξ| (u + c) := logComparison_nonneg |ξ| (by linarith [hu.out])
  have hs (c : ℝ) (hc : 0 < c) :
      Summable (fun n : ℕ => logComparison |ξ| ((n : ℝ) + c)) :=
    (ha c hc).summable_of_integrableOn_Ioi_zero (hi c hc).1 (hn c hc)
  constructor
  · have h := (ha (3 / 2) (by norm_num)).integral_le_tsum
      (hs (3 / 2) (by norm_num)) (hn (3 / 2) (by norm_num))
    rw [(hi (3 / 2) (by norm_num)).2] at h
    norm_num [sq_abs] at h
    exact h.trans ((hs (3 / 2) (by norm_num)).tsum_le_tsum
      (fun n => (pTerm_comparison n ξ).1) (pTerm_summable ξ))
  · have h := (ha 1 (by norm_num)).tsum_le_integral
      (hi 1 (by norm_num)).1 (hn 1 (by norm_num))
    rw [(hi 1 (by norm_num)).2] at h
    norm_num [sq_abs, logComparison] at h
    exact ((pTerm_summable ξ).tsum_le_tsum
      (fun n => (pTerm_comparison n ξ).2) (hs 1 (by norm_num))).trans (by simpa only [logComparison, sq_abs] using h)

/-- Exact logarithmic bounds for the complete literal-P multiplier. The lower
expression is allowed to be negative, and frequency zero is retained. -/
theorem pMultiplier_logarithmic_bounds (ξ : ℝ) :
    Summable (fun n : ℕ =>
      (2 * rate n * trivialCoeff n) * ξ ^ 2 / (rate n ^ 2 + ξ ^ 2)) ∧
    0 ≤ pMultiplier ξ ∧ pMultiplier 0 = 0 ∧
    Real.log (2 + |ξ|) - Real.log 13 / 2 ≤ pMultiplier ξ ∧
    pMultiplier ξ ≤ Real.log (2 + |ξ|) + 1 - Real.log 2 := by
  refine ⟨pTerm_summable ξ, tsum_nonneg (fun n => pTerm_nonneg n ξ),
    by simp [pMultiplier], ?_, ?_⟩
  · have hp : 0 < 1 + ξ ^ 2 / 9 := by positivity
    have hc : (2 + |ξ|) ^ 2 ≤ 13 * (1 + ξ ^ 2 / 9) := by
      nlinarith [sq_abs ξ, sq_nonneg (2 * |ξ| / 3 - 3)]
    have hl := Real.log_le_log (by positivity : 0 < (2 + |ξ|) ^ 2) hc
    rw [Real.log_mul (by norm_num) hp.ne', Real.log_pow] at hl
    linarith [(pMultiplier_integral_bounds ξ).1]
  · have hp : 0 < 1 + ξ ^ 2 / 4 := by positivity
    have hc : 1 + ξ ^ 2 / 4 ≤ ((2 + |ξ|) / 2) ^ 2 := by
      nlinarith [sq_abs ξ, abs_nonneg ξ]
    have hl := Real.log_le_log hp hc
    rw [Real.log_pow, Real.log_div (by positivity) (by norm_num)] at hl
    have hf : ξ ^ 2 / (4 + ξ ^ 2) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    linarith [(pMultiplier_integral_bounds ξ).2]

private lemma scaled_cauchy (l : ℝ) (hl : 0 < l) (t : ℝ) :
    Integrable (fun ξ : ℝ => OriginalActualFourier.phase ξ t /
      ((l ^ 2 + ξ ^ 2 : ℝ) : ℂ)) ∧
    (∫ ξ : ℝ, OriginalActualFourier.phase ξ t / ((l ^ 2 + ξ ^ 2 : ℝ) : ℂ)) =
      ((Real.pi / l * Real.exp (-l * |t|) : ℝ) : ℂ) := by
  let H : ℝ → ℂ := fun w => Complex.exp (Complex.I * (w : ℂ) * ((2 * l * t : ℝ) : ℂ)) /
    ((1 + 4 * w ^ 2 : ℝ) : ℂ)
  have h := OriginalAngularResolvent.angular_resolvent (2 * l * t)
  have hs : (2 * l)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  have he (ξ : ℝ) : OriginalActualFourier.phase ξ t / ((l ^ 2 + ξ ^ 2 : ℝ) : ℂ) =
      ((l ^ 2 : ℝ) : ℂ)⁻¹ * H ((2 * l)⁻¹ * ξ) := by
    dsimp [H, OriginalActualFourier.phase]
    have hphase : Complex.I * (ξ : ℂ) * (t : ℂ) =
        Complex.I * (((2 * l)⁻¹ * ξ : ℝ) : ℂ) * ((2 * l * t : ℝ) : ℂ) := by
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hl.ne']
    have hden : l ^ 2 * (1 + 4 * ((2 * l)⁻¹ * ξ) ^ 2) = l ^ 2 + ξ ^ 2 := by
      field_simp [hl.ne']
      <;> ring
    rw [← hphase, ← hden]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hi : Integrable (fun ξ : ℝ => OriginalActualFourier.phase ξ t /
      ((l ^ 2 + ξ ^ 2 : ℝ) : ℂ)) := by
    simp_rw [he]
    exact (h.1.comp_mul_left' hs).const_mul _
  refine ⟨hi, ?_⟩
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  have habs : |((2 * l)⁻¹)⁻¹| = 2 * l := by rw [inv_inv, abs_of_pos (by positivity)]
  rw [habs, Complex.real_smul]
  have ht : -|2 * l * t| / 2 = -l * |t| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * l)]
    ring
  have hh := h.2
  rw [ht] at hh
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hl : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  change (↑(1 / (2 * Real.pi)) : ℂ) * (∫ w, H w) = _ at hh
  push_cast at hh ⊢
  field_simp at hh ⊢
  linear_combination hh / 2

private lemma atom_fourier_square (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i, x i ≤ D) (ξ : ℝ) :
    ((ξ ^ 2 * ‖OriginalActualFourier.Ahat («prefix» x a) ξ‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, star (a i) * a j * OriginalActualFourier.phase ξ (x i - x j) := by
  classical
  have h := OriginalActualFourier.frequency_mul_Ahat x a ha D hx ξ
  have hs := congrArg (fun z : ℂ => star z * z) h
  have hphase (i j : I) :
      star (OriginalActualFourier.phase (-ξ) (x i)) *
        OriginalActualFourier.phase (-ξ) (x j) =
          OriginalActualFourier.phase ξ (x i - x j) := by
    rw [show star (OriginalActualFourier.phase (-ξ) (x i)) =
      OriginalActualFourier.phase ξ (x i) by
        simpa using OriginalActualFourier.phase_conj (-ξ) (x i)]
    rw [OriginalActualFourier.phase_neg_left, ← OriginalActualFourier.phase_add]
    congr 1 <;> ring
  calc
    _ = star ((Complex.I * (ξ : ℂ)) * OriginalActualFourier.Ahat («prefix» x a) ξ) *
        ((Complex.I * (ξ : ℂ)) * OriginalActualFourier.Ahat («prefix» x a) ξ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      simp [norm_mul, mul_pow, sq_abs]
    _ = star (∑ i, a i * OriginalActualFourier.phase (-ξ) (x i)) *
        (∑ i, a i * OriginalActualFourier.phase (-ξ) (x i)) := hs
    _ = _ := by
      simp only [star_sum, star_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = star (a i) * a j * (star (OriginalActualFourier.phase (-ξ) (x i)) *
            OriginalActualFourier.phase (-ξ) (x j)) := by ring
        _ = _ := by rw [hphase]

private def rateWeight (l ξ : ℝ) : ℝ := 2 * l * ξ ^ 2 / (l ^ 2 + ξ ^ 2)

private lemma one_rate_spectral (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i, x i ≤ D) (l : ℝ) (hl : 0 < l) :
    Integrable (rateWeight l) (OriginalActualFourier.rho («prefix» x a)) ∧
      (quadratic x a (fun t => Real.exp (-l * |t|))).re =
        ∫ ξ, rateWeight l ξ ∂OriginalActualFourier.rho («prefix» x a) := by
  classical
  let A := «prefix» x a
  letI : IsFiniteMeasure (OriginalActualFourier.rho A) :=
    OriginalActualFourier.actual_rho_finite x a ha D hx
  have hden (ξ : ℝ) : 0 < l ^ 2 + ξ ^ 2 := by positivity
  have hc : Continuous (rateWeight l) := by
    unfold rateWeight
    exact (continuous_const.mul (continuous_id.pow 2)).div
      (continuous_const.add (continuous_id.pow 2)) (fun ξ => (hden ξ).ne')
  have hi : Integrable (rateWeight l) (OriginalActualFourier.rho A) := by
    apply (integrable_const (2 * l)).mono' hc.aestronglyMeasurable
    exact ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [rateWeight]; positivity)]
      dsimp [rateWeight]
      apply (div_le_iff₀ (hden ξ)).mpr
      nlinarith [sq_nonneg l]
  have hdm : Measurable (fun ξ => ENNReal.ofReal (OriginalActualFourier.density A ξ)) :=
    (OriginalActualFourier.density_continuous
      (OriginalActualFourier.prefix_integrable x a ha D hx)).measurable.ennreal_ofReal
  have hpoint (ξ : ℝ) :
      ((OriginalActualFourier.density A ξ * rateWeight l ξ : ℝ) : ℂ) =
        ∑ i, ∑ j, (star (a i) * a j * ((l / Real.pi : ℝ) : ℂ)) *
          (OriginalActualFourier.phase ξ (x i - x j) / ((l ^ 2 + ξ ^ 2 : ℝ) : ℂ)) := by
    calc
      _ = ((l / Real.pi : ℝ) : ℂ) *
          ((ξ ^ 2 * ‖OriginalActualFourier.Ahat A ξ‖ ^ 2 : ℝ) : ℂ) /
            ((l ^ 2 + ξ ^ 2 : ℝ) : ℂ) := by
        dsimp [OriginalActualFourier.density, rateWeight]
        push_cast
        field_simp
        <;> ring
      _ = _ := by
        rw [atom_fourier_square x a ha D hx ξ]
        simp only [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hfi (i j : I) :=
    (scaled_cauchy l hl (x i - x j)).1.const_mul
      (star (a i) * a j * ((l / Real.pi : ℝ) : ℂ))
  have hres (i j : I) := (scaled_cauchy l hl (x i - x j)).2
  have he : ((∫ ξ, rateWeight l ξ ∂OriginalActualFourier.rho A : ℝ) : ℂ) =
      quadratic x a (fun t => Real.exp (-l * |t|)) := by
    rw [OriginalActualFourier.rho,
      integral_withDensity_eq_integral_toReal_smul hdm (by simp)]
    simp only [ENNReal.toReal_ofReal (OriginalActualFourier.density_nonneg A _), smul_eq_mul]
    rw [← integral_complex_ofReal]
    simp_rw [hpoint]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hfi i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hfi _ j), integral_const_mul, hres]
    unfold quadratic
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hl.ne']
    <;> ring
  refine ⟨hi, ?_⟩
  simpa using (congrArg Complex.re he).symm

private lemma pTerm_spectral (D : ℝ) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ≤ D) (ha : ∑ i, a i = 0) (n : ℕ) :
    Integrable (pTerm n) (OriginalActualFourier.rho («prefix» x a)) ∧
      (∫ ξ, pTerm n ξ ∂OriginalActualFourier.rho («prefix» x a)) =
        (quadratic x a (mixtureTerm n)).re := by
  have h := one_rate_spectral x a ha D hx (rate n) (by dsimp [rate]; positivity)
  have he : pTerm n = fun ξ => trivialCoeff n * rateWeight (rate n) ξ := by
    funext ξ
    dsimp [pTerm, rateWeight]
    ring
  rw [he]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul, ← h.2, quadratic_mixture_scale]

/-- The complete literal-P quadratic form is the integrable full multiplier
against the original actual Fourier density. No atom, endpoint or frequency
is removed, and no Plancherel-mass or parity premise is imposed. -/
theorem complete_positive_mixture_spectral_identity
    (D : ℝ) (hD : 0 ≤ D) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0) :
    Integrable pMultiplier (OriginalActualFourier.rho («prefix» x a)) ∧
      (quadratic x a P).re =
        ∫ ξ, pMultiplier ξ ∂OriginalActualFourier.rho («prefix» x a) := by
  have ht (n : ℕ) := pTerm_spectral D x a (fun i => (hx i).2) ha n
  have hs : Summable (fun n => ∫ ξ, ‖pTerm n ξ‖
      ∂OriginalActualFourier.rho («prefix» x a)) := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (pTerm_nonneg _ _), (ht _).2]
    exact (Complex.hasSum_re (quadratic_mixture_abs x a).of_norm.hasSum).summable
  have hm : AEStronglyMeasurable pMultiplier
      (OriginalActualFourier.rho («prefix» x a)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (integrable_finsetSum (Finset.range N) (fun n _ => (ht n).1)).1)
    exact ae_of_all _ fun ξ => (pTerm_summable ξ).tendsto_sum_tsum_nat
  have hnorm (ξ : ℝ) : ENNReal.ofReal ‖pMultiplier ξ‖ =
      ∑' n, ENNReal.ofReal ‖pTerm n ξ‖ := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (pTerm_nonneg _ _)]
    rw [abs_of_nonneg (show 0 ≤ pMultiplier ξ from tsum_nonneg (fun n => pTerm_nonneg n ξ))]
    exact ENNReal.ofReal_tsum_of_nonneg (fun n => pTerm_nonneg n ξ) (pTerm_summable ξ)
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_norm]
    simp_rw [hnorm]
    rw [lintegral_tsum (fun n => (ht n).1.norm.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (ht _).1.norm
      (ae_of_all _ fun ξ => norm_nonneg (pTerm _ ξ))]
    exact hs.tsum_ofReal_lt_top
  · have h := integral_tsum_of_summable_integral_norm (fun n => (ht n).1) hs
    have hq := (Complex.hasSum_re (quadratic_mixture_hasSum x a)).tsum_eq
    rw [← hq]
    change (∑' n, (quadratic x a (mixtureTerm n)).re) =
      ∫ ξ, (∑' n, pTerm n ξ) ∂OriginalActualFourier.rho («prefix» x a)
    calc
      _ = ∑' n, ∫ ξ, pTerm n ξ ∂OriginalActualFourier.rho («prefix» x a) :=
        tsum_congr (fun n => (ht n).2.symm)
      _ = _ := h

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
