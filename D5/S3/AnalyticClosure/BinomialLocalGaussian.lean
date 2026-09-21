/- GID: D5/S3/AnalyticClosure/BinomialLocalGaussian
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/BinomialLocalGaussian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform binomial local Gaussian approximation, all-power tails, and finite Gaussian windows. -/

import Mathlib.Analysis.SpecialFunctions.Stirling
import D5.S3.TotalVariation.Pinsker
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter Real Finset MeasureTheory intervalIntegral
open scoped Topology

namespace D5.S3.AnalyticClosure.BinomialLocalGaussian

noncomputable def binomialMass (p : ℝ) (n i : ℕ) : ℝ :=
  (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

noncomputable def binaryKL (x p : ℝ) : ℝ :=
  x * log (x / p) + (1 - x) * log ((1 - x) / (1 - p))

/-- For every fixed Bernoulli parameter strictly between zero and one, the Gaussian
approximation has relative error tending uniformly to zero on the entire window
`|k - n*p| ≤ n^(7/12)`. The quantifiers include every natural `n` and `k` in the window.

The proof applies scalar Stirling at all three growing factorial arguments and the
pinned logarithm-series remainder bound. The window gives `n*|k/n-p|^3 ≤ n^(-1/4)`.
This is a classical local-limit ingredient (Ouimet, arXiv:2001.08512v4, Theorem 2.1),
not a resolution of the powered-sum or maximum asymptotic. -/
theorem local_gaussian_window (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ,
      |(k : ℝ) - n * p| ≤ (n : ℝ) ^ (7 / 12 : ℝ) →
      |binomialMass p n k * sqrt (2 * π * n * p * (1 - p)) *
        exp (((k : ℝ) - n * p) ^ 2 / (2 * n * p * (1 - p))) - 1| < ε := by
  have moving_interior_stirling {α : Type} {f : Filter α}
      (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1)
      (n k : α → ℕ) (hn : Tendsto n f atTop)
      (hx : Tendsto (fun a => (k a : ℝ) / n a) f (𝓝 q)) :
      Tendsto (fun a => log (binomialMass p (n a) (k a)) +
        (1 / 2 : ℝ) * log (2 * π * n a * ((k a : ℝ) / n a) *
          (1 - (k a : ℝ) / n a)) +
        n a * binaryKL ((k a : ℝ) / n a) p) f (𝓝 0) := by
    have log_mass_identity (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n i : ℕ)
        (hi : 0 < i) (hin : i < n) :
        log (binomialMass p n i) +
          (1 / 2 : ℝ) * log (2 * π * n * ((i : ℝ) / n) * (1 - (i : ℝ) / n)) +
          n * binaryKL ((i : ℝ) / n) p =
        log (Stirling.stirlingSeq n) - log (Stirling.stirlingSeq i) -
          log (Stirling.stirlingSeq (n - i)) + (1 / 2 : ℝ) * log π := by
      have hn : 0 < n := hi.trans hin
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hiR : (0 : ℝ) < i := by exact_mod_cast hi
      have hjR : (0 : ℝ) < (n - i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hin
      have hj : ((n - i : ℕ) : ℝ) = (n : ℝ) - i := Nat.cast_sub hin.le
      have hc : (0 : ℝ) < n.choose i := by exact_mod_cast Nat.choose_pos hin.le
      have hnp : 0 < 1 - p := sub_pos.mpr hp1
      have hx : 0 < (i : ℝ) / n := div_pos hiR hnR
      have hxn : 0 < 1 - (i : ℝ) / n := by
        rw [sub_pos, div_lt_one hnR]
        exact_mod_cast hin
      have hcomp : 1 - (i : ℝ) / n = ((n - i : ℕ) : ℝ) / n := by
        rw [hj]; field_simp
      have hnfac : (0 : ℝ) < n.factorial := by positivity
      have hifac : (0 : ℝ) < i.factorial := by positivity
      have hjfac : (0 : ℝ) < (n - i).factorial := by positivity
      rw [binomialMass, log_mul (mul_pos hc (pow_pos hp _)).ne' (pow_pos hnp _).ne',
        log_mul hc.ne' (pow_pos hp _).ne', log_pow, log_pow,
        Nat.cast_choose ℝ hin.le, log_div hnfac.ne' (mul_pos hifac hjfac).ne',
        log_mul hifac.ne' hjfac.ne']
      rw [binaryKL, log_div hx.ne' hp.ne', log_div hxn.ne' hnp.ne',
        log_mul (by positivity : 2 * π * (n : ℝ) * ((i : ℝ) / n) ≠ 0) hxn.ne',
        log_mul (by positivity : 2 * π * (n : ℝ) ≠ 0) hx.ne',
        log_mul (by positivity : 2 * π ≠ 0) hnR.ne',
        log_mul (by norm_num : (2 : ℝ) ≠ 0) pi_pos.ne',
        hcomp, log_div hjR.ne' hnR.ne', log_div hiR.ne' hnR.ne',
        Stirling.log_stirlingSeq_formula, Stirling.log_stirlingSeq_formula,
        Stirling.log_stirlingSeq_formula,
        log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne',
        log_mul (by norm_num : (2 : ℝ) ≠ 0) hiR.ne',
        log_mul (by norm_num : (2 : ℝ) ≠ 0) hjR.ne',
        log_div hnR.ne' (exp_pos 1).ne', log_div hiR.ne' (exp_pos 1).ne',
        log_div hjR.ne' (exp_pos 1).ne', log_exp, hj]
      field_simp
      ring
    have hnR : Tendsto (fun a => (n a : ℝ)) f atTop :=
      tendsto_natCast_atTop_atTop.comp hn
    have hnp : ∀ᶠ a in f, 0 < n a := hn.eventually (eventually_gt_atTop 0)
    have hxp : ∀ᶠ a in f, 0 < (k a : ℝ) / n a := hx.eventually (lt_mem_nhds hq)
    have hxl : ∀ᶠ a in f, (k a : ℝ) / n a < 1 := hx.eventually (gt_mem_nhds hq1)
    have hki : ∀ᶠ a in f, 0 < k a ∧ k a < n a := by
      filter_upwards [hnp, hxp, hxl] with a hn0 hk0 hkn
      have hn0R : (0 : ℝ) < n a := by exact_mod_cast hn0
      constructor
      · have : (0 : ℝ) < k a := (div_pos_iff_of_pos_right hn0R).mp hk0
        exact_mod_cast this
      · exact_mod_cast (div_lt_one hn0R).mp hkn
    have hkR : Tendsto (fun a => (k a : ℝ)) f atTop := by
      apply (hnR.atTop_mul_pos hq hx).congr'
      filter_upwards [hnp] with a ha
      exact mul_div_cancel₀ _ (by exact_mod_cast ha.ne' : (n a : ℝ) ≠ 0)
    have hk : Tendsto k f atTop := tendsto_natCast_atTop_iff.mp hkR
    have hjR : Tendsto (fun a => ((n a - k a : ℕ) : ℝ)) f atTop := by
      apply (hnR.atTop_mul_pos (sub_pos.mpr hq1) (tendsto_const_nhds.sub hx)).congr'
      filter_upwards [hnp, hki] with a hn0 hk0
      rw [Nat.cast_sub hk0.2.le]
      field_simp
    have hj : Tendsto (fun a => n a - k a) f atTop := tendsto_natCast_atTop_iff.mp hjR
    have hlog (j : α → ℕ) (hj : Tendsto j f atTop) :
        Tendsto (fun a => log (Stirling.stirlingSeq (j a))) f (𝓝 (log (sqrt π))) :=
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hj).log (by positivity)
    have he := (((hlog n hn).sub (hlog k hk)).sub (hlog _ hj)).add_const
      ((1 / 2 : ℝ) * log π)
    have hc : log (sqrt π) - log (sqrt π) - log (sqrt π) +
        (1 / 2 : ℝ) * log π = 0 := by rw [log_sqrt pi_pos.le]; ring
    rw [hc] at he
    apply he.congr'
    filter_upwards [hki] with a ha
    exact (log_mass_identity p hp hp1 (n a) (k a) ha.1 ha.2).symm
  -- A cubic logarithm-series remainder controls the growing central window.
  have kl_cubic_error {α : Type} {f : Filter α}
      (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : α → ℕ) (u : α → ℝ)
      (hu : Tendsto u f (𝓝 0))
      (hc : Tendsto (fun a => (n a : ℝ) * |u a| ^ 3) f (𝓝 0)) :
      Tendsto (fun a => (n a : ℝ) *
        (binaryKL (p + u a) p - (u a) ^ 2 / (2 * p * (1 - p)))) f (𝓝 0) := by
    have hscaled (c : ℝ) (hc0 : c ≠ 0) (v : α → ℝ)
        (hv : Tendsto v f (𝓝 0))
        (hcv : Tendsto (fun a => (n a : ℝ) * |v a| ^ 3) f (𝓝 0)) :
        Tendsto (fun a => (n a : ℝ) *
          (log (1 + v a / c) - v a / c + (v a / c) ^ 2 / 2)) f (𝓝 0) := by
      have hvd : Tendsto (fun a => v a / c) f (𝓝 0) := by
        simpa using hv.div_const c
      have hsmall : ∀ᶠ a in f, |v a / c| < 1 :=
        (hvd.abs).eventually (by simpa using (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
      have hbound : ∀ᶠ a in f, |(n a : ℝ) *
          (log (1 + v a / c) - v a / c + (v a / c) ^ 2 / 2)| ≤
          ((n a : ℝ) * |v a| ^ 3) / (|c| ^ 3 * (1 - |v a / c|)) := by
        filter_upwards [hsmall] with a ha
        have hb := abs_log_sub_add_sum_range_le (x := -(v a / c))
          (by simpa using ha) 2
        norm_num [Finset.sum_range_succ] at hb
        rw [abs_mul, Nat.abs_cast]
        calc
          _ ≤ (n a : ℝ) * (|v a / c| ^ 3 / (1 - |v a / c|)) := by
            gcongr
            convert hb using 1 <;> congr 1 <;> ring
          _ = _ := by rw [abs_div, div_pow, div_div, mul_div_assoc]
      have hden : Tendsto (fun a => |c| ^ 3 * (1 - |v a / c|)) f (𝓝 (|c| ^ 3)) := by
        simpa using (tendsto_const_nhds (x := |c| ^ 3)).mul
          ((tendsto_const_nhds (x := (1 : ℝ))).sub hvd.abs)
      have hz := hcv.div hden (pow_ne_zero 3 (abs_ne_zero.mpr hc0))
      simp only [zero_div] at hz
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (by simpa using hz.neg) hz
        (hbound.mono fun a ha => (abs_le.mp ha).1)
        (hbound.mono fun a ha => (abs_le.mp ha).2)
    have he₁ := hscaled p hp.ne' u hu hc
    have hcn : Tendsto (fun a => (n a : ℝ) * |-u a| ^ 3) f (𝓝 0) := by
      simpa only [abs_neg] using hc
    have he₂ := hscaled (1 - p) (sub_pos.mpr hp1).ne' (fun a => -u a)
      (by simpa using hu.neg) hcn
    have huc : Tendsto (fun a => (n a : ℝ) * (u a) ^ 3) f (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hc.neg) hc
      · exact Eventually.of_forall fun a => by
          have := neg_abs_le ((n a : ℝ) * (u a) ^ 3)
          simpa [abs_mul, abs_pow] using this
      · exact Eventually.of_forall fun a => by
          have := le_abs_self ((n a : ℝ) * (u a) ^ 3)
          simpa [abs_mul, abs_pow] using this
    have hpLim : Tendsto (fun a => p + u a) f (𝓝 p) := by simpa using hu.const_add p
    have hpnLim : Tendsto (fun a => 1 - p - u a) f (𝓝 (1 - p)) := by
      simpa using (tendsto_const_nhds (x := 1 - p)).sub hu
    have hlim := ((hpLim.mul he₁).add (hpnLim.mul he₂)).add
        (huc.mul_const (1 / (2 * (1 - p) ^ 2) - 1 / (2 * p ^ 2)))
    simp only [add_zero, mul_zero, zero_mul] at hlim
    apply hlim.congr'
    exact Eventually.of_forall fun a => by
      have h₁ : (p + u a) / p = 1 + u a / p := by field_simp [hp.ne']
      have h₂ : (1 - (p + u a)) / (1 - p) = 1 + -u a / (1 - p) := by
        field_simp [(sub_pos.mpr hp1).ne']
        <;> ring
      dsimp only [binaryKL]
      rw [h₁, h₂]
      field_simp [hp.ne', (sub_pos.mpr hp1).ne']
      ring
  -- Exponentiate the combined Stirling and entropy errors.
  have local_gaussian_of_cubic {α : Type} {f : Filter α}
      (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
      (n k : α → ℕ) (hn : Tendsto n f atTop)
      (hx : Tendsto (fun a => (k a : ℝ) / n a) f (𝓝 p))
      (hc : Tendsto (fun a => (n a : ℝ) * |(k a : ℝ) / n a - p| ^ 3) f (𝓝 0)) :
      Tendsto (fun a => binomialMass p (n a) (k a) *
        sqrt (2 * π * n a * p * (1 - p)) *
        exp (((k a : ℝ) - n a * p) ^ 2 / (2 * n a * p * (1 - p)))) f (𝓝 1) := by
    let x : α → ℝ := fun a => (k a : ℝ) / n a
    let u : α → ℝ := fun a => x a - p
    have hu : Tendsto u f (𝓝 0) := by simpa [u, x] using hx.sub_const p
    have hs := moving_interior_stirling p p hp hp1 hp hp1 n k hn hx
    have he := kl_cubic_error p hp hp1 n u hu hc
    have hkl : Tendsto (fun a => (n a : ℝ) *
        (binaryKL (x a) p - (u a) ^ 2 / (2 * p * (1 - p)))) f (𝓝 0) := by
      simpa [u] using he
    have hratio : Tendsto (fun a => p * (1 - p) / (x a * (1 - x a))) f (𝓝 1) := by
      have hprod := hx.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hx)
      have hr := (tendsto_const_nhds (x := p * (1 - p))).div hprod
        (mul_pos hp (sub_pos.mpr hp1)).ne'
      convert! hr using 1 <;> simp [div_self (mul_pos hp (sub_pos.mpr hp1)).ne']
    have hrlog : Tendsto (fun a => (1 / 2 : ℝ) *
        log (p * (1 - p) / (x a * (1 - x a)))) f (𝓝 0) := by
      simpa using (hratio.log (by norm_num : (1 : ℝ) ≠ 0)).const_mul (1 / 2 : ℝ)
    have hsum := Real.continuous_exp.continuousAt.tendsto.comp ((hs.sub hkl).add hrlog)
    simp only [sub_zero, add_zero, exp_zero] at hsum
    have hnp : ∀ᶠ a in f, 0 < n a := hn.eventually (eventually_gt_atTop 0)
    have hxp : ∀ᶠ a in f, 0 < x a := hx.eventually (lt_mem_nhds hp)
    have hxl : ∀ᶠ a in f, x a < 1 := hx.eventually (gt_mem_nhds hp1)
    apply hsum.congr'
    filter_upwards [hnp, hxp, hxl] with a hn0 hx0 hx1
    have hnR : (0 : ℝ) < n a := by exact_mod_cast hn0
    have hkn : k a < n a := by exact_mod_cast (div_lt_one hnR).mp hx1
    have hmass : 0 < binomialMass p (n a) (k a) := by
      unfold binomialMass
      exact mul_pos (mul_pos (by exact_mod_cast Nat.choose_pos hkn.le) (pow_pos hp _))
        (pow_pos (sub_pos.mpr hp1) _)
    have hvar : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
    have hxvar : 0 < x a * (1 - x a) := mul_pos hx0 (sub_pos.mpr hx1)
    have hlog : log (2 * π * n a * x a * (1 - x a)) +
        log (p * (1 - p) / (x a * (1 - x a))) =
        log (2 * π * n a * p * (1 - p)) := by
      rw [← log_mul (by positivity) (div_pos hvar hxvar).ne']
      congr 1
      field_simp [hx0.ne', (sub_pos.mpr hx1).ne']
    have hquad : (n a : ℝ) * (u a) ^ 2 / (2 * p * (1 - p)) =
        ((k a : ℝ) - n a * p) ^ 2 / (2 * n a * p * (1 - p)) := by
      dsimp [u, x]
      field_simp
    have halg :
        (log (binomialMass p (n a) (k a)) +
          (1 / 2 : ℝ) * log (2 * π * n a * x a * (1 - x a)) +
          n a * binaryKL (x a) p -
          n a * (binaryKL (x a) p - (u a) ^ 2 / (2 * p * (1 - p)))) +
          (1 / 2 : ℝ) * log (p * (1 - p) / (x a * (1 - x a))) =
        log (binomialMass p (n a) (k a)) +
          log (sqrt (2 * π * n a * p * (1 - p))) +
          ((k a : ℝ) - n a * p) ^ 2 / (2 * n a * p * (1 - p)) := by
      rw [log_sqrt (by positivity), ← hlog, ← hquad]
      ring
    change exp _ = _
    calc
      _ = exp (log (binomialMass p (n a) (k a)) +
          log (sqrt (2 * π * n a * p * (1 - p))) +
          ((k a : ℝ) - n a * p) ^ 2 / (2 * n a * p * (1 - p))) :=
        congrArg Real.exp halg
      _ = _ := by rw [exp_add, exp_add, exp_log hmass, exp_log (by positivity)]
  intro ε hε
  classical
  by_contra h
  push Not at h
  choose n hn k hk hbad using h
  have hnt : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have hnRt : Tendsto (fun a => (n a : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnt
  have hnp : ∀ᶠ a in atTop, 0 < n a := hnt.eventually (eventually_gt_atTop 0)
  have hdev : ∀ᶠ a in atTop, |(k a : ℝ) / n a - p| ≤
      (n a : ℝ) ^ (-(5 / 12 : ℝ)) := by
    filter_upwards [hnp] with a ha
    have haR : (0 : ℝ) < n a := by exact_mod_cast ha
    calc
      _ = |(k a : ℝ) - n a * p| / n a := by
        have hi : (k a : ℝ) / n a - p = ((k a : ℝ) - n a * p) / n a := by
          field_simp
        rw [hi, abs_div, abs_of_pos haR]
      _ ≤ (n a : ℝ) ^ (7 / 12 : ℝ) / n a := div_le_div_of_nonneg_right (hk a) haR.le
      _ = _ := by rw [← rpow_sub_one haR.ne']; norm_num
  have hdec : Tendsto (fun a => (n a : ℝ) ^ (-(5 / 12 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 12)).comp hnRt
  have hu : Tendsto (fun a => (k a : ℝ) / n a - p) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hdec.neg) hdec
      (hdev.mono fun a ha => (abs_le.mp ha).1)
      (hdev.mono fun a ha => (abs_le.mp ha).2)
  have hx : Tendsto (fun a => (k a : ℝ) / n a) atTop (𝓝 p) := by
    simpa using hu.add_const p
  have hcbd : ∀ᶠ a in atTop, (n a : ℝ) * |(k a : ℝ) / n a - p| ^ 3 ≤
      (n a : ℝ) ^ (-(1 / 4 : ℝ)) := by
    filter_upwards [hnp, hdev] with a ha hb
    have haR : (0 : ℝ) < n a := by exact_mod_cast ha
    calc
      _ ≤ (n a : ℝ) * ((n a : ℝ) ^ (-(5 / 12 : ℝ))) ^ 3 := by gcongr
      _ = (n a : ℝ) ^ (1 : ℝ) * (n a : ℝ) ^ ((-(5 / 12 : ℝ)) * (3 : ℕ)) := by
        rw [rpow_one, rpow_mul_natCast haR.le]
      _ = _ := by rw [← rpow_add haR]; norm_num
  have hct : Tendsto (fun a => (n a : ℝ) * |(k a : ℝ) / n a - p| ^ 3) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun a => by positivity) hcbd
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hnRt)
  have hg := local_gaussian_of_cubic p hp hp1 n k hnt hx hct
  have hgε : ∀ᶠ a in atTop,
      |binomialMass p (n a) (k a) * sqrt (2 * π * n a * p * (1 - p)) *
        exp (((k a : ℝ) - n a * p) ^ 2 / (2 * n a * p * (1 - p))) - 1| < ε := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hg ε hε)
  obtain ⟨a, ha⟩ := hgε.exists
  exact (not_lt_of_ge (hbad a)) ha

/-- Every positive natural power of the binomial mass has a negligible tail outside
`n^(7/12)`, even after multiplication by an arbitrary fixed real power of `n`.
The binomial theorem and frozen Bernoulli Pinsker inequality include `i = 0,n`.
The estimate is for the actual finite sum, not a weak limit of probability laws. -/
theorem binomial_power_tail (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (l : ℕ) (hl : 0 < l) (s : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ s *
      ∑ i ∈ (range (n + 1)).filter
        (fun i : ℕ => (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|),
        binomialMass p n i ^ l) atTop (𝓝 0) := by
  have binomial_mass_bound (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
      (n i : ℕ) (hn : 0 < n) (hi : i ≤ n) :
      binomialMass p n i ≤ exp (-2 * n * ((i : ℝ) / n - p) ^ 2) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    let x : ℝ := (i : ℝ) / n
    have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hnR.le
    have hx1 : x ≤ 1 := (div_le_one hnR).2 (by exact_mod_cast hi)
    have hmass : 0 < binomialMass p n i := by
      unfold binomialMass
      exact mul_pos (mul_pos (by exact_mod_cast Nat.choose_pos hi) (pow_pos hp _))
        (pow_pos (sub_pos.mpr hp1) _)
    have hsum : ∑ j ∈ range (n + 1), binomialMass x n j = 1 := by
      have hs := (add_pow x (1 - x) n).symm
      simpa [binomialMass, mul_comm, mul_left_comm, mul_assoc] using hs
    have hle : binomialMass x n i ≤ 1 := by
      rw [← hsum]
      unfold binomialMass
      refine single_le_sum (s := range (n + 1))
        (f := fun j : ℕ => (n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j)) ?_ ?_
      · intro j _
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
          (pow_nonneg (sub_nonneg.mpr hx1) _)
      · exact mem_range.mpr (Nat.lt_succ_of_le hi)
    have hid : log (binomialMass p n i) = log (binomialMass x n i) - n * binaryKL x p := by
      by_cases hi0 : i = 0
      · subst i
        simp [x, binomialMass, binaryKL, log_pow]
      by_cases hin : i = n
      · subst i
        simp [x, hn.ne', binomialMass, binaryKL, log_pow]
      have hiR : (0 : ℝ) < i := by exact_mod_cast Nat.pos_of_ne_zero hi0
      have hxp : 0 < x := div_pos hiR hnR
      have hxn : 0 < 1 - x := sub_pos.mpr ((div_lt_one hnR).2 (by exact_mod_cast lt_of_le_of_ne hi hin))
      have hc : (0 : ℝ) < n.choose i := by exact_mod_cast Nat.choose_pos hi
      have hnp : 0 < 1 - p := sub_pos.mpr hp1
      simp only [binomialMass,
        log_mul (mul_pos hc (pow_pos hp _)).ne' (pow_pos hnp _).ne',
        log_mul hc.ne' (pow_pos hp _).ne',
        log_mul (mul_pos hc (pow_pos hxp _)).ne' (pow_pos hxn _).ne',
        log_mul hc.ne' (pow_pos hxp _).ne', log_pow,
        binaryKL, log_div hxp.ne' hp.ne', log_div hxn.ne' hnp.ne']
      rw [Nat.cast_sub hi]
      dsimp [x]
      field_simp
      ring
    have hxmass : 0 < binomialMass x n i := by
      by_cases hi0 : i = 0
      · simp [x, hi0, binomialMass]
      by_cases hin : i = n
      · simp [x, hin, hn.ne', binomialMass]
      have hxp : 0 < x := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hi0) hnR
      have hxn : 0 < 1 - x := sub_pos.mpr ((div_lt_one hnR).2 (by exact_mod_cast lt_of_le_of_ne hi hin))
      exact mul_pos (mul_pos (by exact_mod_cast Nat.choose_pos hi) (pow_pos hxp _)) (pow_pos hxn _)
    have hlogle : log (binomialMass p n i) ≤ -n * binaryKL x p := by
      rw [hid]
      have := log_nonpos hxmass.le hle
      linarith
    have hpin := D5.S3.TotalVariation.Pinsker.binary_pinsker x p ⟨hx0, hx1⟩ ⟨hp.le, hp1.le⟩
      (fun h => (hp.ne' h).elim) (fun h => ((sub_pos.mpr hp1).ne' h).elim)
    have hexp : log (binomialMass p n i) ≤ -2 * n * (x - p) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hpin hnR.le
      dsimp [binaryKL] at hlogle
      nlinarith
    exact (log_le_iff_le_exp hmass).mp hexp
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hbound (n : ℕ) (hn : 0 < n) :
      (∑ i ∈ (range (n + 1)).filter
        (fun i : ℕ => (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|),
        binomialMass p n i ^ l) ≤
      (n + 1 : ℝ) * exp (-(2 * l) * (n : ℝ) ^ (1 / 6 : ℝ)) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hterm (i : ℕ) (hi : i ≤ n)
        (hw : (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|) :
        binomialMass p n i ^ l ≤ exp (-(2 * l) * (n : ℝ) ^ (1 / 6 : ℝ)) := by
      have hdev : (n : ℝ) ^ (1 / 6 : ℝ) ≤ n * ((i : ℝ) / n - p) ^ 2 := by
        calc
          _ = ((n : ℝ) ^ (7 / 12 : ℝ)) ^ 2 / n := by
            rw [← rpow_mul_natCast hnR.le, ← rpow_sub_one hnR.ne']
            norm_num
          _ ≤ |(i : ℝ) - n * p| ^ 2 / n := by gcongr
          _ = _ := by rw [sq_abs]; field_simp
      have hmass0 : 0 ≤ binomialMass p n i := by
        unfold binomialMass
        positivity
      calc
        _ ≤ (exp (-2 * n * ((i : ℝ) / n - p) ^ 2)) ^ l :=
          pow_le_pow_left₀ hmass0 (binomial_mass_bound p hp hp1 n i hn hi) l
        _ = exp ((l : ℝ) * (-2 * n * ((i : ℝ) / n - p) ^ 2)) := (exp_nat_mul _ _).symm
        _ ≤ _ := by
          apply exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left hdev hlR.le]
    calc
      _ ≤ ∑ _i ∈ (range (n + 1)).filter
          (fun i : ℕ => (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|),
          exp (-(2 * l) * (n : ℝ) ^ (1 / 6 : ℝ)) := by
        apply sum_le_sum
        intro i hi
        obtain ⟨hi, hw⟩ := mem_filter.mp hi
        exact hterm i (Nat.le_of_lt_succ (mem_range.mp hi)) hw
      _ ≤ ∑ _i ∈ range (n + 1), exp (-(2 * l) * (n : ℝ) ^ (1 / 6 : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => (exp_pos _).le)
      _ = _ := by simp
  have hexp : Tendsto (fun n : ℕ => (n : ℝ) ^ (s + 1) *
      exp (-(2 * l) * (n : ℝ) ^ (1 / 6 : ℝ))) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (6 * (s + 1)) (2 * l) (by positivity)).comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
    apply ht.congr'
    filter_upwards with n
    dsimp only [Function.comp_apply]
    rw [← rpow_mul (Nat.cast_nonneg n)]
    congr 2
    ring
  have hscaled : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ s *
      (∑ i ∈ (range (n + 1)).filter
        (fun i : ℕ => (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|),
        binomialMass p n i ^ l) ≤
      2 * ((n : ℝ) ^ (s + 1) * exp (-(2 * l) * (n : ℝ) ^ (1 / 6 : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
    calc
      _ ≤ (n : ℝ) ^ s * ((n + 1 : ℝ) * exp (-(2 * l) * (n : ℝ) ^ (1 / 6 : ℝ))) := by
        gcongr
        exact hbound n hn
      _ ≤ (n : ℝ) ^ s * ((2 * n : ℝ) * exp (-(2 * l) * (n : ℝ) ^ (1 / 6 : ℝ))) := by
        gcongr
        linarith
      _ = _ := by rw [rpow_add hnpos, rpow_one]; ring
  apply squeeze_zero' _ hscaled (by simpa using hexp.const_mul 2)
  filter_upwards with n
  apply mul_nonneg (rpow_nonneg (Nat.cast_nonneg n) s)
  apply sum_nonneg
  intro i _
  unfold binomialMass
  positivity

/-- A Gaussian sampled at every lattice point in the growing binomial window has
the full Gaussian integral as its normalized limit. The center `n*p` need not be
integral: comparison of the two monotone sides gives rectangle error at most three,
and the omitted finite Gaussian tail tends to zero. -/
theorem gaussian_window_sum_limit (p c : ℝ) (hp : 0 < p) (hp1 : p < 1) (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ (range (n + 1)).filter (fun i : ℕ =>
          |(i : ℝ) - n * p| ≤ (n : ℝ) ^ (7 / 12 : ℝ)),
        exp (-c * (((i : ℝ) - n * p) / sqrt n) ^ 2)) / sqrt n)
      atTop (𝓝 (sqrt (π / c))) := by
  have finite_rectangle_error (g : ℝ → ℝ) (hg : Continuous g) (n r : ℕ) (hr : r < n)
      (hb : ∀ x : ℝ, 0 ≤ g x ∧ g x ≤ 1)
      (hm : MonotoneOn g (Set.Icc (0 : ℝ) r))
      (ha : AntitoneOn g (Set.Icc (r + 1 : ℕ) (n : ℝ))) :
      |(∑ i ∈ range (n + 1), g i) - ∫ x in (0 : ℝ)..n, g x| ≤ 3 := by
    have hshift (a b : ℕ) (hab : a ≤ b) :
        (∑ i ∈ Ico a b, g (i + 1 : ℕ)) + g a =
          (∑ i ∈ Ico a b, g i) + g b := by
      rw [sum_Ico_add' (fun i : ℕ => g i) a b 1]
      have hs := sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hab) (fun i : ℕ => g i)
      rw [sum_Ico_succ_top hab] at hs
      linarith
    have hm' : MonotoneOn g (Set.Icc ((0 : ℕ) : ℝ) (r : ℝ)) := by simpa using hm
    have hL₁ := hm'.sum_le_integral_Ico (Nat.zero_le r)
    have hL₂ := hm'.integral_le_sum_Ico (Nat.zero_le r)
    have hR₁ := ha.integral_le_sum_Ico hr
    have hR₂ := ha.sum_le_integral_Ico hr
    have hsl := hshift 0 r (Nat.zero_le r)
    have hsr := hshift (r + 1) n hr
    have hic0 : 0 ≤ ∫ x in (r : ℝ)..(r + 1 : ℕ), g x :=
      integral_nonneg (by simp) (fun x _ => (hb x).1)
    have hic1 : (∫ x in (r : ℝ)..(r + 1 : ℕ), g x) ≤ 1 := by
      calc
        _ ≤ ∫ _x in (r : ℝ)..(r + 1 : ℕ), (1 : ℝ) :=
          integral_mono_on (by simp) (hg.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
            (fun x _ => (hb x).2)
        _ = 1 := by simp
    have hi : (∫ x in (0 : ℝ)..r, g x) +
        (∫ x in (r : ℝ)..(r + 1 : ℕ), g x) +
        (∫ x in (r + 1 : ℕ)..n, g x) = ∫ x in (0 : ℝ)..n, g x := by
      rw [integral_add_adjacent_intervals (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
        integral_add_adjacent_intervals (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
    have hs : (∑ i ∈ Ico 0 r, g i) + (∑ i ∈ Ico (r + 1) n, g i) +
        g r + g n = ∑ i ∈ range (n + 1), g i := by
      have h₁ := sum_Ico_consecutive (fun i : ℕ => g i) (Nat.zero_le r) (Nat.le_succ r)
      have h₂ := sum_Ico_consecutive (fun i : ℕ => g i) (Nat.zero_le (r + 1)) hr
      have h₃ := sum_range_succ (fun i : ℕ => g i) n
      simp only [Nat.Ico_succ_singleton, sum_singleton, Nat.Ico_zero_eq_range] at h₁ h₂ ⊢
      linarith
    rw [abs_le]
    simp only [Nat.cast_zero, Nat.succ_eq_add_one] at hL₁ hL₂ hR₁ hR₂ hsl
    constructor <;> linarith [(hb 0).1, (hb 0).2, (hb r).1, (hb r).2,
      (hb (r + 1 : ℕ)).1, (hb (r + 1 : ℕ)).2, (hb n).1, (hb n).2]
  have gaussian_rectangle_bound (p c : ℝ) (hp : 0 < p) (hp1 : p < 1) (hc : 0 < c)
      (n : ℕ) (hn : 0 < n) :
      |(∑ i ∈ range (n + 1), exp (-c * (((i : ℝ) - n * p) / sqrt n) ^ 2)) -
        ∫ x in (0 : ℝ)..n, exp (-c * ((x - n * p) / sqrt n) ^ 2)| ≤ 3 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hroot : 0 < sqrt (n : ℝ) := sqrt_pos.mpr hnR
    let r := ⌊(n : ℝ) * p⌋₊
    have hr : r < n := (Nat.floor_lt (by positivity : 0 ≤ (n : ℝ) * p)).2 (by nlinarith)
    have hrlo : (r : ℝ) ≤ n * p := Nat.floor_le (by positivity)
    have hrhi : (n : ℝ) * p < (r + 1 : ℕ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((n : ℝ) * p)
    refine finite_rectangle_error (fun x : ℝ => exp (-c * ((x - n * p) / sqrt n) ^ 2))
      (by fun_prop) n r hr ?_ ?_ ?_
    · intro x
      refine ⟨(exp_pos _).le, ?_⟩
      rw [exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _)
    · intro x hx y hy hxy
      apply exp_le_exp.mpr
      have hx' : (x - n * p) / sqrt n ≤ (y - n * p) / sqrt n := by gcongr
      have hy' : (y - n * p) / sqrt n ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hy.2]) hroot.le
      have hs := mul_self_le_mul_self (neg_nonneg.mpr hy') (neg_le_neg hx')
      nlinarith
    · intro x hx y hy hxy
      apply exp_le_exp.mpr
      have hx' : (x - n * p) / sqrt n ≤ (y - n * p) / sqrt n := by gcongr
      have hy' : 0 ≤ (x - n * p) / sqrt n := div_nonneg (by linarith [hx.1]) hroot.le
      have hs := mul_self_le_mul_self hy' hx'
      nlinarith
  have gaussian_finite_sum_limit (p c : ℝ) (hp : 0 < p) (hp1 : p < 1) (hc : 0 < c) :
      Tendsto (fun n : ℕ =>
        (∑ i ∈ range (n + 1), exp (-c * (((i : ℝ) - n * p) / sqrt n) ^ 2)) /
          sqrt n) atTop (𝓝 (sqrt (π / c))) := by
    have hsqrt : Tendsto (fun n : ℕ => sqrt (n : ℝ)) atTop atTop := by
      simpa only [sqrt_eq_rpow, Function.comp_def] using
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
    have hleft : Tendsto (fun n : ℕ => -(p * sqrt (n : ℝ))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hsqrt.const_mul_atTop hp)
    have hright : Tendsto (fun n : ℕ => (1 - p) * sqrt (n : ℝ)) atTop atTop :=
      hsqrt.const_mul_atTop (sub_pos.mpr hp1)
    have hint := intervalIntegral_tendsto_integral (integrable_exp_neg_mul_sq hc) hleft hright
    rw [integral_gaussian] at hint
    have hnormalized : Tendsto (fun n : ℕ =>
        (∫ x in (0 : ℝ)..n, exp (-c * ((x - n * p) / sqrt n) ^ 2)) / sqrt n)
        atTop (𝓝 (sqrt (π / c))) := by
      apply hint.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hs : 0 < sqrt (n : ℝ) := sqrt_pos.mpr hnR
      have heq : (∫ x in (0 : ℝ)..n, exp (-c * ((x - n * p) / sqrt n) ^ 2)) =
          sqrt n * ∫ x in -(p * sqrt n)..(1 - p) * sqrt n, exp (-c * x ^ 2) := by
        rw [integral_comp_sub_right (fun y => exp (-c * (y / sqrt n) ^ 2)) (n * p),
          integral_comp_div (fun y => exp (-c * y ^ 2)) hs.ne', smul_eq_mul]
        congr 2
        · field_simp
          nlinarith [sq_sqrt hnR.le]
        · field_simp
          nlinarith [sq_sqrt hnR.le]
      rw [heq, mul_div_cancel_left₀ _ hs.ne']
    have hdec : Tendsto (fun n : ℕ => 3 / sqrt (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsqrt
    have herror : ∀ᶠ n : ℕ in atTop,
        |(∑ i ∈ range (n + 1), exp (-c * (((i : ℝ) - n * p) / sqrt n) ^ 2)) / sqrt n -
          (∫ x in (0 : ℝ)..n, exp (-c * ((x - n * p) / sqrt n) ^ 2)) / sqrt n| ≤
        3 / sqrt n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [← sub_div, abs_div, abs_of_nonneg (sqrt_nonneg _)]
      exact div_le_div_of_nonneg_right (gaussian_rectangle_bound p c hp hp1 hc n hn) (sqrt_nonneg _)
    have herrlim := tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hdec.neg) hdec
      (herror.mono fun n hn => (abs_le.mp hn).1) (herror.mono fun n hn => (abs_le.mp hn).2)
    have hfinal := herrlim.add hnormalized
    simpa only [sub_add_cancel, zero_add] using hfinal
  have hterm (n i : ℕ) (hn : 0 < n)
      (hw : (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|) :
      exp (-c * (((i : ℝ) - n * p) / sqrt n) ^ 2) ≤
        exp (-c * (n : ℝ) ^ (1 / 6 : ℝ)) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hdev : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (((i : ℝ) - n * p) / sqrt n) ^ 2 := by
      calc
        _ = ((n : ℝ) ^ (7 / 12 : ℝ)) ^ 2 / n := by
          rw [← rpow_mul_natCast hnR.le, ← rpow_sub_one hnR.ne']
          norm_num
        _ ≤ |(i : ℝ) - n * p| ^ 2 / n := by gcongr
        _ = _ := by rw [div_pow, sq_sqrt hnR.le, sq_abs]
    exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left hdev (neg_nonpos.mpr hc.le))
  have hbound (n : ℕ) (hn : 1 ≤ n) :
      (∑ i ∈ (range (n + 1)).filter (fun i : ℕ =>
          (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|),
        exp (-c * (((i : ℝ) - n * p) / sqrt n) ^ 2)) / sqrt n ≤
        2 * ((n : ℝ) * exp (-c * (n : ℝ) ^ (1 / 6 : ℝ))) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs : 1 ≤ sqrt (n : ℝ) := (le_sqrt (by norm_num) (Nat.cast_nonneg n)).2 (by simpa using hnR)
    have hsum : (∑ i ∈ (range (n + 1)).filter (fun i : ℕ =>
          (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|),
        exp (-c * (((i : ℝ) - n * p) / sqrt n) ^ 2)) ≤
        (n + 1 : ℝ) * exp (-c * (n : ℝ) ^ (1 / 6 : ℝ)) := by
      calc
        _ ≤ ∑ _i ∈ (range (n + 1)).filter (fun i : ℕ =>
            (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|),
            exp (-c * (n : ℝ) ^ (1 / 6 : ℝ)) :=
          sum_le_sum fun i hi => hterm n i hn (mem_filter.mp hi).2
        _ ≤ ∑ _i ∈ range (n + 1), exp (-c * (n : ℝ) ^ (1 / 6 : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => (exp_pos _).le)
        _ = _ := by simp
    calc
      _ ≤ (n + 1 : ℝ) * exp (-c * (n : ℝ) ^ (1 / 6 : ℝ)) :=
        (div_le_self (by positivity) hs).trans hsum
      _ ≤ _ := by nlinarith [exp_pos (-c * (n : ℝ) ^ (1 / 6 : ℝ))]
  have hexp : Tendsto (fun n : ℕ => (n : ℝ) * exp (-c * (n : ℝ) ^ (1 / 6 : ℝ)))
      atTop (𝓝 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 c hc).comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
    apply ht.congr'
    filter_upwards with n
    dsimp only [Function.comp_apply]
    rw [← rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have htail : Tendsto (fun n : ℕ =>
      (∑ i ∈ (range (n + 1)).filter (fun i : ℕ =>
          (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|),
        exp (-c * (((i : ℝ) - n * p) / sqrt n) ^ 2)) / sqrt n) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity)
      ((eventually_ge_atTop 1).mono fun n hn => hbound n hn)
      (by simpa using hexp.const_mul 2)
  have hf := (gaussian_finite_sum_limit p c hp hp1 hc).sub htail
  simp only [sub_zero] at hf
  apply hf.congr'
  filter_upwards with n
  have hs := sum_filter_add_sum_filter_not (range (n + 1))
    (fun i : ℕ => |(i : ℝ) - n * p| ≤ (n : ℝ) ^ (7 / 12 : ℝ))
    (fun i : ℕ => exp (-c * (((i : ℝ) - n * p) / sqrt n) ^ 2))
  simp only [not_le] at hs
  rw [← sub_div, ← hs]
  ring

end D5.S3.AnalyticClosure.BinomialLocalGaussian
