/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inclusive finite Abel summation identifies the independent original signed J integral. -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
The signed J below is defined by its original integral. No finite-expression
identity is a hypothesis. The only test-function assumptions are AC and a.e.
agreement of the supplied derivative with an actual derivative.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace OriginalSignedJ

def cutoff (t : ℝ) : Finset ℕ := Finset.Icc 2 ⌊Real.exp t⌋₊

def b (t : ℝ) : ℝ :=
  Real.eulerMascheroniConstant - t +
    ∑ n ∈ cutoff t, ArithmeticFunction.vonMangoldt n / (n : ℝ)

def testLift (f : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp (t / 2) * f t

/-- Independent original definition, including the factor 2. -/
def J (D : ℝ) (f fprime : ℝ → ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..D,
    b t * Real.exp (t / 2) * (fprime t + f t / 2)

def fullR (D Z : ℝ) (f : ℝ → ℝ) : ℝ :=
  2 * (∑ n ∈ cutoff D,
    ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) * f (Real.log n)) -
  2 * (∫ t in (0 : ℝ)..D, Real.exp (t / 2) * f t) + b D * Z / 2

/-- A finite-horizon representation; this is not a definition of the original b. -/
def finiteB {ι : Type*} (s : Finset ι) (γ : ℝ) (w k : ι → ℝ) (t : ℝ) : ℝ :=
  γ - t + ∑ i ∈ s, if k i ≤ t then w i else 0

lemma indicator_tail_integrable {g : ℝ → ℝ} {D : ℝ}
    (hg : IntervalIntegrable g volume 0 D) (a : ℝ) :
    IntervalIntegrable ((Ici a).indicator g) volume 0 D := by
  exact intervalIntegrable_iff.mpr (hg.def'.indicator measurableSet_Ici)

/-- Closed inclusion at the knot; the equality case a = D is included. -/
lemma integral_indicator_tail {g : ℝ → ℝ} {D a : ℝ}
    (ha : 0 ≤ a) (haD : a ≤ D) :
    (∫ t in (0 : ℝ)..D, (Ici a).indicator g t) = ∫ t in a..D, g t := by
  have hinter : Ici a ∩ Icc 0 D = Icc a D := by
    ext t
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨hat, _, htD⟩
      exact ⟨hat, htD⟩
    · rintro ⟨hat, htD⟩
      exact ⟨hat, ha.trans hat, htD⟩
  rw [intervalIntegral.integral_of_le (ha.trans haD),
    ← integral_Icc_eq_integral_Ioc, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, hinter,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haD]

lemma finiteB_mul_integrable {ι : Type*} (s : Finset ι) (γ : ℝ) (w k : ι → ℝ)
    {g : ℝ → ℝ} {D : ℝ} (hg : IntervalIntegrable g volume 0 D) :
    IntervalIntegrable (fun t => finiteB s γ w k t * g t) volume 0 D := by
  classical
  have hi (i : ι) : IntervalIntegrable
      (fun t => (if k i ≤ t then w i else 0) * g t) volume 0 D := by
    convert (indicator_tail_integrable hg (k i)).const_mul (w i) using 1
    ext t
    by_cases ht : k i ≤ t <;> simp [Set.indicator, ht]
  have hs := IntervalIntegrable.sum s (fun i _ => hi i)
  have hc := hg.continuousOn_mul
    ((continuous_const : Continuous (fun _ : ℝ => γ)).sub continuous_id).continuousOn
  convert hc.add hs using 1
  ext t
  simp [finiteB, Finset.sum_apply, add_mul, Finset.sum_mul]

/-- Finite indicator/Fubini plus AC integration by parts, with no smoothness
assumption at the knots and no assumed Abel identity. -/
theorem finite_abel_ac {ι : Type*} (s : Finset ι) (γ : ℝ) (w k : ι → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hk : ∀ i ∈ s, k i ∈ Icc 0 D)
    {H : ℝ → ℝ} (hH : AbsolutelyContinuousOnInterval H 0 D) :
    (∑ i ∈ s, w i * H (k i)) - (∫ t in (0 : ℝ)..D, H t) -
      (γ - D + ∑ i ∈ s, w i) * H D =
    -γ * H 0 - ∫ t in (0 : ℝ)..D, finiteB s γ w k t * deriv H t := by
  classical
  have hg := hH.intervalIntegrable_deriv
  have hi (i : ι) : IntervalIntegrable
      (fun t => (if k i ≤ t then w i else 0) * deriv H t) volume 0 D := by
    convert (indicator_tail_integrable hg (k i)).const_mul (w i) using 1
    ext t
    by_cases ht : k i ≤ t <;> simp [Set.indicator, ht]
  have ht := hg.continuousOn_mul (continuous_id : Continuous (fun t : ℝ => t)).continuousOn
  have hid : AbsolutelyContinuousOnInterval (fun t : ℝ => t) 0 D :=
    (contDiff_id : ContDiff ℝ 1 (fun t : ℝ => t)).contDiffOn.absolutelyContinuousOnInterval
  have hparts := hid.integral_mul_deriv_eq_deriv_mul hH
  simp only [deriv_id'', one_mul, zero_mul, sub_zero] at hparts
  have hprimitive := hH.integral_deriv_eq_sub
  have htail (i : ι) (hiS : i ∈ s) :
      (∫ t in (0 : ℝ)..D, (if k i ≤ t then w i else 0) * deriv H t) =
        w i * (H D - H (k i)) := by
    have hsmall : AbsolutelyContinuousOnInterval H (k i) D := by
      apply hH.mono
      rw [uIcc_of_le (hk i hiS).2, uIcc_of_le hD]
      exact Icc_subset_Icc (hk i hiS).1 le_rfl
    calc
      _ = w i * (∫ t in (0 : ℝ)..D, (Ici (k i)).indicator (deriv H) t) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _
        by_cases ht : k i ≤ t <;> simp [Set.indicator, ht]
      _ = w i * (∫ t in k i..D, deriv H t) := by
        rw [integral_indicator_tail (hk i hiS).1 (hk i hiS).2]
      _ = w i * (H D - H (k i)) := by rw [hsmall.integral_deriv_eq_sub]
  have hexpand :
      (∫ t in (0 : ℝ)..D, finiteB s γ w k t * deriv H t) =
        γ * (H D - H 0) - (D * H D - ∫ t in (0 : ℝ)..D, H t) +
          ∑ i ∈ s, w i * (H D - H (k i)) := by
    calc
      _ = ∫ t in (0 : ℝ)..D,
          (γ * deriv H t - t * deriv H t) +
            ∑ i ∈ s, (if k i ≤ t then w i else 0) * deriv H t := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [finiteB, add_mul, sub_mul, Finset.sum_mul]
      _ = _ := by
        have hadd := intervalIntegral.integral_add ((hg.const_mul γ).sub ht)
          (IntervalIntegrable.sum s (fun i _ => hi i))
        calc
          _ = (∫ t in (0 : ℝ)..D, γ * deriv H t - t * deriv H t) +
              ∫ t in (0 : ℝ)..D,
                (∑ i ∈ s, fun u => (if k i ≤ u then w i else 0) * deriv H u) t := by
            convert hadd using 1 <;> simp
          _ = _ := by
            have hsub := intervalIntegral.integral_sub (hg.const_mul γ) ht
            have hparts' :
                (∫ x in (0 : ℝ)..D, id x * deriv H x) =
                  D * H D - ∫ x in (0 : ℝ)..D, H x := by
              simpa only [id_eq] using hparts
            rw [intervalIntegral.integral_const_mul, hprimitive, hparts'] at hsub
            have hsub' :
                (∫ t in (0 : ℝ)..D, γ * deriv H t - t * deriv H t) =
                  γ * (H D - H 0) - (D * H D - ∫ t in (0 : ℝ)..D, H t) := by
              simpa only [id_eq] using hsub
            rw [hsub']
            have hsum :
                (∫ t in (0 : ℝ)..D,
                  (∑ i ∈ s, fun u => (if k i ≤ u then w i else 0) * deriv H u) t) =
                  ∑ i ∈ s, ∫ t in (0 : ℝ)..D,
                    (if k i ≤ t then w i else 0) * deriv H t := by
              convert intervalIntegral.integral_finsetSum (fun i _ => hi i) using 1 <;> simp
            rw [hsum]
            congr 1
            exact Finset.sum_congr rfl htail
  rw [hexpand]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

lemma cutoff_knot {D : ℝ} (hD : 0 ≤ D) {n : ℕ} (hn : n ∈ cutoff D) :
    Real.log (n : ℝ) ∈ Icc 0 D := by
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  exact ⟨Real.log_nonneg hn1,
    (Real.log_le_iff_le_exp hn0).mpr
      ((Nat.le_floor_iff (Real.exp_nonneg D)).mp (Finset.mem_Icc.mp hn).2)⟩

lemma finiteB_eq_b {D t : ℝ} (ht : t ≤ D) :
    finiteB (cutoff D) Real.eulerMascheroniConstant
      (fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ))
      (fun n => Real.log (n : ℝ)) t = b t := by
  classical
  have hsub : cutoff t ⊆ cutoff D := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans (Nat.floor_mono (Real.exp_le_exp.mpr ht))⟩
  unfold finiteB b
  congr 1
  calc
    _ = ∑ n ∈ cutoff t,
        if Real.log (n : ℝ) ≤ t then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro n hnD hnt
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (by have := (Finset.mem_Icc.mp hnD).1; omega : 0 < n)
      have hnlog : ¬ Real.log (n : ℝ) ≤ t := by
        intro hnlog
        apply hnt
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnD).1,
          (Nat.le_floor_iff (Real.exp_nonneg t)).mpr
            ((Real.log_le_iff_le_exp hn0).mp hnlog)⟩
      simp [hnlog]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 0 < n)
      rw [if_pos ((Real.log_le_iff_le_exp hn0).mpr
        ((Nat.le_floor_iff (Real.exp_nonneg t)).mp (Finset.mem_Icc.mp hn).2))]

lemma testLift_ac {D : ℝ} {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 D) :
    AbsolutelyContinuousOnInterval (testLift f) 0 D := by
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (t / 2)) := by fun_prop
  exact he.contDiffOn.absolutelyContinuousOnInterval.fun_mul hf

lemma testLift_ae_deriv {D : ℝ} {f fprime : ℝ → ℝ}
    (hfp : ∀ᵐ t : ℝ, t ∈ uIcc 0 D → HasDerivAt f (fprime t) t) :
    ∀ᵐ t : ℝ, t ∈ uIcc 0 D →
      deriv (testLift f) t = Real.exp (t / 2) * (fprime t + f t / 2) := by
  filter_upwards [hfp] with t ht htD
  have he : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (Real.exp (t / 2) / 2) t := by
    have h := (Real.hasDerivAt_exp (t / 2)).comp t
      ((hasDerivAt_id t).div_const (2 : ℝ))
    simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using h
  have hp := (he.mul (ht htD)).deriv
  change deriv ((fun t : ℝ => Real.exp (t / 2)) * f) t = _
  calc
    _ = Real.exp (t / 2) / 2 * f t +
        Real.exp (t / 2) * fprime t := by simpa [testLift] using hp
    _ = Real.exp (t / 2) * (fprime t + f t / 2) := by ring

lemma original_integrands_integrable {D : ℝ} (hD : 0 ≤ D) {f fprime : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 D)
    (hfp : ∀ᵐ t : ℝ, t ∈ uIcc 0 D → HasDerivAt f (fprime t) t) :
    IntervalIntegrable (testLift f) volume 0 D ∧
    IntervalIntegrable (fun t => b t * Real.exp (t / 2) * (fprime t + f t / 2))
      volume 0 D := by
  have hH := testLift_ac hf
  refine ⟨hH.continuousOn.intervalIntegrable, ?_⟩
  have hi := finiteB_mul_integrable (cutoff D) Real.eulerMascheroniConstant
    (fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ))
    (fun n => Real.log (n : ℝ)) hH.intervalIntegrable_deriv
  apply hi.congr_ae
  filter_upwards [ae_restrict_of_ae (testLift_ae_deriv hfp),
    ae_restrict_mem measurableSet_uIoc] with t ht htD
  have htcc : t ∈ uIcc 0 D := uIoc_subset_uIcc htD
  have htD' : t ≤ D := (uIcc_of_le hD ▸ htcc).2
  rw [finiteB_eq_b htD', ht htcc]
  ring

lemma weight_testLift {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) :
    ArithmeticFunction.vonMangoldt n / (n : ℝ) * testLift f (Real.log n) =
      ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) * f (Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold testLift
  rw [Real.exp_half, Real.exp_log hn0]
  calc
    _ = ArithmeticFunction.vonMangoldt n * (Real.sqrt (n : ℝ) / (n : ℝ)) *
        f (Real.log n) := by ring
    _ = _ := by rw [Real.sqrt_div_self]; simp only [div_eq_mul_inv]

/-- The exact original identity. D = 0 and n = exp D are included. -/
theorem original_J_identity {D : ℝ} (hD : 0 ≤ D) {f fprime : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 D)
    (hfp : ∀ᵐ t : ℝ, t ∈ uIcc 0 D → HasDerivAt f (fprime t) t) :
    2 * (∑ n ∈ cutoff D,
      ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) * f (Real.log n)) -
      2 * (∫ t in (0 : ℝ)..D, Real.exp (t / 2) * f t) -
      2 * b D * Real.exp (D / 2) * f D =
    -2 * Real.eulerMascheroniConstant * f 0 - J D f fprime := by
  have h := finite_abel_ac (cutoff D) Real.eulerMascheroniConstant
    (fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ))
    (fun n => Real.log (n : ℝ)) hD (fun _ hn => cutoff_knot hD hn) (testLift_ac hf)
  have hj :
      (∫ t in (0 : ℝ)..D, finiteB (cutoff D) Real.eulerMascheroniConstant
        (fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ))
        (fun n => Real.log (n : ℝ)) t * deriv (testLift f) t) =
      ∫ t in (0 : ℝ)..D, b t * Real.exp (t / 2) * (fprime t + f t / 2) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [testLift_ae_deriv hfp] with t ht htD
    have htcc : t ∈ uIcc 0 D := uIoc_subset_uIcc htD
    have htD' : t ≤ D := (uIcc_of_le hD ▸ htcc).2
    rw [finiteB_eq_b htD', ht htcc]
    ring
  have hsum :
      (∑ n ∈ cutoff D, ArithmeticFunction.vonMangoldt n / (n : ℝ) *
        testLift f (Real.log n)) =
      ∑ n ∈ cutoff D, ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) *
        f (Real.log n) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact weight_testLift (by have := (Finset.mem_Icc.mp hn).1; omega) f
  rw [hj, hsum] at h
  change _ - _ - b D * testLift f D = _ at h
  simp only [testLift, zero_div, Real.exp_zero, one_mul] at h
  unfold J
  linear_combination 2 * h

/-- Exact endpoint substitution only; the genuine correlation/resolvent
endpoint must be supplied by its own proof, not inferred from J. -/
theorem fullR_eq_original_J {D Z : ℝ} (hD : 0 ≤ D) {f fprime : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 D)
    (hfp : ∀ᵐ t : ℝ, t ∈ uIcc 0 D → HasDerivAt f (fprime t) t)
    (hend : f D = -Real.exp (-D / 2) * Z / 4) :
    fullR D Z f = -2 * Real.eulerMascheroniConstant * f 0 - J D f fprime := by
  have h := original_J_identity hD hf hfp
  have he : Real.exp (D / 2) * Real.exp (-D / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hboundary : -2 * b D * Real.exp (D / 2) * f D = b D * Z / 2 := by
    rw [hend]
    calc
      _ = (b D * Z / 2) * (Real.exp (D / 2) * Real.exp (-D / 2)) := by ring
      _ = _ := by rw [he, mul_one]
  unfold fullR
  linear_combination h - hboundary

end OriginalSignedJ
