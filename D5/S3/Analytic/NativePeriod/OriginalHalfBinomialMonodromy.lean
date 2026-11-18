/- GID: D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy
   generality: I
   mirror-B: D5/B/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.CoveringMap, mathlib/module/Mathlib.Topology.Homotopy.Lifting]
   utility: none
   digest: Actual native period germ continuation along every punctured-disk path and its endpoint monodromy. -/

import D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-! The path certificate consists of the explicit native holomorphic charts.
The covering and uniqueness results are the existing Mathlib theorems. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter unitInterval
open scoped Topology

namespace D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
open OriginalHalfBinomialPeriod (period)
open OriginalHalfBinomialDiskCorrection
open OriginalHalfBinomialContinuation
open OriginalHalfBinomialLocalCharts

def b : ℂ := 1 / 2
def baseLog : ℂ := Complex.log b
def deck (k : ℤ) : ℂ := k * (2 * (Real.pi : ℂ) * Complex.I)

/-- A certificate for this particular native pair: holomorphic r-charts,
their equations, neighborhood transition germs, and the actual initial germ. -/
structure NativeCharts (γ L : C(I, ℂ)) : Prop where
  projection : ∀ t, Complex.exp (L t) = γ t
  halfPlane : ∀ t, L t ∈ E
  inverseAlong : ∀ t, ∀ᶠ s in 𝓝 t, localLog (L t) (γ s) = L s
  germAlong : ∀ t, ∀ᶠ s in 𝓝 t,
    chartN (L t) =ᶠ[𝓝 (γ s)] chartN (L s)
  holomorphic : ∀ t, DifferentiableOn ℂ (chartN (L t)) (chartDomain (L t))
  equation : ∀ t, ∀ r ∈ chartDomain (L t),
    DifferentiableAt ℂ (deriv (chartN (L t))) r ∧
    r * (1 - r) * deriv (deriv (chartN (L t))) r +
      (1 - 2 * r) * deriv (chartN (L t)) r - (1 / 4 : ℂ) * chartN (L t) r = 0 ∧
    deriv (chartN (L t)) r * period r - chartN (L t) r * deriv period r =
      -Complex.I / ((Real.pi : ℂ) * r * (1 - r))
  initial : chartN (L 0) =ᶠ[𝓝 b] (fun r => Complex.I * period (1 - r))

private lemma base_lens : b ∈ lens := by
  norm_num [b, lens, Metric.mem_ball, dist_eq_norm]

private lemma base_exp : Complex.exp baseLog = b :=
  Complex.exp_log (by norm_num [b])

private lemma base_E : baseLog ∈ E := (native_initial_germ b base_lens).1

private lemma native_certificate (γ L : C(I, ℂ)) (hD : ∀ t, ‖γ t‖ < 1)
    (he : ∀ t, Complex.exp (L t) = γ t) (hL0 : L 0 = baseLog) : NativeCharts γ L := by
  have hE (t : I) : L t ∈ E := by
    have h := hD t
    rw [← he t, Complex.norm_exp, ← Real.exp_zero, Real.exp_lt_exp] at h
    exact h
  have hnear (t : I) : ∀ᶠ s in 𝓝 t, (L s - L t).im ∈ Ioo (-Real.pi) Real.pi := by
    apply (isOpen_Ioo.preimage (by fun_prop : Continuous (fun s : I => (L s - L t).im))).mem_nhds
    simp [Real.pi_pos]
  refine ⟨he, hE, ?_, ?_, fun t => (chart_equations (L t)).2.1,
    fun t r hr => ((chart_equations (L t)).2.2 r hr).2, ?_⟩
  · intro t
    filter_upwards [hnear t] with s hs
    rw [← he s, localLog, ← Complex.exp_sub, Complex.log_exp hs.1 hs.2.le]
    ring
  · intro t
    filter_upwards [hnear t] with s hs
    simpa only [he s] using (chart_transition (L t) (L s) (hE s) hs).2.2
  · rw [hL0]
    exact (native_initial_germ b base_lens).2.1

/-- Every continuous path in the full punctured complex disk has a unique
normalized exponential lift, and that lift supplies actual native germ charts. -/
theorem native_path_continuation (γ : C(I, ℂ)) (hD : ∀ t, ‖γ t‖ < 1)
    (hn : ∀ t, γ t ≠ 0) (hb : γ 0 = b) :
    ∃! L : C(I, ℂ), L 0 = baseLog ∧ NativeCharts γ L := by
  let g : C(I, {r : ℂ // r ≠ 0}) :=
    ⟨fun t => ⟨γ t, hn t⟩, γ.continuous.subtype_mk _⟩
  have h0 : g 0 = (⟨Complex.exp baseLog, Complex.exp_ne_zero baseLog⟩ : {r : ℂ // r ≠ 0}) :=
    Subtype.ext (hb.trans base_exp.symm)
  let L := Complex.isCoveringMap_exp.liftPath g baseLog h0
  have he : ∀ t, Complex.exp (L t) = γ t := fun t =>
    congrArg Subtype.val (congr_fun (Complex.isCoveringMap_exp.liftPath_lifts g baseLog h0) t)
  have hL0 : L 0 = baseLog := Complex.isCoveringMap_exp.liftPath_zero g baseLog h0
  refine ⟨L, ⟨hL0, native_certificate γ L hD he hL0⟩, ?_⟩
  intro M hM
  apply (Complex.isCoveringMap_exp.eq_liftPath_iff' h0).mpr
  exact ⟨funext (fun t => Subtype.ext (hM.2.projection t)), hM.1⟩

private lemma chart_shift (z : ℂ) (k : ℤ) :
    chartT (z + deck k) = (fun r => chartT z r + 2 * k) ∧
    chartN (z + deck k) = (fun r => chartN z r + 2 * k * period r) := by
  have he : Complex.exp (z + deck k) = Complex.exp z :=
    Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩
  have ht : ∀ r, chartT (z + deck k) r = chartT z r + 2 * k := by
    intro r
    have hd := (cover_periods.2.2.2 (localLog z r) k).1
    have hep : Complex.exp (localLog z r + k * (2 * (Real.pi : ℂ) * Complex.I)) =
        Complex.exp (localLog z r) :=
      Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩
    dsimp only [T] at hd
    rw [hep] at hd
    dsimp only [chartT, localLog]
    rw [he]
    dsimp only [localLog] at hd
    dsimp only [deck]
    linear_combination hd
  exact ⟨funext ht, funext (fun r => by rw [chartN, ht]; dsimp [chartN]; ring)⟩

/-- A loop's endpoint integer is obtained from exp equality. Its returned
holomorphic germ is the native numerator plus 2k times the native denominator. -/
theorem native_loop_monodromy (γ : C(I, ℂ)) (hD : ∀ t, ‖γ t‖ < 1)
    (hn : ∀ t, γ t ≠ 0) (hb : γ 0 = b) (hb1 : γ 1 = b) :
    ∃ L : C(I, ℂ), ∃ k : ℤ, L 0 = baseLog ∧ NativeCharts γ L ∧
      L 1 = baseLog + deck k ∧
      chartN (L 1) =ᶠ[𝓝 b]
        (fun r => Complex.I * period (1 - r) + 2 * k * period r) ∧
      chartT (L 1) =ᶠ[𝓝 b]
        (fun r => OriginalHalfBinomialWronskian.tau r + 2 * k) := by
  obtain ⟨L, hL, _⟩ := native_path_continuation γ hD hn hb
  have he : Complex.exp (L 1) = Complex.exp baseLog := (hL.2.projection 1).trans (hb1.trans base_exp.symm)
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  change L 1 = baseLog + deck k at hk
  refine ⟨L, k, hL.1, hL.2, hk, ?_, ?_⟩
  · rw [hk, (chart_shift baseLog k).2]
    filter_upwards [(native_initial_germ b base_lens).2.1] with r hr
    change chartN (Complex.log b) r + _ = _
    rw [hr]
  · rw [hk, (chart_shift baseLog k).1]
    filter_upwards [(native_initial_germ b base_lens).2.2] with r hr
    change chartT (Complex.log b) r + _ = _
    rw [hr]

/-- The positive circle and its explicitly oriented lift. -/
def gamma0 : C(I, ℂ) := ⟨fun t => b * Complex.exp ((t : ℝ) * (2 * (Real.pi : ℂ) * Complex.I)), by fun_prop⟩

def positiveLift : C(I, ℂ) :=
  ⟨fun t => baseLog + (t : ℝ) * (2 * (Real.pi : ℂ) * Complex.I), by fun_prop⟩

private lemma positive_projects (t : I) : Complex.exp (positiveLift t) = gamma0 t := by
  change Complex.exp (baseLog + _) = b * _
  rw [Complex.exp_add, base_exp]

private lemma gamma0_disk (t : I) : ‖gamma0 t‖ < 1 := by
  norm_num [gamma0, b, norm_mul, Complex.norm_exp, Complex.mul_re]

private lemma positive_zero : positiveLift 0 = baseLog := by simp [positiveLift]

/-- The actual positively oriented loop returns the A0 native germ,
with A0 acting on (n,y) by (n+2y,y). -/
theorem positive_zero_monodromy :
    NativeCharts gamma0 positiveLift ∧ positiveLift 1 = baseLog + deck 1 ∧
    chartN (positiveLift 1) =ᶠ[𝓝 b]
      (fun r => Complex.I * period (1 - r) + 2 * period r) := by
  refine ⟨native_certificate gamma0 positiveLift gamma0_disk positive_projects positive_zero,
    by simp [positiveLift, deck], ?_⟩
  have he : positiveLift 1 = baseLog + deck 1 := by simp [positiveLift, deck]
  rw [he, (chart_shift baseLog 1).2]
  filter_upwards [(native_initial_germ b base_lens).2.1] with r hr
  dsimp only [baseLog]
  norm_num only [Int.cast_one, mul_one]
  rw [hr]

end D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
