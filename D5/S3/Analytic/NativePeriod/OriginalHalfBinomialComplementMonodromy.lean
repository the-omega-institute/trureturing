/- GID: D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy
   generality: I
   mirror-B: D5/B/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Homotopy.Lifting]
   utility: none
   digest: Complementary native period charts with exact orientation and scalar phase at one. -/

import D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy

/-! The complementary coordinate is s=1-r. The ordered native pair is
(iP(s),-i n(s)); no nonvanishing assumption on its second component is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter unitInterval
open scoped Topology

namespace D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
open OriginalHalfBinomialPeriod (period)
open OriginalHalfBinomialDiskCorrection
open OriginalHalfBinomialContinuation
open OriginalHalfBinomialLocalCharts
open OriginalHalfBinomialMonodromy

def complementDomain (z : ℂ) : Set ℂ := {r | 1 - r ∈ chartDomain z}
def complementN (r : ℂ) : ℂ := Complex.I * period (1 - r)
def complementY (z r : ℂ) : ℂ := -Complex.I * chartN z (1 - r)
def complementPath (γ : C(I, ℂ)) : C(I, ℂ) := ⟨fun t => 1 - γ t, by fun_prop⟩
def gamma1 : C(I, ℂ) := complementPath gamma0

private lemma reflected_derivatives (f : ℂ → ℂ) (a r : ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hr : 1 - r ∈ U)
    (hf : ∀ s ∈ U, DifferentiableAt ℂ f s)
    (hf' : DifferentiableAt ℂ (deriv f) (1 - r)) :
    DifferentiableAt ℂ (fun w => a * f (1 - w)) r ∧
    deriv (fun w => a * f (1 - w)) r = -a * deriv f (1 - r) ∧
    DifferentiableAt ℂ (deriv (fun w => a * f (1 - w))) r ∧
    deriv (deriv (fun w => a * f (1 - w))) r = a * deriv (deriv f) (1 - r) := by
  have hd (w : ℂ) (hw : 1 - w ∈ U) :
      HasDerivAt (fun v => a * f (1 - v)) (-a * deriv f (1 - w)) w := by
    convert ((hf _ hw).hasDerivAt.comp w ((hasDerivAt_id w).const_sub 1)).const_mul a using 1
    · funext v; rfl
    · ring
  have he : deriv (fun w => a * f (1 - w)) =ᶠ[𝓝 r]
      (fun w => -a * deriv f (1 - w)) := by
    filter_upwards [(hU.preimage (by fun_prop : Continuous (fun w : ℂ => 1 - w))).mem_nhds hr] with w hw
    exact (hd w hw).deriv
  have hd2 : HasDerivAt (deriv (fun w => a * f (1 - w)))
      (a * deriv (deriv f) (1 - r)) r := by
    convert ((hf'.hasDerivAt.comp r ((hasDerivAt_id r).const_sub 1)).const_mul (-a)).congr_of_eventuallyEq he using 1
    ring
  exact ⟨(hd r hr).differentiableAt, (hd r hr).deriv, hd2.differentiableAt, hd2.deriv⟩

/-- Both complementary components solve the same native differential equation,
with the same oriented Wronskian on every complementary chart. -/
theorem complementary_equations (z : ℂ) :
    DifferentiableOn ℂ complementN (complementDomain z) ∧
    DifferentiableOn ℂ (complementY z) (complementDomain z) ∧
    (∀ r ∈ complementDomain z,
      DifferentiableAt ℂ (deriv complementN) r ∧
      DifferentiableAt ℂ (deriv (complementY z)) r ∧
      r * (1 - r) * deriv (deriv complementN) r +
        (1 - 2 * r) * deriv complementN r - (1 / 4 : ℂ) * complementN r = 0 ∧
      r * (1 - r) * deriv (deriv (complementY z)) r +
        (1 - 2 * r) * deriv (complementY z) r - (1 / 4 : ℂ) * complementY z r = 0 ∧
      deriv complementN r * complementY z r - complementN r * deriv (complementY z) r =
        -Complex.I / ((Real.pi : ℂ) * r * (1 - r))) := by
  have hU : IsOpen (chartDomain z) :=
    Metric.isOpen_ball.inter (Complex.isOpen_slitPlane.preimage (by fun_prop))
  have hp (s : ℂ) (hs : s ∈ chartDomain z) :=
    OriginalHalfBinomialPeriod.picard_fuchs (z := s) (by simpa [disk] using hs.1)
  have hn (s : ℂ) (hs : s ∈ chartDomain z) := (chart_equations z).2.2 s hs
  have dn (r : ℂ) (hr : r ∈ complementDomain z) :=
    reflected_derivatives period Complex.I r (chartDomain z) hU hr
      (fun s hs => (hp s hs).1) (hp _ hr).2.1
  have dy (r : ℂ) (hr : r ∈ complementDomain z) :=
    reflected_derivatives (chartN z) (-Complex.I) r (chartDomain z) hU hr
      (fun s hs => (chart_equations z).2.1.differentiableAt (hU.mem_nhds hs)) (hn _ hr).2.1
  refine ⟨fun r hr => (dn r hr).1.differentiableWithinAt,
    fun r hr => (dy r hr).1.differentiableWithinAt, ?_⟩
  intro r hr
  refine ⟨(dn r hr).2.2.1, (dy r hr).2.2.1, ?_, ?_, ?_⟩
  · change r * (1 - r) * deriv (deriv (fun w => Complex.I * period (1 - w))) r +
      (1 - 2 * r) * deriv (fun w => Complex.I * period (1 - w)) r -
      (1 / 4 : ℂ) * (Complex.I * period (1 - r)) = 0
    rw [(dn r hr).2.2.2, (dn r hr).2.1]
    linear_combination Complex.I * (hp _ hr).2.2
  · change r * (1 - r) * deriv (deriv (fun w => -Complex.I * chartN z (1 - w))) r +
      (1 - 2 * r) * deriv (fun w => -Complex.I * chartN z (1 - w)) r -
      (1 / 4 : ℂ) * (-Complex.I * chartN z (1 - r)) = 0
    rw [(dy r hr).2.2.2, (dy r hr).2.1]
    linear_combination -Complex.I * (hn _ hr).2.2.1
  · change deriv (fun w => Complex.I * period (1 - w)) r * _ -
      _ * deriv (fun w => -Complex.I * chartN z (1 - w)) r = _
    rw [(dn r hr).2.1, (dy r hr).2.1]
    dsimp [complementN, complementY]
    have hw := (hn _ hr).2.2.2
    have ha : (1 - r) * (1 - (1 - r)) = r * (1 - r) := by ring
    have hw' : deriv (chartN z) (1 - r) * period (1 - r) -
        chartN z (1 - r) * deriv period (1 - r) =
        -Complex.I / ((Real.pi : ℂ) * r * (1 - r)) := by
      convert hw using 1 <;> congr 1 <;> ring
    calc
      _ = -(Complex.I ^ 2) * (deriv (chartN z) (1 - r) * period (1 - r) -
          chartN z (1 - r) * deriv period (1 - r)) := by ring
      _ = _ := by rw [Complex.I_sq, neg_neg, one_mul, hw']

private lemma complement_base : 1 - b = b := by norm_num [b]

/-- The complementary charts have exactly the native scalar phase on the full
complex overlap, as an equality of germs rather than a pointwise match. -/
theorem complementary_initial_germ (r : ℂ) (hr : r ∈ lens) :
    complementY (Complex.log (1 - r)) =ᶠ[𝓝 r] period := by
  have hn : ‖r‖ < 1 ∧ ‖1 - r‖ < 1 := by
    simpa only [lens, mem_inter_iff, Metric.mem_ball, dist_eq_norm,
      sub_zero, norm_sub_rev] using hr
  have hs : 1 - r ∈ lens := by
    constructor
    · simpa [Metric.mem_ball, dist_zero_right] using hn.2
    · simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hn.1
  have he := (native_initial_germ (1 - r) hs).2.1.comp_tendsto
    ((by fun_prop : Continuous (fun s : ℂ => 1 - s)).continuousAt (x := r)).tendsto
  filter_upwards [he] with s hss
  dsimp only [Function.comp_def] at hss
  dsimp only [complementY]
  rw [hss]
  simp only [sub_sub_cancel]
  rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

private lemma initial_y : complementY baseLog =ᶠ[𝓝 b] period := by
  simpa only [complement_base, baseLog] using complementary_initial_germ b
    (by norm_num [b, lens, Metric.mem_ball, dist_eq_norm])

/-- Continuation along any full complementary punctured-disk path. The
transformed charts glue as germs and start at the literal native denominator. -/
theorem complementary_path_continuation (γ : C(I, ℂ))
    (hD : ∀ t, ‖1 - γ t‖ < 1) (hn : ∀ t, γ t ≠ 1) (hb : γ 0 = b) :
    ∃ L : C(I, ℂ), L 0 = baseLog ∧ NativeCharts (complementPath γ) L ∧
      (∀ t, ∀ᶠ s in 𝓝 t, complementY (L t) =ᶠ[𝓝 (γ s)] complementY (L s)) ∧
      complementY (L 0) =ᶠ[𝓝 b] period := by
  obtain ⟨L, hL, _⟩ := native_path_continuation (complementPath γ) hD
    (fun t => sub_ne_zero.mpr (Ne.symm (hn t))) (by change 1 - γ 0 = b; rw [hb, complement_base])
  refine ⟨L, hL.1, hL.2, ?_, ?_⟩
  · intro t
    filter_upwards [hL.2.germAlong t] with s hs
    have he := hs.comp_tendsto
      (show Tendsto (fun r : ℂ => 1 - r) (𝓝 (γ s)) (𝓝 (complementPath γ s)) from
        (continuous_const.sub continuous_id).continuousAt.tendsto)
    exact he.mono (fun r hr => by dsimp [complementY]; rw [show chartN (L t) (1 - r) = chartN (L s) (1 - r) from hr])
  · rw [hL.1]
    exact initial_y

/-- The positive complementary circle has the same positive exponential lift.
Its exact native action is A1:(n,y)↦(n,y-2n). -/
theorem positive_one_monodromy :
    NativeCharts (complementPath gamma1) positiveLift ∧
    complementY (positiveLift 0) =ᶠ[𝓝 b] period ∧
    complementY (positiveLift 1) =ᶠ[𝓝 b]
      (fun r => period r - 2 * Complex.I * period (1 - r)) := by
  have hpath : complementPath gamma1 = gamma0 := by
    ext t
    simp [complementPath, gamma1]
  refine ⟨hpath ▸ positive_zero_monodromy.1, ?_, ?_⟩
  · simpa [positiveLift] using initial_y
  · have he := positive_zero_monodromy.2.2.comp_tendsto
      (show Tendsto (fun r : ℂ => 1 - r) (𝓝 b) (𝓝 b) by
        simpa only [complement_base] using
          ((by fun_prop : Continuous (fun r : ℂ => 1 - r)).continuousAt (x := b)).tendsto)
    filter_upwards [he] with r hr
    dsimp [Function.comp_def] at hr
    dsimp only [complementY]
    rw [hr]
    simp only [sub_sub_cancel]
    linear_combination -(period r) * Complex.I_sq

/-- Every based complementary loop returns the literal denominator germ
y-2kn, where k is the endpoint integer of its positive complementary lift. -/
theorem complementary_loop_monodromy (γ : C(I, ℂ))
    (hD : ∀ t, ‖1 - γ t‖ < 1) (hn : ∀ t, γ t ≠ 1)
    (hb : γ 0 = b) (hb1 : γ 1 = b) :
    ∃ L : C(I, ℂ), ∃ k : ℤ, L 0 = baseLog ∧ NativeCharts (complementPath γ) L ∧
      L 1 = baseLog + deck k ∧
      complementY (L 0) =ᶠ[𝓝 b] period ∧
      complementY (L 1) =ᶠ[𝓝 b]
        (fun r => period r - 2 * k * Complex.I * period (1 - r)) := by
  obtain ⟨L, k, hL0, hc, hL1, hN, _⟩ := native_loop_monodromy (complementPath γ) hD
    (fun t => sub_ne_zero.mpr (Ne.symm (hn t)))
    (by change 1 - γ 0 = b; rw [hb, complement_base])
    (by change 1 - γ 1 = b; rw [hb1, complement_base])
  refine ⟨L, k, hL0, hc, hL1, by rw [hL0]; exact initial_y, ?_⟩
  have he := hN.comp_tendsto
    (show Tendsto (fun r : ℂ => 1 - r) (𝓝 b) (𝓝 b) by
      simpa only [complement_base] using
        ((by fun_prop : Continuous (fun r : ℂ => 1 - r)).continuousAt (x := b)).tendsto)
  filter_upwards [he] with r hr
  dsimp [Function.comp_def] at hr
  dsimp [complementY]
  rw [hr]
  simp only [sub_sub_cancel]
  linear_combination -(period r) * Complex.I_sq

end D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
