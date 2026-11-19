/- GID: D5/S3/Quantum/Analysis/MeasurableFirstResponse
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/MeasurableFirstResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp vector response of the original measurable evolution. -/

import D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Taylor

/-! # Sharp first response for vectorwise measurable coefficients -/

open scoped Topology
open MeasureTheory Filter intervalIntegral
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel

namespace D5.S3.Quantum.Analysis.MeasurableFirstResponse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The actual vector Bochner response, using the original measurable evolution. -/
noncomputable def response (S : Contraction E) (B H : ℝ → E →L[ℂ] E)
    (t r : ℝ) (x : E) : E :=
  ∫ s in r..t, measurableEvolution S B t s (H s (measurableEvolution S B s r x))

private theorem native_bound (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s)
    {t r : ℝ} (hp : (t, r) ∈ triangle T) (x : E) :
    ‖measurableEvolution S B t r x‖ ≤ Real.exp (∫ s in r..t, g s) * ‖x‖ := by
  obtain ⟨Phi, hPhi⟩ := measurable_evolution S
  rcases hPhi B T hT hB g hg hgn hBg with
    ⟨_, _, _, hseries, _, _, _, _, _, hb, _⟩
  have heq : Phi B t r x = measurableEvolution S B t r x := by
    rw [measurableEvolution_apply S B (hp.2.1.trans hp.2.2)
      (fun z => (hB z).mono_set (Set.Icc_subset_Icc hp.1 le_rfl)) g
      (hg.mono_set (Set.Icc_subset_Icc hp.1 le_rfl))
      (fun s hs => hgn s ⟨hp.1.trans hs.1, hs.2⟩)
      (fun s hs => hBg s ⟨hp.1.trans hs.1, hs.2⟩) ⟨hp.2.1, hp.2.2⟩ x]
    exact (hseries t r hp x).2.tsum_eq.symm
  rw [← heq]
  exact ((Phi B t r).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hb t r hp) (norm_nonneg x))

private theorem clock_nonneg {r t : ℝ} (hrt : r ≤ t) {h : ℝ → ℝ}
    (hn : ∀ s ∈ Set.Icc r t, 0 ≤ h s) : 0 ≤ ∫ s in r..t, h s :=
  intervalIntegral.integral_nonneg hrt hn

private theorem clock_split {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Icc r t)) :
    (∫ z in r..s, g z) + (∫ z in s..t, g z) = ∫ z in r..t, g z := by
  exact intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hrs).mpr
      (hg.mono_set (Set.Icc_subset_Icc le_rfl hst)))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr
      (hg.mono_set (Set.Icc_subset_Icc hrs le_rfl)))

private theorem exponential_clock {r t : ℝ} (hrt : r ≤ t) {h : ℝ → ℝ}
    (hh : IntegrableOn h (Set.Icc r t)) (hn : ∀ s ∈ Set.Icc r t, 0 ≤ h s) :
    IntervalIntegrable (fun s => h s * Real.exp (∫ z in s..t, h z)) volume r t ∧
    (∫ s in r..t, h s * Real.exp (∫ z in s..t, h z)) =
      Real.exp (∫ s in r..t, h s) - 1 := by
  let A := ∫ s in r..t, h s
  let F : ℝ → ℝ := fun s => ∫ z in r..s, h z
  let K : ℝ → ℝ := fun s => A - F s
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr hh
  have hF : AbsolutelyContinuousOnInterval F r t :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => A) r t :=
    LipschitzOnWith.absolutelyContinuousOnInterval
      (LipschitzWith.const A).lipschitzOnWith
  have hK : AbsolutelyContinuousOnInterval K r t := hconst.sub hF
  have hKe : ∀ s ∈ Set.Icc r t, K s = ∫ z in s..t, h z := by
    intro s hs
    have he := clock_split hs.1 hs.2 hh
    dsimp [K, F, A]
    linarith
  have hKm : Set.MapsTo K (Set.uIcc r t) (Set.Icc 0 A) := by
    intro s hs
    rw [Set.uIcc_of_le hrt] at hs
    refine ⟨?_, ?_⟩
    · rw [hKe s hs]
      exact clock_nonneg hs.2 (fun z hz => hn z ⟨hs.1.trans hz.1, hz.2⟩)
    · have hpos := clock_nonneg hs.1 (fun z hz => hn z ⟨hz.1, hz.2.trans hs.2⟩)
      dsimp [K, F]
      linarith
  obtain ⟨C, hC⟩ := (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ 1 Real.exp
    (Set.Icc 0 A)).exists_lipschitzOnWith (by decide) (convex_Icc 0 A) isCompact_Icc
  have hExp : AbsolutelyContinuousOnInterval (fun s => Real.exp (K s)) r t :=
    hC.comp_absolutelyContinuousOnInterval hKm hK
  have hd : (fun s => deriv (fun u => Real.exp (K u)) s) =ᵐ[
      volume.restrict (Set.uIcc r t)] (fun s => -(h s * Real.exp (K s))) := by
    apply (ae_restrict_iff' measurableSet_uIcc).mpr
    filter_upwards [hi.ae_hasDerivAt_integral] with s hs hmem
    have he := ((hasDerivAt_const s A).sub (hs hmem r (by simp))).exp
    simpa [K, F, mul_comm] using he.deriv
  have hw : IntervalIntegrable (fun s => h s * Real.exp (K s)) volume r t :=
    hi.mul_continuousOn hExp.continuousOn
  have hFTC := hExp.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae_restrict
    (hd.filter_mono (ae_mono (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl))),
    intervalIntegral.integral_neg] at hFTC
  have hval : (∫ s in r..t, h s * Real.exp (K s)) = Real.exp A - 1 := by
    have hKr : K r = A := by simp [K, F]
    have hKt : K t = 0 := by simp [K, F, A]
    rw [hKr, hKt, Real.exp_zero] at hFTC
    linarith
  have heq : ∀ s ∈ Set.uIcc r t,
      h s * Real.exp (K s) = h s * Real.exp (∫ z in s..t, h z) := by
    intro s hs
    rw [hKe s (by simpa [Set.uIcc_of_le hrt] using hs)]
  refine ⟨hw.congr (fun s hs => heq s (Set.uIoc_subset_uIcc hs)), ?_⟩
  rw [← intervalIntegral.integral_congr heq]
  exact hval

private structure Control (Q : ℝ → E →L[ℂ] E) (k : ℝ → ℝ) (T : ℝ) : Prop where
  measurable : ∀ x : E, AEStronglyMeasurable (fun s => Q s x)
    (volume.restrict (Set.Icc 0 T))
  integrable : IntegrableOn k (Set.Icc 0 T)
  nonneg : ∀ s ∈ Set.Icc 0 T, 0 ≤ k s
  bound : ∀ s ∈ Set.Icc 0 T, ‖Q s‖ ≤ k s

omit [CompleteSpace E] in
private theorem control_add {B H : ℝ → E →L[ℂ] E} {g h : ℝ → ℝ} {T : ℝ}
    (cB : Control B g T) (cH : Control H h T) : Control (B+H) (g+h) T where
  measurable x := (cB.measurable x).add (cH.measurable x)
  integrable := cB.integrable.add cH.integrable
  nonneg s hs := add_nonneg (cB.nonneg s hs) (cH.nonneg s hs)
  bound s hs := (norm_add_le _ _).trans (add_le_add (cB.bound s hs) (cH.bound s hs))

private theorem response_regular (S : Contraction E) {B H : ℝ → E →L[ℂ] E}
    {g h : ℝ → ℝ} {T r : ℝ} (hT : 0 ≤ T) (hr : r ∈ Set.Icc 0 T)
    (cB : Control B g T) (cH : Control H h T) (x : E) :
    ContinuousOn (fun t => response S B H t r x) (Set.Icc r T) ∧
    ∀ t ∈ Set.Icc r T, IntervalIntegrable
      (fun s => measurableEvolution S B t s (H s (measurableEvolution S B s r x)))
      volume r t := by
  have hd := native_data S B hT cB.measurable g cB.integrable cB.nonneg cB.bound
  have hv : ContinuousOn (fun s => measurableEvolution S B s r x) (Set.Icc r T) :=
    (hd.1 x).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hr.1, hs.1, hs.2⟩)
  have hf := evaluation_integrable
    (fun z => (cH.measurable z).mono_set (Set.Icc_subset_Icc hr.1 le_rfl))
    (cH.integrable.mono_set (Set.Icc_subset_Icc hr.1 le_rfl))
    (fun s hs => cH.bound s ⟨hr.1.trans hs.1, hs.2⟩) hv
  exact forced_regular S B hT hr cB.measurable g cB.integrable cB.nonneg cB.bound hf

private theorem increment_bound (S : Contraction E) {B H : ℝ → E →L[ℂ] E}
    {g h : ℝ → ℝ} {T t r : ℝ} (hT : 0 ≤ T) (hp : (t, r) ∈ triangle T)
    (cB : Control B g T) (cH : Control H h T) (x : E) :
    ‖measurableEvolution S (B+H) t r x - measurableEvolution S B t r x‖ ≤
      Real.exp (∫ s in r..t, g s) * (Real.exp (∫ s in r..t, h s) - 1) * ‖x‖ := by
  have hd := relative_duhamel S B H hT cB.measurable cH.measurable g h
    cB.integrable cH.integrable cB.nonneg cH.nonneg cB.bound cH.bound
    hp.1 hp.2.1 hp.2.2 x
  have cQ := control_add cB cH
  have hgt := cB.integrable.mono_set (Set.Icc_subset_Icc hp.1 hp.2.2)
  have hht := cH.integrable.mono_set (Set.Icc_subset_Icc hp.1 hp.2.2)
  have hc := exponential_clock hp.2.1 hht
    (fun s hs => cH.nonneg s ⟨hp.1.trans hs.1, hs.2.trans hp.2.2⟩)
  rw [hd.2.2.2]
  calc
    _ ≤ ∫ s in r..t, ‖measurableEvolution S (B+H) t s
        (H s (measurableEvolution S B s r x))‖ :=
      intervalIntegral.norm_integral_le_integral_norm hp.2.1
    _ ≤ ∫ s in r..t, (Real.exp (∫ z in r..t, g z) * ‖x‖) *
        (h s * Real.exp (∫ z in s..t, h z)) := by
      apply intervalIntegral.integral_mono_on hp.2.1 hd.2.1.norm (hc.1.const_mul _)
      intro s hs
      have hsT : s ∈ Set.Icc 0 T := ⟨hp.1.trans hs.1, hs.2.trans hp.2.2⟩
      have hx := native_bound S B hT cB.measurable g cB.integrable cB.nonneg cB.bound
        (t := s) (r := r) ⟨hp.1, hs.1, hsT.2⟩ x
      have hy := native_bound S (B+H) hT cQ.measurable (g+h) cQ.integrable cQ.nonneg cQ.bound
        (t := t) (r := s) ⟨hsT.1, hs.2, hp.2.2⟩ (H s (measurableEvolution S B s r x))
      have he : Real.exp (∫ z in s..t, (g+h) z) * Real.exp (∫ z in r..s, g z) =
          Real.exp (∫ z in r..t, g z) * Real.exp (∫ z in s..t, h z) := by
        have hig := (intervalIntegrable_iff_integrableOn_Icc_of_le hs.2).mpr
          (hgt.mono_set (Set.Icc_subset_Icc hs.1 le_rfl))
        have hih := (intervalIntegrable_iff_integrableOn_Icc_of_le hs.2).mpr
          (hht.mono_set (Set.Icc_subset_Icc hs.1 le_rfl))
        simp only [Pi.add_apply]
        rw [intervalIntegral.integral_add hig hih, ← Real.exp_add, ← Real.exp_add]
        congr 1
        linarith [clock_split hs.1 hs.2 hgt]
      calc
        _ ≤ Real.exp (∫ z in s..t, (g+h) z) * ‖H s (measurableEvolution S B s r x)‖ := hy
        _ ≤ Real.exp (∫ z in s..t, (g+h) z) *
            (h s * (Real.exp (∫ z in r..s, g z) * ‖x‖)) :=
          mul_le_mul_of_nonneg_left
            (((H s).le_opNorm _).trans (mul_le_mul (cH.bound s hsT) hx
              (norm_nonneg _) (cH.nonneg s hsT))) (Real.exp_pos _).le
        _ = (Real.exp (∫ z in s..t, (g+h) z) * Real.exp (∫ z in r..s, g z)) *
            (h s * ‖x‖) := by ring
        _ = _ := by rw [he]; ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, hc.2]; ring

private theorem sharp_second_order_defect (S : Contraction E) {B H : ℝ → E →L[ℂ] E}
    {g h : ℝ → ℝ} {T t r : ℝ} (hT : 0 ≤ T) (hp : (t, r) ∈ triangle T)
    (cB : Control B g T) (cH : Control H h T) (x : E) :
    ‖measurableEvolution S (B+H) t r x - measurableEvolution S B t r x -
      response S B H t r x‖ ≤ Real.exp (∫ s in r..t, g s) *
      (Real.exp (∫ s in r..t, h s) - 1 - ∫ s in r..t, h s) * ‖x‖ := by
  have hd := relative_duhamel S B H hT cB.measurable cH.measurable g h
    cB.integrable cH.integrable cB.nonneg cH.nonneg cB.bound cH.bound
    hp.1 hp.2.1 hp.2.2 x
  have hi := (response_regular S hT ⟨hp.1, hp.2.1.trans hp.2.2⟩ cB cH x).2 t
    ⟨hp.2.1, hp.2.2⟩
  have hgt := cB.integrable.mono_set (Set.Icc_subset_Icc hp.1 hp.2.2)
  have hht := cH.integrable.mono_set (Set.Icc_subset_Icc hp.1 hp.2.2)
  have hhi := (intervalIntegrable_iff_integrableOn_Icc_of_le hp.2.1).mpr hht
  have hc := exponential_clock hp.2.1 hht
    (fun s hs => cH.nonneg s ⟨hp.1.trans hs.1, hs.2.trans hp.2.2⟩)
  have hw : IntervalIntegrable (fun s => h s * (Real.exp (∫ z in s..t, h z) - 1))
      volume r t := by
    convert hc.1.sub hhi using 1
    funext s
    ring
  have hwi : (∫ s in r..t, h s * (Real.exp (∫ z in s..t, h z) - 1)) =
      Real.exp (∫ s in r..t, h s) - 1 - ∫ s in r..t, h s := by
    calc
      _ = ∫ s in r..t, (h s * Real.exp (∫ z in s..t, h z) - h s) := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      _ = _ := by rw [intervalIntegral.integral_sub hc.1 hhi, hc.2]
  rw [hd.2.2.2]
  change ‖(∫ s in r..t, measurableEvolution S (B+H) t s
      (H s (measurableEvolution S B s r x))) -
      ∫ s in r..t, measurableEvolution S B t s
      (H s (measurableEvolution S B s r x))‖ ≤ _
  rw [← intervalIntegral.integral_sub hd.2.1 hi]
  calc
    _ ≤ ∫ s in r..t, ‖measurableEvolution S (B+H) t s
        (H s (measurableEvolution S B s r x)) - measurableEvolution S B t s
        (H s (measurableEvolution S B s r x))‖ :=
      intervalIntegral.norm_integral_le_integral_norm hp.2.1
    _ ≤ ∫ s in r..t, (Real.exp (∫ z in r..t, g z) * ‖x‖) *
        (h s * (Real.exp (∫ z in s..t, h z) - 1)) := by
      apply intervalIntegral.integral_mono_on hp.2.1 (hd.2.1.sub hi).norm (hw.const_mul _)
      intro s hs
      have hsT : s ∈ Set.Icc 0 T := ⟨hp.1.trans hs.1, hs.2.trans hp.2.2⟩
      have hx := native_bound S B hT cB.measurable g cB.integrable cB.nonneg cB.bound
        (t := s) (r := r) ⟨hp.1, hs.1, hsT.2⟩ x
      have hy := increment_bound S hT (t := t) (r := s) ⟨hsT.1, hs.2, hp.2.2⟩
        cB cH (H s (measurableEvolution S B s r x))
      have hh0 : 0 ≤ Real.exp (∫ z in s..t, h z) - 1 := by
        apply sub_nonneg.mpr
        exact Real.one_le_exp_iff.mpr (clock_nonneg hs.2
          (fun z hz => cH.nonneg z ⟨hsT.1.trans hz.1, hz.2.trans hp.2.2⟩))
      have he : Real.exp (∫ z in s..t, g z) * Real.exp (∫ z in r..s, g z) =
          Real.exp (∫ z in r..t, g z) := by
        rw [← Real.exp_add, add_comm, clock_split hs.1 hs.2 hgt]
      calc
        _ ≤ Real.exp (∫ z in s..t, g z) * (Real.exp (∫ z in s..t, h z) - 1) *
            ‖H s (measurableEvolution S B s r x)‖ := hy
        _ ≤ Real.exp (∫ z in s..t, g z) * (Real.exp (∫ z in s..t, h z) - 1) *
            (h s * (Real.exp (∫ z in r..s, g z) * ‖x‖)) :=
          mul_le_mul_of_nonneg_left
            (((H s).le_opNorm _).trans (mul_le_mul (cH.bound s hsT) hx
              (norm_nonneg _) (cH.nonneg s hsT)))
            (mul_nonneg (Real.exp_pos _).le hh0)
        _ = (Real.exp (∫ z in s..t, g z) * Real.exp (∫ z in r..s, g z)) *
            (‖x‖ * (h s * (Real.exp (∫ z in s..t, h z) - 1))) := by ring
        _ = _ := by rw [he]; ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, hwi]; ring

private theorem quadratic_exp_bound {a : ℝ} (ha : 0 ≤ a) :
    Real.exp a - 1 - a ≤ (1 / 2 : ℝ) * Real.exp a * a^2 := by
  by_cases hz : a = 0
  · simp [hz]
  obtain ⟨c, hc, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.exp) (n := 1) (x₀ := 0) (x := a) (Ne.symm hz)
    Real.contDiff_exp.contDiffOn
  have hpoly : taylorWithinEval Real.exp 1 (Set.uIcc 0 a) 0 a = 1 + a := by
    have hd : iteratedDerivWithin 1 Real.exp (Set.uIcc 0 a) 0 = 1 := by
      rw [iteratedDerivWithin_one]
      exact (Real.hasDerivAt_exp 0).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_uIcc (Ne.symm hz)) 0 (by simp)) |>.trans (by simp)
    simp [taylorWithinEval_succ, hd]
  have he' : Real.exp a - 1 - a = Real.exp c * a^2 / 2 := by
    rw [hpoly, iteratedDeriv_eq_iterate, Real.iter_deriv_exp] at he
    norm_num at he
    linarith
  rw [he']
  have hca : c ≤ a := by
    rw [Set.uIoo_of_lt (lt_of_le_of_ne ha (Ne.symm hz))] at hc
    exact hc.2.le
  nlinarith [mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hca) (sq_nonneg a)]

omit [NormedSpace ℂ E] [CompleteSpace E] in
private theorem remainder_comparison {a b : ℝ} (hb : 0 ≤ b) (x : E) :
    Real.exp a * (Real.exp b - 1 - b) * ‖x‖ ≤
      (1 / 2 : ℝ) * Real.exp (a + b) * b^2 * ‖x‖ := by
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (quadratic_exp_bound hb) (Real.exp_pos a).le) (norm_nonneg x)
  rw [Real.exp_add]
  convert he using 1
  ring

omit [CompleteSpace E] in
private theorem control_smul {H : ℝ → E →L[ℂ] E} {h : ℝ → ℝ} {T : ℝ}
    (cH : Control H h T) (ε : ℝ) : Control (ε • H) (fun s => |ε| * h s) T where
  measurable x := by
    convert (cH.measurable x).const_smul ε using 1
  integrable := cH.integrable.const_mul |ε|
  nonneg s hs := mul_nonneg (abs_nonneg ε) (cH.nonneg s hs)
  bound s hs := by
    simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (cH.bound s hs) (abs_nonneg ε)

omit [CompleteSpace E] in
private theorem response_smul (S : Contraction E) (B H : ℝ → E →L[ℂ] E)
    (t r : ℝ) (x : E) (ε : ℝ) : response S B (ε • H) t r x = ε • response S B H t r x := by
  simp only [response, Pi.smul_apply, smul_apply]
  simp_rw [← ContinuousLinearMap.coe_coe, LinearMap.map_smul_of_tower]
  exact intervalIntegral.integral_smul ε _

private theorem clock_le_horizon {T t r : ℝ} (hp : (t, r) ∈ triangle T)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Icc 0 T))
    (hn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s) :
    (∫ s in r..t, g s) ≤ ∫ s in 0..T, g s := by
  apply intervalIntegral.integral_mono_interval hp.1 hp.2.1 hp.2.2 _
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (hp.1.trans (hp.2.1.trans hp.2.2))).mpr hg)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hn s ⟨hs.1.le, hs.2⟩

private theorem quotient_bound (S : Contraction E) {B H : ℝ → E →L[ℂ] E}
    {g h : ℝ → ℝ} {T t r : ℝ} (hT : 0 ≤ T) (hp : (t, r) ∈ triangle T)
    (cB : Control B g T) (cH : Control H h T) (x : E) {ε : ℝ}
    (hε : ε ≠ 0) (hε1 : |ε| ≤ 1) :
    ‖ε⁻¹ • (measurableEvolution S (B + ε • H) t r x - measurableEvolution S B t r x) -
      response S B H t r x‖ ≤ |ε| * ((1 / 2 : ℝ) *
        Real.exp ((∫ s in 0..T, g s) + ∫ s in 0..T, h s) *
        (∫ s in 0..T, h s)^2 * ‖x‖) := by
  let a := ∫ s in r..t, g s
  let b := ∫ s in r..t, h s
  let G := ∫ s in 0..T, g s
  let K := ∫ s in 0..T, h s
  have hb : 0 ≤ b := clock_nonneg hp.2.1
    (fun s hs => cH.nonneg s ⟨hp.1.trans hs.1, hs.2.trans hp.2.2⟩)
  have haG : a ≤ G := clock_le_horizon hp cB.integrable cB.nonneg
  have hbK : b ≤ K := clock_le_horizon hp cH.integrable cH.nonneg
  have hK : 0 ≤ K := hb.trans hbK
  have hε0 : 0 < |ε| := abs_pos.mpr hε
  have hd := sharp_second_order_defect S hT hp cB (control_smul cH ε) x
  simp only [intervalIntegral.integral_const_mul] at hd
  have hq : ‖measurableEvolution S (B + ε • H) t r x - measurableEvolution S B t r x -
      response S B (ε • H) t r x‖ ≤
      (1 / 2 : ℝ) * Real.exp (a + |ε| * b) * (|ε| * b)^2 * ‖x‖ :=
    hd.trans (remainder_comparison (mul_nonneg hε0.le hb) x)
  have hqe : ε⁻¹ • (measurableEvolution S (B + ε • H) t r x -
      measurableEvolution S B t r x) - response S B H t r x =
      ε⁻¹ • (measurableEvolution S (B + ε • H) t r x -
      measurableEvolution S B t r x - response S B (ε • H) t r x) := by
    rw [response_smul]
    simp only [smul_sub, inv_smul_smul₀ hε]
  rw [hqe, norm_smul, Real.norm_eq_abs, abs_inv]
  have hexp : Real.exp (a + |ε| * b) ≤ Real.exp (G + K) := by
    apply Real.exp_le_exp.mpr
    have hab : |ε| * b ≤ K := (mul_le_of_le_one_left hb hε1).trans hbK
    linarith
  have hpow : b^2 ≤ K^2 := pow_le_pow_left₀ hb hbK 2
  calc
    _ ≤ |ε|⁻¹ * ((1 / 2 : ℝ) * Real.exp (a + |ε| * b) * (|ε| * b)^2 * ‖x‖) :=
      mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hε0.le)
    _ = |ε| * ((1 / 2 : ℝ) * Real.exp (a + |ε| * b) * b^2 * ‖x‖) := by
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hε0.le
      gcongr

/-- Actual Bochner response, sharp local tail, and a signed derivative uniform on the triangle. -/
theorem uniform_signed_response (S : Contraction E) (B H : ℝ → E →L[ℂ] E)
    {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (hH : ∀ x : E, AEStronglyMeasurable (fun s => H s x) (volume.restrict (Set.Icc 0 T)))
    (g h : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T)) (hh : IntegrableOn h (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s) (hhn : ∀ s ∈ Set.Icc 0 T, 0 ≤ h s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) (hHh : ∀ s ∈ Set.Icc 0 T, ‖H s‖ ≤ h s) :
    (∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ x : E,
      IntervalIntegrable
        (fun s => measurableEvolution S B t s (H s (measurableEvolution S B s r x))) volume r t ∧
      ‖response S B H t r x‖ ≤ Real.exp (∫ s in r..t, g s) * (∫ s in r..t, h s) * ‖x‖ ∧
      ‖measurableEvolution S (B+H) t r x - measurableEvolution S B t r x -
        response S B H t r x‖ ≤ Real.exp (∫ s in r..t, g s) *
        (Real.exp (∫ s in r..t, h s) - 1 - ∫ s in r..t, h s) * ‖x‖ ∧
      Real.exp (∫ s in r..t, g s) * (Real.exp (∫ s in r..t, h s) - 1 - ∫ s in r..t, h s) * ‖x‖ ≤
        (1 / 2 : ℝ) * Real.exp ((∫ s in r..t, g s) + ∫ s in r..t, h s) *
        (∫ s in r..t, h s)^2 * ‖x‖) ∧
    (∀ (x : E) (η : ℝ), 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < |ε| → |ε| < δ → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T →
      ‖ε⁻¹ • (measurableEvolution S (B + ε • H) t r x - measurableEvolution S B t r x) -
        response S B H t r x‖ < η) := by
  let cB : Control B g T := ⟨hB, hg, hgn, hBg⟩
  let cH : Control H h T := ⟨hH, hh, hhn, hHh⟩
  constructor
  · intro r t hr hrt htT x
    have hp : (t, r) ∈ triangle T := ⟨hr, hrt, htT⟩
    refine ⟨(response_regular S hT ⟨hr, hrt.trans htT⟩ cB cH x).2 t ⟨hrt, htT⟩,
      ?_, sharp_second_order_defect S hT hp cB cH x,
      remainder_comparison (clock_nonneg hrt
        (fun s hs => hhn s ⟨hr.trans hs.1, hs.2.trans htT⟩)) x⟩
    have hi := (response_regular S hT ⟨hp.1, hp.2.1.trans hp.2.2⟩ cB cH x).2 t
      ⟨hp.2.1, hp.2.2⟩
    have hgt := cB.integrable.mono_set (Set.Icc_subset_Icc hp.1 hp.2.2)
    have hht := (intervalIntegrable_iff_integrableOn_Icc_of_le hp.2.1).mpr
      (cH.integrable.mono_set (Set.Icc_subset_Icc hp.1 hp.2.2))
    calc
      _ ≤ ∫ s in r..t, ‖measurableEvolution S B t s
          (H s (measurableEvolution S B s r x))‖ :=
        intervalIntegral.norm_integral_le_integral_norm hp.2.1
      _ ≤ ∫ s in r..t, Real.exp (∫ z in r..t, g z) * (h s * ‖x‖) := by
        apply intervalIntegral.integral_mono_on hp.2.1 hi.norm
          ((hht.mul_const ‖x‖).const_mul _)
        intro s hs
        have hsT : s ∈ Set.Icc 0 T := ⟨hp.1.trans hs.1, hs.2.trans hp.2.2⟩
        have hx := native_bound S B hT cB.measurable g cB.integrable cB.nonneg cB.bound
          (t := s) (r := r) ⟨hp.1, hs.1, hsT.2⟩ x
        have hy := native_bound S B hT cB.measurable g cB.integrable cB.nonneg cB.bound
          (t := t) (r := s) ⟨hsT.1, hs.2, hp.2.2⟩ (H s (measurableEvolution S B s r x))
        have he : Real.exp (∫ z in s..t, g z) * Real.exp (∫ z in r..s, g z) =
            Real.exp (∫ z in r..t, g z) := by
          rw [← Real.exp_add, add_comm, clock_split hs.1 hs.2 hgt]
        calc
          _ ≤ Real.exp (∫ z in s..t, g z) * ‖H s (measurableEvolution S B s r x)‖ := hy
          _ ≤ Real.exp (∫ z in s..t, g z) *
              (h s * (Real.exp (∫ z in r..s, g z) * ‖x‖)) :=
            mul_le_mul_of_nonneg_left
              (((H s).le_opNorm _).trans (mul_le_mul (cH.bound s hsT) hx
                (norm_nonneg _) (cH.nonneg s hsT))) (Real.exp_pos _).le
          _ = (Real.exp (∫ z in s..t, g z) * Real.exp (∫ z in r..s, g z)) *
              (h s * ‖x‖) := by ring
          _ = _ := by rw [he]
      _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]; ring
  · intro x η hη
    let C : ℝ := (1 / 2 : ℝ) * Real.exp ((∫ s in 0..T, g s) + ∫ s in 0..T, h s) *
      (∫ s in 0..T, h s)^2 * ‖x‖
    have hC : 0 ≤ C := by dsimp [C]; positivity
    refine ⟨min 1 (η / (C + 1)), lt_min zero_lt_one (div_pos hη (by linarith)), ?_⟩
    intro ε hε hεδ r t hr hrt htT
    have hε1 : |ε| ≤ 1 := (hεδ.trans_le (min_le_left _ _)).le
    have he : |ε| < η / (C + 1) := hεδ.trans_le (min_le_right _ _)
    have heη : |ε| * (C + 1) < η := (lt_div_iff₀ (by linarith)).mp he
    exact (quotient_bound S hT ⟨hr, hrt, htT⟩ cB cH x (abs_pos.mp hε) hε1).trans_lt
      (by change |ε| * C < η; nlinarith)

end D5.S3.Quantum.Analysis.MeasurableFirstResponse
