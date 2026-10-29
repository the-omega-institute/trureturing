/- GID: D5/S3/Weil/ZetaGamma/FormCore/L2LogarithmicUncertainty
   generality: I
   mirror-B: none(waiver:source-capacity-repair)
   mirror-E: none(waiver:source-capacity-repair)
   anchors: []
   utility: none
   digest: Actual L2 Fourier concentration bridge; downstream Reg intake and endpoint obligations remain open. -/
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate FourierTransform ENNReal
namespace D5.S3.Weil.ZetaGamma.FormCore.L2LogarithmicUncertainty
abbrev LineL2 := Lp ℂ 2 (volume : Measure ℝ)
abbrev RealL2 := Lp ℝ 2 (volume : Measure ℝ)
def cyclesBand (R : ℝ) : Set ℝ := Ioo (-R) R
def sourceEnergy (u : LineL2) : ℝ := ∫ x : ℝ, ‖u x‖ ^ 2
def firstPositionMoment (u : LineL2) : ℝ :=
  ∫ x : ℝ in Ioi 0, x * ‖u x‖ ^ 2
def bandMemLp (f : LineL2) (R : ℝ) :
    MemLp ((cyclesBand R).indicator (f : ℝ → ℂ)) 2 volume :=
  (Lp.memLp f).indicator measurableSet_Ioo.nullMeasurableSet
def bandPiece (f : LineL2) (R : ℝ) : LineL2 :=
  (bandMemLp f R).toLp ((cyclesBand R).indicator (f : ℝ → ℂ))
def bandNorm (f : LineL2) (R : ℝ) : ℝ := ‖bandPiece f R‖
private lemma sourceEnergy_integrable (u : LineL2) :
    Integrable (fun x : ℝ => ‖u x‖ ^ 2) volume := by
  exact (Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)
private lemma compact_memLp_one (u : LineL2) {r : ℝ} (hr : 0 ≤ r) :
    MemLp ((Icc (0 : ℝ) r).indicator (u : ℝ → ℂ)) 1 volume := by
  have h2 : MemLp ((Icc (0 : ℝ) r).indicator (u : ℝ → ℂ)) 2 volume :=
    (Lp.memLp u).indicator measurableSet_Icc.nullMeasurableSet
  apply h2.mono_exponent_of_measure_support_ne_top
      (s := Icc (0 : ℝ) r) (hpq := by norm_num)
  · intro x hx
    simp [Set.indicator, hx]
  · simp [Real.volume_Icc, hr]
private lemma compact_memLp_two (u : LineL2) {r : ℝ} (hr : 0 ≤ r) :
    MemLp ((Icc (0 : ℝ) r).indicator (u : ℝ → ℂ)) 2 volume :=
  (Lp.memLp u).indicator measurableSet_Icc.nullMeasurableSet
private def compactPiece (u : LineL2) {r : ℝ} (hr : 0 ≤ r) : LineL2 :=
  (compact_memLp_two u hr).toLp ((Icc (0 : ℝ) r).indicator (u : ℝ → ℂ))
/-- The compact piece has the raw Fourier L∞ bound obtained from L2 Hölder.
The full source is never required to be L1. -/
theorem compact_fourier_Linf_bound (u : LineL2) {r : ℝ} (hr : 0 < r) :
    ∀ w : ℝ,
      ‖𝓕 ((Icc (0 : ℝ) r).indicator (u : ℝ → ℂ)) w‖ ≤
        Real.sqrt r * Real.sqrt (sourceEnergy u) := by
  let v : ℝ → ℂ := (Icc (0 : ℝ) r).indicator (u : ℝ → ℂ)
  have hv2 : MemLp v 2 volume :=
    (Lp.memLp u).indicator measurableSet_Icc.nullMeasurableSet
  have hv1 : MemLp v 1 volume := compact_memLp_one u hr.le
  have hconst : MemLp ((Icc (0 : ℝ) r).indicator (fun _ : ℝ => (1 : ℂ)))
      2 volume := by
    exact memLp_indicator_const 2 measurableSet_Icc.nullMeasurableSet
      (1 : ℂ) (Or.inr (by simp [Real.volume_Icc, hr.le]))
  have hsource : Integrable (fun x : ℝ => ‖u x‖ ^ 2) volume :=
    sourceEnergy_integrable u
  have hvnorm : Integrable (fun x : ℝ => ‖v x‖ ^ 2) volume :=
    hv2.integrable_norm_pow (p := 2) (by norm_num)
  have hfirst : (∫ x : ℝ, ‖v x‖ ^ 2) ≤ sourceEnergy u := by
    apply integral_mono_ae hvnorm hsource
    filter_upwards with x
    by_cases hx : x ∈ Icc (0 : ℝ) r
    · simp only [v, Set.indicator_of_mem hx]
      exact le_rfl
    · simp [v, hx]
  have hsecond :
      (∫ x : ℝ, ‖(Icc (0 : ℝ) r).indicator (fun _ : ℝ => (1 : ℂ)) x‖ ^ (2 : ℝ)) = r := by
    have hcongr :
        (fun x : ℝ => ‖(Icc (0 : ℝ) r).indicator (fun _ : ℝ => (1 : ℂ)) x‖ ^ (2 : ℝ)) =
          (Icc (0 : ℝ) r).indicator (fun _ : ℝ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ Icc (0 : ℝ) r <;> simp [hx]
    rw [hcongr, integral_indicator_const (1 : ℝ) measurableSet_Icc]
    simp [Real.volume_Icc, hr.le]
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := (2 : ℝ)) (q := (2 : ℝ))
      (by norm_num [Real.holderConjugate_iff] : Real.HolderConjugate 2 2)
    (show MemLp v (ENNReal.ofReal 2) volume by simpa using hv2)
    (show MemLp ((Icc (0 : ℝ) r).indicator (fun _ : ℝ => (1 : ℂ)))
        (ENNReal.ofReal 2) volume by simpa using hconst)
  intro w
  have hfirst' : (∫ x : ℝ, ‖v x‖ ^ (2 : ℝ)) ≤ sourceEnergy u := by
    simpa [Real.rpow_two] using hfirst
  have hS : 0 ≤ sourceEnergy u := integral_nonneg fun _ => sq_nonneg _
  have hprod :
      (fun x : ℝ => ‖v x‖ *
        ‖(Icc (0 : ℝ) r).indicator (fun _ : ℝ => (1 : ℂ)) x‖) =
        (fun x : ℝ => ‖v x‖) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) r <;> simp [v, hx]
  calc
    ‖𝓕 v w‖ ≤ ∫ x : ℝ, ‖v x‖ := Real.norm_fourier_le_integral_norm v w
    _ = ∫ x : ℝ, ‖v x‖ *
        ‖(Icc (0 : ℝ) r).indicator (fun _ : ℝ => (1 : ℂ)) x‖ := by rw [hprod]
    _ ≤ (∫ x : ℝ, ‖v x‖ ^ (2 : ℝ)) ^ (1 / 2) *
        (∫ x : ℝ, ‖(Icc (0 : ℝ) r).indicator (fun _ : ℝ => (1 : ℂ)) x‖ ^
          (2 : ℝ)) ^ (1 / 2) := hholder
    _ ≤ Real.sqrt (sourceEnergy u) * Real.sqrt r := by
      rw [hsecond]
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      exact mul_le_mul
        (Real.rpow_le_rpow (by positivity) hfirst' (by norm_num)) le_rfl
        (by positivity) (Real.rpow_nonneg hS _)
    _ = Real.sqrt r * Real.sqrt (sourceEnergy u) := by ring
theorem source_energy_nonnegative (u : LineL2) : 0 ≤ sourceEnergy u := by
  exact integral_nonneg fun _ => sq_nonneg _
theorem first_position_moment_nonnegative (u : LineL2)
    (hSupport : ∀ᵐ x : ℝ ∂volume, x < 0 → u x = 0) :
    0 ≤ firstPositionMoment u := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  exact mul_nonneg (le_of_lt (mem_Ioi.mp hx)) (sq_nonneg _)
private lemma band_norm_le_of_ae_norm_le (f g : LineL2) {R A : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A)
    (hpoint : ∀ᵐ w : ℝ ∂volume,
      w ∈ cyclesBand R → ‖f w‖ ≤ A + ‖g w‖) :
    bandNorm f R ≤ A * Real.sqrt (2 * R) + bandNorm g R := by
  let s : Set ℝ := cyclesBand R
  have hs : MeasurableSet s := measurableSet_Ioo
  have hs_top : volume s ≠ ∞ := by
    simp [s, cyclesBand, Real.volume_Ioo, hR.le]
  have hf : MemLp (s.indicator (f : ℝ → ℂ)) 2 volume :=
    bandMemLp f R
  have hg : MemLp (s.indicator (g : ℝ → ℂ)) 2 volume :=
    bandMemLp g R
  have hA_mem : MemLp (s.indicator (fun _ : ℝ => (A : ℝ))) 2 volume :=
    memLp_indicator_const 2 hs.nullMeasurableSet A (Or.inr hs_top)
  have hgn_mem : MemLp (s.indicator (fun x : ℝ => ‖g x‖)) 2 volume :=
    by simpa only [norm_indicator_eq_indicator_norm] using hg.norm
  have hsum_mem := hA_mem.add hgn_mem
  let bound : RealL2 := hsum_mem.toLp
    (s.indicator (fun x : ℝ => A) + s.indicator (fun x : ℝ => ‖g x‖))
  have hbound_eq :
      s.indicator (fun x : ℝ => A) + s.indicator (fun x : ℝ => ‖g x‖) =
        s.indicator (fun x : ℝ => A + ‖g x‖) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx, add_comm]
  have hbound_coe :
      bound =ᵐ[volume] s.indicator (fun x : ℝ => A + ‖g x‖) := by
    simpa [bound, hbound_eq] using hsum_mem.coeFn_toLp
  have hf_coe : (bandPiece f R : ℝ → ℂ) =ᵐ[volume]
      s.indicator (f : ℝ → ℂ) := (bandMemLp f R).coeFn_toLp
  have hpoint' : ∀ᵐ w : ℝ ∂volume,
      ‖bandPiece f R w‖ ≤ ‖bound w‖ := by
    filter_upwards [hf_coe, hbound_coe, hpoint] with w hwf hwb hw
    rw [hwf, hwb]
    by_cases hws : w ∈ s
    · simp only [Set.indicator_of_mem hws]
      simpa [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hA (norm_nonneg _))] using hw hws
    · simp [hws]
  have hnorm : bandNorm f R ≤ ‖bound‖ :=
    Lp.norm_le_norm_of_ae_le hpoint'
  have hA_norm :
      ‖hA_mem.toLp (s.indicator (fun _ : ℝ => (A : ℝ)))‖ =
        A * Real.sqrt (2 * R) := by
    change ‖indicatorConstLp (μ := volume) 2 hs hs_top A‖ = _
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    have htwo : R + R = 2 * R := by ring
    simp [s, cyclesBand, Real.volume_Ioo, hR.le, Real.sqrt_eq_rpow,
      abs_of_nonneg hA, htwo]
  have hgn_norm :
      ‖hgn_mem.toLp (s.indicator (fun x : ℝ => ‖g x‖))‖ = bandNorm g R := by
    change ‖hgn_mem.toLp (s.indicator (fun x : ℝ => ‖g x‖))‖ =
      ‖(bandMemLp g R).toLp ((cyclesBand R).indicator (g : ℝ → ℂ))‖
    rw [Lp.norm_toLp, Lp.norm_toLp]
    simpa only [norm_indicator_eq_indicator_norm, s] using congrArg ENNReal.toReal
      (eLpNorm_norm _ hg.aestronglyMeasurable)
  calc
    bandNorm f R ≤ ‖bound‖ := hnorm
    _ = ‖hA_mem.toLp (s.indicator (fun _ : ℝ => (A : ℝ))) +
        hgn_mem.toLp (s.indicator (fun x : ℝ => ‖g x‖))‖ := by
      change ‖hsum_mem.toLp
        (s.indicator (fun x : ℝ => A) + s.indicator (fun x : ℝ => ‖g x‖))‖ = _
      rw [MemLp.toLp_add]
    _ ≤ ‖hA_mem.toLp (s.indicator (fun _ : ℝ => (A : ℝ)))‖ +
        ‖hgn_mem.toLp (s.indicator (fun x : ℝ => ‖g x‖))‖ := norm_add_le _ _
    _ = A * Real.sqrt (2 * R) + bandNorm g R := by rw [hA_norm, hgn_norm]
/- The first-moment tail payment is proved before any Fourier statement.  This
   is the exact place where the support half-line and the factor `1 / r` enter.
   The theorem is an ordinary set-integral estimate and does not assume that
   the full source is integrable in L1. -/
theorem tail_position_energy_le (u : LineL2) {r : ℝ} (hr : 0 < r)
    (hMoment : Integrable (fun x : ℝ => x * ‖u x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ)))) :
    (∫ x : ℝ in Ioi r, ‖u x‖ ^ 2) ≤ firstPositionMoment u / r := by
  have hU : Integrable (fun x : ℝ => ‖u x‖ ^ 2)
      (volume.restrict (Ioi r)) :=
    (sourceEnergy_integrable u).integrableOn
  have hM_r : Integrable (fun x : ℝ => x * ‖u x‖ ^ 2)
      (volume.restrict (Ioi r)) := by
    apply hMoment.mono_measure
    exact Measure.restrict_mono_set volume (show Ioi r ⊆ Ioi (0 : ℝ) from
      fun x hx => lt_trans hr hx)
  have hscaled : Integrable (fun x : ℝ => (1 / r) * (x * ‖u x‖ ^ 2))
      (volume.restrict (Ioi r)) := hM_r.const_mul _
  have hpoint : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi r)),
      ‖u x‖ ^ 2 ≤ (1 / r) * (x * ‖u x‖ ^ 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx' : r ≤ x := le_of_lt (mem_Ioi.mp hx)
    have hn : 0 ≤ ‖u x‖ ^ 2 := sq_nonneg _
    calc
      ‖u x‖ ^ 2 ≤ (x * ‖u x‖ ^ 2) / r := by
        apply (le_div_iff₀ hr).2
        nlinarith [mul_nonneg (sub_nonneg.mpr hx') hn]
      _ = (1 / r) * (x * ‖u x‖ ^ 2) := by ring
  have hlocal : (∫ x : ℝ in Ioi r, ‖u x‖ ^ 2) ≤
      ∫ x : ℝ in Ioi r, (1 / r) * (x * ‖u x‖ ^ 2) :=
    integral_mono_ae hU hscaled hpoint
  calc
    (∫ x : ℝ in Ioi r, ‖u x‖ ^ 2) ≤
        ∫ x : ℝ in Ioi r, (1 / r) * (x * ‖u x‖ ^ 2) := hlocal
    _ = (1 / r) * (∫ x : ℝ in Ioi r, x * ‖u x‖ ^ 2) := by
      rw [integral_const_mul]
    _ ≤ (1 / r) * firstPositionMoment u := by
      gcongr
      apply integral_mono_measure
        (μ := volume.restrict (Ioi r))
        (ν := volume.restrict (Ioi (0 : ℝ)))
      · exact Measure.restrict_mono_set volume (show Ioi r ⊆ Ioi (0 : ℝ) from
          fun x hx => lt_trans hr hx)
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
        exact mul_nonneg (le_of_lt (mem_Ioi.mp hx)) (sq_nonneg _)
      · exact hMoment
    _ = firstPositionMoment u / r := by ring
theorem compact_remainder_norm_le (u : LineL2) {r : ℝ} (hr : 0 < r)
    (hSupport : ∀ᵐ x : ℝ ∂volume, x < 0 → u x = 0)
    (hMoment : Integrable (fun x : ℝ => x * ‖u x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ)))) :
    ‖u - compactPiece u hr.le‖ ≤
      Real.sqrt (firstPositionMoment u / r) := by
  let tail : LineL2 := u - compactPiece u hr.le
  have htail_ae : (tail : ℝ → ℂ) =ᵐ[volume]
      (Ioi r).indicator (u : ℝ → ℂ) := by
    have hu : ∀ᵐ x : ℝ ∂volume, x < 0 → u x = 0 := hSupport
    have hc : (compactPiece u hr.le : ℝ → ℂ) =ᵐ[volume]
        (Icc (0 : ℝ) r).indicator (u : ℝ → ℂ) := by
      exact (compact_memLp_two u hr.le).coeFn_toLp
    filter_upwards [hu, hc, Lp.coeFn_sub u (compactPiece u hr.le)] with x hxneg hxc htail
    by_cases hx0 : x < 0
    · have hux : u x = 0 := hxneg hx0
      rw [htail]
      simp only [Pi.sub_apply]
      rw [hux]
      have hnot : ¬ x ∈ Ioi r := by
        exact not_lt_of_ge (le_trans (le_of_lt hx0) hr.le)
      have hnotmem : x ∉ Icc (0 : ℝ) r := by
        exact fun hx => (not_lt_of_ge hx.1) hx0
      rw [hxc]
      simp [hnot, hnotmem]
    by_cases hxr : x ≤ r
    · have hxc' : (compactPiece u hr.le : ℝ → ℂ) x = u x := by
        rw [hxc]
        simp [le_of_not_gt hx0, hxr]
      rw [htail]
      simp only [Pi.sub_apply]
      rw [hxc']
      simp [hxr]
    · have hxc' : (compactPiece u hr.le : ℝ → ℂ) x = 0 := by
        rw [hxc]
        have hnotmem : x ∉ Icc (0 : ℝ) r := by
          exact fun hx => hxr hx.2
        simp [hnotmem]
      rw [htail]
      simp only [Pi.sub_apply]
      rw [hxc']
      have hri : r < x := lt_of_not_ge hxr
      simp [hri]
  have htail_norm_eq :
      ‖tail‖ = Real.sqrt (∫ x : ℝ, ‖tail x‖ ^ 2) := by
    rw [Lp.norm_def]
    change lpNorm (tail : ℝ → ℂ) 2 volume = _
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (f := (tail : ℝ → ℂ))
      (μ := volume)
      (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
      ((Lp.memLp tail).aestronglyMeasurable)]
    norm_num [Real.sqrt_eq_rpow, Real.rpow_two]
  have htail_int_eq :
      (∫ x : ℝ, ‖tail x‖ ^ 2) =
        ∫ x : ℝ in Ioi r, ‖u x‖ ^ 2 := by
    calc
      (∫ x : ℝ, ‖tail x‖ ^ 2) =
          ∫ x : ℝ, ‖(Ioi r).indicator (u : ℝ → ℂ) x‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards [htail_ae] with x hx
            rw [hx]
      _ = ∫ x : ℝ in Ioi r, ‖u x‖ ^ 2 := by
        rw [← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Ioi r <;> simp [hx]
  have htail_le :
      (∫ x : ℝ, ‖tail x‖ ^ 2) ≤ firstPositionMoment u / r := by
    rw [htail_int_eq]
    exact tail_position_energy_le u hr hMoment
  change ‖tail‖ ≤ Real.sqrt (firstPositionMoment u / r)
  rw [htail_norm_eq]
  exact Real.sqrt_le_sqrt htail_le
private theorem band_norm_le_norm (f : LineL2) {R : ℝ} (hR : 0 < R) :
    bandNorm f R ≤ ‖f‖ := by
  have hcoe : (bandPiece f R : ℝ → ℂ) =ᵐ[volume]
      (cyclesBand R).indicator (f : ℝ → ℂ) :=
    (bandMemLp f R).coeFn_toLp
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hcoe] with w hw
  rw [hw]
  by_cases hwr : w ∈ cyclesBand R <;> simp [hwr]
private theorem compact_fourier_lp_ae_bound (u : LineL2) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ w : ℝ ∂volume,
      ‖𝓕 (compactPiece u hr.le) w‖ ≤
        Real.sqrt r * Real.sqrt (sourceEnergy u) := by
  let v : ℝ → ℂ := (Icc (0 : ℝ) r).indicator (u : ℝ → ℂ)
  have hv1 : Integrable v := by
    apply memLp_one_iff_integrable.mp
    simpa [v] using (compact_memLp_one u hr.le)
  have hv2 : MemLp v 2 volume := by
    simpa [v] using (compact_memLp_two u hr.le)
  have hraw := LineFourier.raw_fourier_ae_eq_L2 hv1 hv2
  have hraw' : ((𝓕 (compactPiece u hr.le) : LineL2) : ℝ → ℂ) =ᵐ[volume] 𝓕 v := by
    simpa [compactPiece, v] using hraw.symm
  filter_upwards [hraw'] with w hw
  rw [hw]
  exact compact_fourier_Linf_bound u hr w
theorem fourier_band_bound (u : LineL2) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hSupport : ∀ᵐ x : ℝ ∂volume, x < 0 → u x = 0)
    (hMoment : Integrable (fun x : ℝ => x * ‖u x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ)))) :
    bandNorm (𝓕 u : LineL2) R ≤
      (Real.sqrt r * Real.sqrt (sourceEnergy u)) * Real.sqrt (2 * R) +
        Real.sqrt (firstPositionMoment u / r) := by
  let tail : LineL2 := u - compactPiece u hr.le
  have hu : u = compactPiece u hr.le + tail := by
    dsimp [tail]
    abel
  have hFourier : (𝓕 u : LineL2) =
      (𝓕 (compactPiece u hr.le) : LineL2) + (𝓕 tail : LineL2) := by
    calc
      (𝓕 u : LineL2) = 𝓕 (compactPiece u hr.le + tail) := congrArg 𝓕 hu
      _ = (𝓕 (compactPiece u hr.le) : LineL2) + (𝓕 tail : LineL2) := by
        change (Lp.fourierTransformₗᵢ ℝ ℂ) (compactPiece u hr.le + tail) =
          (Lp.fourierTransformₗᵢ ℝ ℂ) (compactPiece u hr.le) +
            (Lp.fourierTransformₗᵢ ℝ ℂ) tail
        exact (Lp.fourierTransformₗᵢ ℝ ℂ).map_add _ _
  have hdecomp : ((𝓕 u : LineL2) : ℝ → ℂ) =ᵐ[volume]
      ((𝓕 (compactPiece u hr.le) : LineL2) : ℝ → ℂ) +
        ((𝓕 tail : LineL2) : ℝ → ℂ) := by
    rw [hFourier]
    exact Lp.coeFn_add _ _
  have hcompact := compact_fourier_lp_ae_bound u hr
  have hA : 0 ≤ Real.sqrt r * Real.sqrt (sourceEnergy u) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpoint : ∀ᵐ w : ℝ ∂volume,
      w ∈ cyclesBand R →
        ‖((𝓕 u : LineL2) : ℝ → ℂ) w‖ ≤
          Real.sqrt r * Real.sqrt (sourceEnergy u) +
            ‖((𝓕 tail : LineL2) : ℝ → ℂ) w‖ := by
    filter_upwards [hdecomp, hcompact] with w hw hc
    intro hwband
    rw [hw]
    calc
      ‖((𝓕 (compactPiece u hr.le) : LineL2) : ℝ → ℂ) w +
          ((𝓕 tail : LineL2) : ℝ → ℂ) w‖ ≤
          ‖((𝓕 (compactPiece u hr.le) : LineL2) : ℝ → ℂ) w‖ +
            ‖((𝓕 tail : LineL2) : ℝ → ℂ) w‖ := norm_add_le _ _
      _ ≤ Real.sqrt r * Real.sqrt (sourceEnergy u) +
          ‖((𝓕 tail : LineL2) : ℝ → ℂ) w‖ := by gcongr
  have htail : bandNorm (𝓕 tail : LineL2) R ≤
      Real.sqrt (firstPositionMoment u / r) := by
    calc
      bandNorm (𝓕 tail : LineL2) R ≤ ‖𝓕 tail‖ := band_norm_le_norm _ hR
      _ = ‖tail‖ := by rw [Lp.norm_fourier_eq]
      _ ≤ Real.sqrt (firstPositionMoment u / r) := by
        exact compact_remainder_norm_le u hr hSupport hMoment
  calc
    bandNorm (𝓕 u : LineL2) R ≤
        (Real.sqrt r * Real.sqrt (sourceEnergy u)) * Real.sqrt (2 * R) +
          bandNorm (𝓕 tail) R :=
      band_norm_le_of_ae_norm_le _ _ hR hA hpoint
    _ ≤ (Real.sqrt r * Real.sqrt (sourceEnergy u)) * Real.sqrt (2 * R) +
        Real.sqrt (firstPositionMoment u / r) := by gcongr
theorem fourier_band_bound_exact (u : LineL2) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hSupport : ∀ᵐ x : ℝ ∂volume, x < 0 → u x = 0)
    (hMoment : Integrable (fun x : ℝ => x * ‖u x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ)))) :
    bandNorm (𝓕 u : LineL2) R ≤
      Real.sqrt (2 * R * r * sourceEnergy u) +
        Real.sqrt (firstPositionMoment u / r) := by
  have hbase := fourier_band_bound u hr hR hSupport hMoment
  have hS : 0 ≤ sourceEnergy u := source_energy_nonnegative u
  have hroot :
      (Real.sqrt r * Real.sqrt (sourceEnergy u)) * Real.sqrt (2 * R) =
        Real.sqrt (2 * R * r * sourceEnergy u) := by
    calc
      (Real.sqrt r * Real.sqrt (sourceEnergy u)) * Real.sqrt (2 * R) =
          Real.sqrt (r * sourceEnergy u) * Real.sqrt (2 * R) := by
            rw [← Real.sqrt_mul hr.le]
      _ = Real.sqrt ((r * sourceEnergy u) * (2 * R)) := by
            rw [Real.sqrt_mul (mul_nonneg hr.le hS)]
      _ = Real.sqrt (2 * R * r * sourceEnergy u) := by
            congr 1 <;> ring
  calc
    bandNorm (𝓕 u : LineL2) R ≤
        (Real.sqrt r * Real.sqrt (sourceEnergy u)) * Real.sqrt (2 * R) +
          Real.sqrt (firstPositionMoment u / r) := hbase
    _ = Real.sqrt (2 * R * r * sourceEnergy u) +
          Real.sqrt (firstPositionMoment u / r) := by rw [hroot]
def bandMass (f : LineL2) (R : ℝ) : ℝ := (bandNorm f R) ^ 2
private lemma sq_add_le_two_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]
private lemma optimized_root_sum_sq {S m R r : ℝ}
    (hS : 0 < S) (hm : 0 < m) (hR : 0 < R)
    (hr : r = Real.sqrt (m / (2 * R * S))) :
    (Real.sqrt (2 * R * r * S) + Real.sqrt (m / r)) ^ 2 ≤
      4 * Real.sqrt (2 * R * m / S) * S := by
  have hrpos : 0 < r := by
    rw [hr]
    positivity
  have hratio : 0 ≤ m / (2 * R * S) := by positivity
  have hr2 : r ^ 2 = m / (2 * R * S) := by
    calc
      r ^ 2 = (Real.sqrt (m / (2 * R * S))) ^ 2 := by rw [hr]
      _ = m / (2 * R * S) := Real.sq_sqrt hratio
  have hfirst : (Real.sqrt (2 * R * r * S)) ^ 2 = 2 * R * r * S := by
    rw [Real.sq_sqrt]
    positivity
  have hsecond : (Real.sqrt (m / r)) ^ 2 = m / r := by
    rw [Real.sq_sqrt]
    positivity
  have hqr : Real.sqrt (2 * R * m / S) * r = m / S := by
    rw [hr]
    calc
      Real.sqrt (2 * R * m / S) * Real.sqrt (m / (2 * R * S)) =
          Real.sqrt ((2 * R * m / S) * (m / (2 * R * S))) := by
            rw [Real.sqrt_mul' _ hratio]
      _ = Real.sqrt ((m / S) ^ 2) := by
            congr 1
            field_simp
      _ = m / S := by
            rw [Real.sqrt_sq (by positivity)]
  have hqrS : Real.sqrt (2 * R * m / S) * r * S = m := by
    rw [hqr]
    field_simp
  have hqrS' : Real.sqrt (R * 2 * m / S) * r * S = m := by
    rw [show R * 2 * m / S = 2 * R * m / S by ring]
    exact hqrS
  have hr2' : 2 * R * S * r ^ 2 = m := by
    rw [hr2]
    field_simp
  calc
    (Real.sqrt (2 * R * r * S) + Real.sqrt (m / r)) ^ 2 ≤
        2 * (Real.sqrt (2 * R * r * S)) ^ 2 +
          2 * (Real.sqrt (m / r)) ^ 2 :=
      sq_add_le_two_sq _ _
    _ = 4 * R * r * S + 2 * m / r := by rw [hfirst, hsecond]; ring
    _ = 4 * Real.sqrt (2 * R * m / S) * S := by
      field_simp [ne_of_gt hrpos]
      nlinarith [hr2', hqrS']
theorem fourier_band_mass_ratio (u : LineL2) {R : ℝ} (hR : 0 < R)
    (hSupport : ∀ᵐ x : ℝ ∂volume, x < 0 → u x = 0)
    (hMoment : Integrable (fun x : ℝ => x * ‖u x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))))
    (hS : 0 < sourceEnergy u)
    (hm : 0 < firstPositionMoment u) :
    bandMass (𝓕 u : LineL2) R / sourceEnergy u ≤
      4 * Real.sqrt (2 * R * firstPositionMoment u / sourceEnergy u) := by
  let r : ℝ := Real.sqrt
    (firstPositionMoment u / (2 * R * sourceEnergy u))
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hbound := fourier_band_bound_exact u hr hR hSupport hMoment
  have hsum : 0 ≤ Real.sqrt (2 * R * r * sourceEnergy u) +
      Real.sqrt (firstPositionMoment u / r) := by positivity
  have hnorm : 0 ≤ bandNorm (𝓕 u : LineL2) R := norm_nonneg _
  have hsq : bandNorm (𝓕 u : LineL2) R ^ 2 ≤
      (Real.sqrt (2 * R * r * sourceEnergy u) +
        Real.sqrt (firstPositionMoment u / r)) ^ 2 := by
    nlinarith
  have hopt := optimized_root_sum_sq
    (S := sourceEnergy u) (m := firstPositionMoment u) (R := R) (r := r)
    hS hm hR (by rfl)
  have hmass : bandMass (𝓕 u : LineL2) R ≤
      4 * Real.sqrt (2 * R * firstPositionMoment u / sourceEnergy u) *
        sourceEnergy u := by
    unfold bandMass
    calc
      bandNorm (𝓕 u : LineL2) R ^ 2 ≤
          (Real.sqrt (2 * R * r * sourceEnergy u) +
            Real.sqrt (firstPositionMoment u / r)) ^ 2 := hsq
      _ ≤ 4 * Real.sqrt (2 * R * firstPositionMoment u / sourceEnergy u) *
          sourceEnergy u := by
        simpa using hopt
  apply (div_le_iff₀ hS).2
  simpa [mul_comm] using hmass
/-- Signed logarithmic integration after the nonnegative layer-cake payment.
The two integrability hypotheses are deliberately explicit: the negative part
must be established by the layer-cake argument, while the positive part is the
actual form-domain supplier on the Gamma source path. -/
theorem signed_log_lower_bound_of_layer_cake
    {f : ℝ → ℂ} {S A : ℝ}
    (hA : 0 < A)
    (hMassInt : Integrable (fun x : ℝ => ‖f x‖ ^ 2) volume)
    (hMass : (∫ x : ℝ, ‖f x‖ ^ 2) = S)
    (hLogInt : Integrable (fun x : ℝ => Real.log |x| * ‖f x‖ ^ 2) volume)
    (hNegInt : Integrable
      (fun x : ℝ => max (Real.log (A / |x|)) 0 * ‖f x‖ ^ 2) volume)
    (hNegBound : (∫ x : ℝ,
      max (Real.log (A / |x|)) 0 * ‖f x‖ ^ 2) ≤ 2 * S) :
    S * (Real.log A - 2) ≤
      ∫ x : ℝ, Real.log |x| * ‖f x‖ ^ 2 := by
  let q : ℝ → ℝ := fun x => ‖f x‖ ^ 2
  let g : ℝ → ℝ := fun x => max (Real.log (A / |x|)) 0 * q x
  let c : ℝ → ℝ := fun x => Real.log A * q x
  have hq_nonneg : ∀ᵐ x : ℝ ∂volume, 0 ≤ q x :=
    Eventually.of_forall (fun x => sq_nonneg _)
  have hq_int : Integrable q volume := by simpa [q] using hMassInt
  have hg_int : Integrable g volume := by simpa [g, q] using hNegInt
  have hc_int : Integrable c volume := by
    simpa [c] using hq_int.const_mul (Real.log A)
  have hsub_int : Integrable (fun x => c x - g x) volume := hc_int.sub hg_int
  have hpoint : ∀ᵐ x : ℝ ∂volume,
      c x - g x ≤ Real.log |x| * q x := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ), hq_nonneg] with x hx0 hqx
    have hxabs : 0 < |x| := abs_pos.mpr hx0
    have hlog : Real.log |x| = Real.log A - Real.log (A / |x|) := by
      rw [Real.log_div (ne_of_gt hA) (ne_of_gt hxabs)]
      ring
    dsimp [c, g, q]
    rw [hlog]
    have hmax : Real.log (A / |x|) ≤ max (Real.log (A / |x|)) 0 :=
      le_max_left _ _
    nlinarith
  have hmono : (∫ x : ℝ, c x - g x) ≤
      ∫ x : ℝ, Real.log |x| * q x :=
    integral_mono_ae hsub_int (by simpa [q] using hLogInt) hpoint
  have hsub_eq : (∫ x : ℝ, c x - g x) =
      Real.log A * S - ∫ x : ℝ, g x := by
    rw [integral_sub hc_int hg_int, integral_const_mul, hMass]
  have hneg : Real.log A * S - 2 * S ≤
      Real.log A * S - ∫ x : ℝ, g x := by
    dsimp [g, q] at hNegBound ⊢
    linarith
  calc
    S * (Real.log A - 2) = Real.log A * S - 2 * S := by ring
    _ ≤ Real.log A * S - ∫ x : ℝ, g x := hneg
    _ = ∫ x : ℝ, c x - g x := hsub_eq.symm
    _ ≤ ∫ x : ℝ, Real.log |x| * q x := hmono
    _ = ∫ x : ℝ, Real.log |x| * ‖f x‖ ^ 2 := by rfl
def angularUnitary (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * f (ξ / (2 * Real.pi))
theorem angular_unitary_mass_preserved {f : ℝ → ℂ}
    (hInt : Integrable (fun x : ℝ => ‖f x‖ ^ 2) volume) :
    (∫ ξ : ℝ, ‖angularUnitary f ξ‖ ^ 2) =
      ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have hπ : 0 < (2 * Real.pi : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 hπ
  have hcongr : (fun ξ : ℝ => ‖angularUnitary f ξ‖ ^ 2) =
      (fun ξ : ℝ => (1 / (2 * Real.pi)) *
        ‖f (ξ / (2 * Real.pi))‖ ^ 2) := by
    funext ξ
    simp only [angularUnitary, norm_mul, norm_inv, Complex.norm_real, abs_of_pos hsqrt]
    have hsqrt_norm : ‖Real.sqrt (2 * Real.pi)‖ = Real.sqrt (2 * Real.pi) :=
      abs_of_pos hsqrt
    rw [hsqrt_norm, mul_pow, inv_pow, Real.sq_sqrt hπ.le]
    ring
  rw [hcongr, integral_const_mul]
  change (1 / (2 * Real.pi)) *
      (∫ ξ : ℝ, ‖f (ξ / (2 * Real.pi))‖ ^ 2) = _
  have hcomp := MeasureTheory.Measure.integral_comp_div
    (fun x : ℝ => ‖f x‖ ^ 2) (2 * Real.pi)
  rw [hcomp]
  rw [abs_of_pos hπ]
  simp only [smul_eq_mul]
  field_simp
private theorem lp_mass_eq_norm_sq (u : LineL2) :
    (∫ x : ℝ, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
  have hnorm : ‖u‖ = Real.sqrt (∫ x : ℝ, ‖u x‖ ^ 2) := by
    rw [Lp.norm_def]
    change lpNorm (u : ℝ → ℂ) 2 volume = _
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (f := (u : ℝ → ℂ))
      (μ := volume)
      (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
      ((Lp.memLp u).aestronglyMeasurable)]
    norm_num [Real.sqrt_eq_rpow, Real.rpow_two]
  rw [hnorm]
  exact (Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)).symm
private theorem source_energy_eq_norm_sq (u : LineL2) :
    sourceEnergy u = ‖u‖ ^ 2 := by
  exact lp_mass_eq_norm_sq u
private theorem bandMass_eq_setIntegral (f : LineL2) {R : ℝ} (hR : 0 < R) :
    bandMass f R = ∫ x : ℝ in cyclesBand R, ‖f x‖ ^ 2 := by
  have hnorm : ‖bandPiece f R‖ ^ 2 = ∫ x : ℝ, ‖bandPiece f R x‖ ^ 2 := by
    rw [lp_mass_eq_norm_sq]
  have hcoe : (bandPiece f R : ℝ → ℂ) =ᵐ[volume]
      (cyclesBand R).indicator (f : ℝ → ℂ) :=
    (bandMemLp f R).coeFn_toLp
  change ‖bandPiece f R‖ ^ 2 = ∫ x : ℝ in cyclesBand R, ‖f x‖ ^ 2
  rw [hnorm]
  calc
    (∫ x : ℝ, ‖bandPiece f R x‖ ^ 2) =
        ∫ x : ℝ, ‖(cyclesBand R).indicator (f : ℝ → ℂ) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx]
    _ = ∫ x : ℝ, (cyclesBand R).indicator (fun x => ‖f x‖ ^ 2) x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ cyclesBand R <;> simp [hx]
    _ = ∫ x : ℝ in cyclesBand R, ‖f x‖ ^ 2 := by
      change (∫ x : ℝ, (Ioo (-R) R).indicator (fun x => ‖f x‖ ^ 2) x) = _
      rw [integral_indicator measurableSet_Ioo]
      rfl
/- The missing negative layer is now proved from the whole band profile.  The
   density measure packages the actual Fourier square mass, so the layer-cake
   tails are the genuine band masses rather than a scalar surrogate. -/
theorem nonnegative_layer_cake_bound
    {f : ℝ → ℂ} {S m A : ℝ}
    (hA : 0 < A) (hS : 0 < S) (hm : 0 < m)
    (hAeq : A = S / (32 * m))
    (hMassInt : Integrable (fun x : ℝ => ‖f x‖ ^ 2) volume)
    (hMass : (∫ x : ℝ, ‖f x‖ ^ 2) = S)
    (hProfile : ∀ {R : ℝ}, 0 < R →
      (∫ x : ℝ in cyclesBand R, ‖f x‖ ^ 2) ≤
        4 * Real.sqrt (2 * R * m / S) * S) :
    Integrable (fun x : ℝ =>
      max (Real.log (A / |x|)) 0 * ‖f x‖ ^ 2) volume ∧
      (∫ x : ℝ, max (Real.log (A / |x|)) 0 * ‖f x‖ ^ 2) ≤ 2 * S := by
  classical
  let q : ℝ → ℝ := fun x => ‖f x‖ ^ 2
  let h : ℝ → ℝ := fun x => max (Real.log (A / |x|)) 0
  let qE : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (q x)
  let μ : Measure ℝ := volume.withDensity qE
  have hq_int : Integrable q volume := by simpa [q] using hMassInt
  have hq_ae : AEMeasurable q volume := hq_int.aestronglyMeasurable.aemeasurable
  have hqE_ae : AEMeasurable qE volume := by
    exact hq_ae.ennreal_ofReal
  have hmeas : Measurable h := by
    dsimp [h]
    fun_prop
  have hmeas_ae : AEMeasurable h μ := hmeas.aemeasurable
  have hnonneg : ∀ᵐ x : ℝ ∂μ, 0 ≤ h x :=
    Eventually.of_forall (fun x => le_max_right _ _)
  have hlayer :
      (∫⁻ x : ℝ, ENNReal.ofReal (h x) ∂μ) =
        ∫⁻ t : ℝ in Ioi 0, μ {x : ℝ | t < h x} :=
    lintegral_eq_lintegral_meas_lt μ hnonneg hmeas_ae
  have hleft :
      (∫⁻ x : ℝ, ENNReal.ofReal (h x * q x)) =
        ∫⁻ x : ℝ, ENNReal.ofReal (h x) ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ hqE_ae hmeas.aemeasurable.ennreal_ofReal]
    apply lintegral_congr_ae
    filter_upwards with x
    dsimp [qE, q]
    calc
      ENNReal.ofReal (h x * ‖f x‖ ^ 2) =
          ENNReal.ofReal (‖f x‖ ^ 2 * h x) := by rw [mul_comm]
      _ = ENNReal.ofReal (‖f x‖ ^ 2) * ENNReal.ofReal (h x) :=
        ENNReal.ofReal_mul (sq_nonneg _)
  have htail_bound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi 0)),
      μ {x : ℝ | t < h x} ≤
        ENNReal.ofReal (4 * Real.sqrt (2 * (A * Real.exp (-t)) * m / S) * S) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    let R : ℝ := A * Real.exp (-t)
    have hR : 0 < R := by dsimp [R]; positivity
    have hset : {x : ℝ | t < h x} =ᵐ[μ] cyclesBand R := by
      filter_upwards [Measure.ae_ne μ (0 : ℝ)] with x hx0
      have hxabs : 0 < |x| := abs_pos.mpr hx0
      apply propext
      constructor
      · intro htx
        have htx' : t < Real.log (A / |x|) := by
          rcases (lt_max_iff.mp htx) with htx' | htx'
          · exact htx'
          · linarith
        have hexp : Real.exp t < A / |x| :=
          (Real.lt_log_iff_exp_lt (div_pos hA hxabs)).mp htx'
        have hmul : Real.exp t * |x| < A :=
          (lt_div_iff₀ hxabs).mp hexp
        have htarget : |x| < A * Real.exp (-t) := by
          have hdiv : |x| < A / Real.exp t := by
            exact (lt_div_iff₀ (Real.exp_pos t)).mpr (by simpa [mul_comm] using hmul)
          simpa [div_eq_mul_inv, ← Real.exp_neg] using hdiv
        simpa [cyclesBand, R, abs_lt] using htarget
      · intro htx
        have htarget : |x| < A * Real.exp (-t) := by
          simpa [cyclesBand, R, abs_lt] using htx
        have hmul : Real.exp t * |x| < A := by
          have hdiv : |x| < A / Real.exp t := by
            simpa [div_eq_mul_inv, ← Real.exp_neg] using htarget
          simpa [mul_comm] using (lt_div_iff₀ (Real.exp_pos t)).mp hdiv
        have hexp : Real.exp t < A / |x| :=
          (lt_div_iff₀ hxabs).mpr (by simpa [mul_comm] using hmul)
        have htx' : t < Real.log (A / |x|) :=
          (Real.lt_log_iff_exp_lt (div_pos hA hxabs)).mpr hexp
        exact (lt_max_iff.mpr (Or.inl htx'))
    have hmeasure : μ {x : ℝ | t < h x} = μ (cyclesBand R) :=
      measure_congr hset
    rw [hmeasure]
    dsimp [μ]
    change (volume.withDensity qE) (Ioo (-R) R) ≤ _
    rw [withDensity_apply qE measurableSet_Ioo]
    dsimp [qE, q]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict (Ioo (-R) R)) hq_int.integrableOn]
    · exact ENNReal.ofReal_le_ofReal (hProfile hR)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact sq_nonneg _
  let C : ℝ := 4 * Real.sqrt (2 * m / S) * S * Real.sqrt A
  have hsqrt_exp (t : ℝ) : Real.sqrt (Real.exp (-t)) = Real.exp (-t / 2) := by
    have he : Real.exp (-t) = (Real.exp (-t / 2)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring
    rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hprofile_exp (t : ℝ) :
      4 * Real.sqrt (2 * (A * Real.exp (-t)) * m / S) * S =
        C * Real.exp (-t / 2) := by
    dsimp [C]
    have h₁ : 0 ≤ 2 * m / S := by positivity
    have h₂ : 0 ≤ A := hA.le
    calc
      4 * Real.sqrt (2 * (A * Real.exp (-t)) * m / S) * S =
          4 * (Real.sqrt (2 * m / S) * Real.sqrt (A * Real.exp (-t))) * S := by
            congr 2
            rw [show 2 * (A * Real.exp (-t)) * m / S =
                (2 * m / S) * (A * Real.exp (-t)) by ring,
              Real.sqrt_mul h₁]
      _ = 4 * Real.sqrt (2 * m / S) * S *
          (Real.sqrt A * Real.exp (-t / 2)) := by
            rw [Real.sqrt_mul h₂, hsqrt_exp]
            ring
      _ = (4 * Real.sqrt (2 * m / S) * S * Real.sqrt A) *
          Real.exp (-t / 2) := by ring
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hexp_int : Integrable (fun t : ℝ => Real.exp ((-1 / 2) * t))
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact integrableOn_exp_mul_Ioi (by norm_num) 0
  have hC_int : Integrable (fun t : ℝ => C * Real.exp ((-1 / 2) * t))
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [smul_eq_mul] using hexp_int.const_mul C
  have hC_nonneg_ae : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi 0)),
      0 ≤ C * Real.exp ((-1 / 2) * t) :=
    Eventually.of_forall (fun t => mul_nonneg hC_nonneg (Real.exp_pos _).le)
  have hC_eval :
      (∫ t : ℝ in Ioi 0, C * Real.exp ((-1 / 2) * t)) = 2 * C := by
    rw [integral_const_mul]
    rw [integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0]
    norm_num [mul_comm]
  have hCA : 2 * C = 2 * S := by
    dsimp [C]
    rw [hAeq]
    have h₁ : 0 ≤ 2 * m / S := by positivity
    have hprod : Real.sqrt (2 * m / S) * Real.sqrt (S / (32 * m)) =
        (1 / 4 : ℝ) := by
      rw [← Real.sqrt_mul h₁]
      have hratio : (2 * m / S) * (S / (32 * m)) = (1 / 4 : ℝ) ^ 2 := by
        field_simp
        ring
      rw [hratio, Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
    rw [show 4 * Real.sqrt (2 * m / S) * S * Real.sqrt (S / (32 * m)) =
        4 * S * (Real.sqrt (2 * m / S) * Real.sqrt (S / (32 * m))) by ring,
      hprod]
    ring
  have houter :
      (∫⁻ t : ℝ in Ioi 0, μ {x : ℝ | t < h x}) ≤ ENNReal.ofReal (2 * S) := by
    calc
      (∫⁻ t : ℝ in Ioi 0, μ {x : ℝ | t < h x}) ≤
          ∫⁻ t : ℝ in Ioi 0,
            ENNReal.ofReal (4 * Real.sqrt (2 * (A * Real.exp (-t)) * m / S) * S) :=
        lintegral_mono_ae htail_bound
      _ = ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal (C * Real.exp ((-1 / 2) * t)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [hprofile_exp, show (-t / 2 : ℝ) = (-1 / 2) * t by ring]
      _ = ENNReal.ofReal (∫ t : ℝ in Ioi 0,
          C * Real.exp ((-1 / 2) * t)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hC_int hC_nonneg_ae]
      _ = ENNReal.ofReal (2 * S) := by rw [hC_eval, hCA]
  have hbound :
      (∫⁻ x : ℝ, ENNReal.ofReal (h x * q x)) ≤ ENNReal.ofReal (2 * S) := by
    rw [hleft, hlayer]
    exact houter
  have hbound_top : (∫⁻ x : ℝ, ENNReal.ofReal (h x * q x)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hg_ae : AEMeasurable (fun x : ℝ => h x * q x) volume :=
    hmeas.aemeasurable.mul hq_ae
  have hg_nonneg : ∀ᵐ x : ℝ ∂volume, 0 ≤ h x * q x := by
    filter_upwards with x
    exact mul_nonneg (le_max_right _ _) (sq_nonneg _)
  have hE_ae : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (h x * q x)) volume := hg_ae.ennreal_ofReal
  have hto_int : Integrable
      (fun x : ℝ => (ENNReal.ofReal (h x * q x)).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hE_ae hbound_top
  have hg_int : Integrable (fun x : ℝ => h x * q x) volume := by
    apply hto_int.congr
    filter_upwards [hg_nonneg] with x hx
    simp [ENNReal.toReal_ofReal hx]
  have hreal :
      ENNReal.ofReal (∫ x : ℝ, h x * q x) =
        ∫⁻ x : ℝ, ENNReal.ofReal (h x * q x) :=
    ofReal_integral_eq_lintegral_ofReal hg_int hg_nonneg
  have htoReal := (ENNReal.toReal_le_toReal hbound_top ENNReal.ofReal_ne_top).mpr hbound
  have hreal_le : (∫ x : ℝ, h x * q x) ≤ 2 * S := by
    calc
      (∫ x : ℝ, h x * q x) =
          (ENNReal.ofReal (∫ x : ℝ, h x * q x)).toReal := by
            rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hg_nonneg)]
      _ = (∫⁻ x : ℝ, ENNReal.ofReal (h x * q x)).toReal := by rw [hreal]
      _ ≤ (ENNReal.ofReal (2 * S)).toReal := htoReal
      _ = 2 * S := ENNReal.toReal_ofReal (by positivity)
  constructor
  · simpa [h, q] using hg_int
  · simpa [h, q] using hreal_le
theorem angular_unitary_fourier_mass_eq_source_energy (u : LineL2) :
    (∫ ξ : ℝ, ‖angularUnitary ((𝓕 u : LineL2) : ℝ → ℂ) ξ‖ ^ 2) = sourceEnergy u := by
  rw [angular_unitary_mass_preserved]
  · rw [lp_mass_eq_norm_sq, Lp.norm_fourier_eq, source_energy_eq_norm_sq]
  · exact sourceEnergy_integrable (𝓕 u : LineL2)
/- The angular statement is the exact consumer normalization.  The two
   hypotheses for the negative logarithmic part are kept explicit until the
   nonnegative layer-cake theorem is completed. -/
theorem angular_log_lower_bound_of_layer_cake
    (u : LineL2) {A : ℝ}
    (hSupport : ∀ᵐ x : ℝ ∂volume, x < 0 → u x = 0)
    (hMoment : Integrable (fun x : ℝ => x * ‖u x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))))
    (hS : 0 < sourceEnergy u)
    (hm : 0 < firstPositionMoment u)
    (hA : A = sourceEnergy u / (32 * firstPositionMoment u))
    (hLogInt : Integrable
      (fun x : ℝ => Real.log |x| * ‖((𝓕 u : LineL2) : ℝ → ℂ) x‖ ^ 2) volume)
    (hNegInt : Integrable
      (fun x : ℝ => max (Real.log (A / |x|)) 0 *
        ‖((𝓕 u : LineL2) : ℝ → ℂ) x‖ ^ 2) volume)
    (hNegBound : (∫ x : ℝ, max (Real.log (A / |x|)) 0 *
      ‖((𝓕 u : LineL2) : ℝ → ℂ) x‖ ^ 2) ≤ 2 * sourceEnergy u) :
    sourceEnergy u * (Real.log (Real.pi * sourceEnergy u /
      (16 * firstPositionMoment u)) - 2) ≤
      ∫ ξ : ℝ, Real.log |ξ| *
        ‖angularUnitary ((𝓕 u : LineL2) : ℝ → ℂ) ξ‖ ^ 2 := by
  have hmA : 0 < A := by
    rw [hA]
    positivity
  have hfourier_mass :
      (∫ x : ℝ, ‖((𝓕 u : LineL2) : ℝ → ℂ) x‖ ^ 2) = sourceEnergy u := by
    rw [lp_mass_eq_norm_sq, Lp.norm_fourier_eq, source_energy_eq_norm_sq]
  have hsigned := signed_log_lower_bound_of_layer_cake
    (f := ((𝓕 u : LineL2) : ℝ → ℂ)) (S := sourceEnergy u) (A := A)
    hmA (sourceEnergy_integrable (𝓕 u : LineL2)) hfourier_mass hLogInt hNegInt hNegBound
  have ha : 0 < (2 * Real.pi : ℝ) := by positivity
  have hq : Integrable
      (fun x : ℝ => ‖((𝓕 u : LineL2) : ℝ → ℂ) x‖ ^ 2) volume :=
    sourceEnergy_integrable (𝓕 u : LineL2)
  let q : ℝ → ℝ := fun x => ‖((𝓕 u : LineL2) : ℝ → ℂ) x‖ ^ 2
  let lq : ℝ → ℝ := fun x => Real.log |x| * q x
  have hqcomp : Integrable (fun ξ : ℝ => q (ξ / (2 * Real.pi))) volume :=
    hq.comp_div (by positivity)
  have hlqcomp : Integrable (fun ξ : ℝ => lq (ξ / (2 * Real.pi))) volume :=
    (by simpa [lq] using hLogInt.comp_div (by positivity))
  have hpoint :
      (fun ξ : ℝ => Real.log |ξ| *
        ‖angularUnitary ((𝓕 u : LineL2) : ℝ → ℂ) ξ‖ ^ 2) =ᵐ[volume]
      (fun ξ : ℝ => (1 / (2 * Real.pi)) *
        ((Real.log (2 * Real.pi) + Real.log |ξ / (2 * Real.pi)|) *
          q (ξ / (2 * Real.pi)))) := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ξ hξ
    have hlog : Real.log |ξ| = Real.log (2 * Real.pi) +
        Real.log |ξ / (2 * Real.pi)| := by
      have habs : (2 * Real.pi) * |ξ / (2 * Real.pi)| = |ξ| := by
        rw [abs_div, abs_of_pos ha]
        field_simp
      calc
        Real.log |ξ| = Real.log ((2 * Real.pi) * |ξ / (2 * Real.pi)|) := by rw [habs]
        _ = Real.log (2 * Real.pi) + Real.log |ξ / (2 * Real.pi)| := by
          exact Real.log_mul (ne_of_gt ha)
            (ne_of_gt (abs_pos.mpr (div_ne_zero hξ (ne_of_gt ha))))
    rw [hlog]
    simp only [angularUnitary, norm_mul, norm_inv, Complex.norm_real]
    have hsqrt_norm : ‖Real.sqrt (2 * Real.pi)‖ = Real.sqrt (2 * Real.pi) :=
      abs_of_pos (Real.sqrt_pos.2 ha)
    rw [hsqrt_norm, mul_pow, inv_pow, Real.sq_sqrt ha.le]
    ring_nf
    rfl
  have hangular :
      (∫ ξ : ℝ, Real.log |ξ| *
        ‖angularUnitary ((𝓕 u : LineL2) : ℝ → ℂ) ξ‖ ^ 2) =
        Real.log (2 * Real.pi) * sourceEnergy u +
          ∫ x : ℝ, Real.log |x| * q x := by
    rw [integral_congr_ae hpoint, integral_const_mul]
    have hcomp_q := MeasureTheory.Measure.integral_comp_div q (2 * Real.pi)
    have hcomp_lq := MeasureTheory.Measure.integral_comp_div lq (2 * Real.pi)
    have hsplit :
        (fun ξ : ℝ => (Real.log (2 * Real.pi) + Real.log |ξ / (2 * Real.pi)|) *
          q (ξ / (2 * Real.pi))) =
        (fun ξ : ℝ => Real.log (2 * Real.pi) * q (ξ / (2 * Real.pi)) +
          lq (ξ / (2 * Real.pi))) := by
      funext ξ
      dsimp [lq]
      ring
    rw [hsplit, integral_add (hqcomp.const_mul _) hlqcomp,
      integral_const_mul, hcomp_q, hcomp_lq]
    simp only [abs_of_pos ha, smul_eq_mul]
    rw [hfourier_mass]
    dsimp [q, lq]
    field_simp [Real.pi_pos.ne']
  rw [hangular]
  rw [hA] at hsigned
  have hlogA : Real.log (sourceEnergy u / (32 * firstPositionMoment u)) =
      Real.log (sourceEnergy u) - Real.log (32 * firstPositionMoment u) := by
    rw [Real.log_div (ne_of_gt hS) (by positivity)]
  rw [hlogA] at hsigned
  have hlogprod : Real.log (Real.pi * sourceEnergy u /
      (16 * firstPositionMoment u)) =
      Real.log (2 * Real.pi) + Real.log (sourceEnergy u) -
        Real.log (32 * firstPositionMoment u) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
      (ne_of_gt hS), Real.log_mul (by positivity) (by positivity)]
    have hlog32 : Real.log (32 : ℝ) = Real.log 2 + Real.log 16 := by
      rw [show (32 : ℝ) = 2 * 16 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have hlog32m : Real.log (32 * firstPositionMoment u) =
        Real.log 32 + Real.log (firstPositionMoment u) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hm)]
    have hlog2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi := by
      rw [Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)]
    rw [hlog32m, hlog32, hlog2pi]
    ring
  rw [hlogprod]
  linarith
/- The actual Fourier consumer discharges the negative layer from the proved
   band profile.  Its only logarithmic input is the positive form-domain
   integrability supplied by the completed Gamma source. -/
theorem angular_log_lower_bound
    (u : LineL2) {A : ℝ}
    (hSupport : ∀ᵐ x : ℝ ∂volume, x < 0 → u x = 0)
    (hMoment : Integrable (fun x : ℝ => x * ‖u x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))))
    (hS : 0 < sourceEnergy u)
    (hm : 0 < firstPositionMoment u)
    (hA : A = sourceEnergy u / (32 * firstPositionMoment u))
    (hLogInt : Integrable
      (fun x : ℝ => Real.log |x| * ‖((𝓕 u : LineL2) : ℝ → ℂ) x‖ ^ 2) volume) :
    sourceEnergy u * (Real.log (Real.pi * sourceEnergy u /
      (16 * firstPositionMoment u)) - 2) ≤
      ∫ ξ : ℝ, Real.log |ξ| *
        ‖angularUnitary ((𝓕 u : LineL2) : ℝ → ℂ) ξ‖ ^ 2 := by
  have hApos : 0 < A := by
    rw [hA]
    positivity
  have hfourier_mass :
      (∫ x : ℝ, ‖((𝓕 u : LineL2) : ℝ → ℂ) x‖ ^ 2) = sourceEnergy u := by
    rw [lp_mass_eq_norm_sq, Lp.norm_fourier_eq, source_energy_eq_norm_sq]
  have hProfile : ∀ {R : ℝ}, 0 < R →
      (∫ x : ℝ in cyclesBand R,
        ‖((𝓕 u : LineL2) : ℝ → ℂ) x‖ ^ 2) ≤
        4 * Real.sqrt (2 * R * firstPositionMoment u / sourceEnergy u) *
          sourceEnergy u := by
    intro R hR
    rw [← bandMass_eq_setIntegral (𝓕 u : LineL2) hR]
    exact (div_le_iff₀ hS).mp
      (fourier_band_mass_ratio u hR hSupport hMoment hS hm)
  have hNeg := nonnegative_layer_cake_bound
    (f := ((𝓕 u : LineL2) : ℝ → ℂ))
    (S := sourceEnergy u) (m := firstPositionMoment u) (A := A)
    hApos hS hm hA (sourceEnergy_integrable (𝓕 u : LineL2)) hfourier_mass
      hProfile
  exact angular_log_lower_bound_of_layer_cake u hSupport hMoment hS hm hA hLogInt
    hNeg.1 hNeg.2
/- The compiled frontier is deliberately explicit.  The actual band estimate,
   optimized mass profile, nonnegative layer-cake bound, source-to-angular
   mass normalization, signed-log comparison, and the angular consumer are
   present.  The consumer keeps the positive logarithmic form-domain premise
   explicit; the completed Gamma source must supply it.  B01/B03/B04/B05/B06
   remain open.  No full-source L1 premise is introduced.
 -/
end D5.S3.Weil.ZetaGamma.FormCore.L2LogarithmicUncertainty
