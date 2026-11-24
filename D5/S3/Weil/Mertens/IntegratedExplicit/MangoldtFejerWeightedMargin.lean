/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerWeightedMargin
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The weighted triangular transform has a uniform positive margin. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerActualOrdinates
import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootQuarterPhaseIncrement
import D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum
import Batteries.Tactic.OpenPrivate

/-! The weighted deficit cannot concentrate near the zeros of the triangular
cosine transform. The resulting positive margin strengthens the Mangoldt gap. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Real MeasureTheory
open scoped BigOperators Interval Topology ComplexConjugate
open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.IntegratedExplicit
open ActualKernelLocalPositivity (K K_continuous)
open MangoldtFejerOptimality (cosineTransform)
open MangoldtFejerGap (rh_iff_eventually_fejer_gap)
open RHSharpActualEnvelope (G coeff_real coeff_norm_hasSum)
open PrimePower.SublinearOrder (tsum_occurrences_eq_twice_positive)
open private phaseDeficit positiveExp negativeExp negativeExp_pos negativeExp_mul_positiveExp
  residualConstant abs_G_sub_K_le from
  D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap
open private actual_series defect_series shift scale shift_small shift_log curvature from
  D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerGap
open private uniform_pairs loss from
  D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap
open private scaled_count_asymptotic from
  D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerActualOrdinates
open private triangularLaw integral_triangularLaw triangularLaw_probability
  triangularLaw_cosineTransform from
  D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerOptimality

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerWeightedMargin

private def triangularKernel (t : ℝ) : ℝ := sinc (t / 4) ^ 2

private lemma kernel_nonneg (t : ℝ) : 0 ≤ triangularKernel t := sq_nonneg _

private lemma kernel_le_one (t : ℝ) : triangularKernel t ≤ 1 := by
  have h := abs_sinc_le_one (t / 4)
  simpa [triangularKernel, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

private lemma shift_one (y : ℝ) : shift 1 y = y * negativeExp y := by simp [shift]

private lemma scale_eq (y : ℝ) : scale y = y * shift 1 y := by rw [scale, shift_one]; ring

private lemma scale_pos {y : ℝ} (hy : 0 < y) : 0 < scale y := by
  rw [scale_eq, shift_one]
  exact mul_pos hy (mul_pos hy (negativeExp_pos _))

private def cutoff (y : ℝ) : ℝ := (shift 1 y)⁻¹

private lemma cutoff_tendsto : Tendsto cutoff atTop atTop := by
  exact tendsto_inv_nhdsGT_zero.comp (shift_small (a := 1) one_pos)

private lemma log_cutoff_div : Tendsto (fun y => log (cutoff y) / y) atTop (𝓝 (1 / 2)) := by
  simpa [cutoff, log_inv] using shift_log (a := 1) one_pos

private lemma tendsto_log_div : Tendsto (fun y : ℝ => log y / y) atTop (𝓝 0) := by
  simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero)

private lemma deficit_lower (rh : RiemannHypothesis) :
    ∀ᶠ y : ℝ in atTop, scale y / 64 ≤ phaseDeficit y := by
  obtain ⟨C, _, hC⟩ := MangoldtUniformFejerGap.rh_iff_eventually_uniform_fejer_gap.mp rh
  have hsmall : Tendsto (fun y : ℝ => log y / y / 12 + C / y + residualConstant / y ^ 2)
      atTop (𝓝 0) := by
    have hi : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv, inv_pow] using
      ((tendsto_log_div.div_const 12).add (hi.const_mul C)).add
        ((hi.pow 2).const_mul residualConstant)
  filter_upwards [tendsto_exp_atTop.eventually hC, eventually_gt_atTop (0 : ℝ),
    hsmall.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 48 - 1 / 64)] with y hy hy0 hs
  rw [log_exp, ← exp_half] at hy
  have hw := negativeExp_mul_positiveExp y
  change negativeExp y * exp (y / 2) = 1 at hw
  have hg := mul_le_mul_of_nonneg_left hy (negativeExp_pos y).le
  have hG : G y ≤ firstLiMass - negativeExp y * (y ^ 2 / 48 - y * log y / 12 - C * y) := by
    change negativeExp y * U (exp y) ≤ _
    linarith only [hg, congrArg (fun t : ℝ => firstLiMass * t) hw]
  have habs := abs_G_sub_K_le hy0
  have hK : K y ≤ G y + negativeExp y * residualConstant := by
    linarith only [neg_abs_le (G y - K y), habs]
  have hcomp := mul_le_mul_of_nonneg_right hs.le (sq_nonneg y)
  have halg : (log y / y / 12 + C / y + residualConstant / y ^ 2) * y^2 =
      y * log y / 12 + C * y + residualConstant := by
    field_simp [hy0.ne']
  rw [halg] at hcomp
  have hcomp' := mul_le_mul_of_nonneg_left hcomp (negativeExp_pos y).le
  unfold phaseDeficit scale
  linarith only [hcomp', hK, hG]

private def ordinateWeight (y t : ℝ) : ℝ := (1 - cos (t * y)) / (1 / 4 + t^2)

private def positiveWeight (S : Spectrum) (y : ℝ) (j : S.index) : ℝ :=
  2 * (S.mult j : ℝ) * ordinateWeight y (S.gamma j)

private lemma positiveWeight_nonneg (S : Spectrum) (y : ℝ) (j : S.index) :
    0 ≤ positiveWeight S y j := by
  unfold positiveWeight ordinateWeight
  positivity [cos_le_one (S.gamma j * y)]

private lemma positiveWeight_le (S : Spectrum) (y : ℝ) (j : S.index) :
    positiveWeight S y j ≤ 4 * ((S.mult j : ℝ) / (S.gamma j) ^ 2) := by
  have hgamma := S.gamma_pos j
  have hc : 1 - cos (S.gamma j * y) ≤ 2 := by linarith [neg_one_le_cos (S.gamma j * y)]
  unfold positiveWeight ordinateWeight
  calc
    _ ≤ 2 * (S.mult j : ℝ) * (2 / (1 / 4 + S.gamma j ^ 2)) := by
      gcongr
    _ ≤ 2 * (S.mult j : ℝ) * (2 / (S.gamma j) ^ 2) := by
      gcongr
      linarith
    _ = _ := by ring

private lemma summable_positiveWeight (rh : RiemannHypothesis) (y : ℝ) :
    Summable (positiveWeight (zetaSpectrum rh) y) := by
  let S := zetaSpectrum rh
  obtain ⟨_, _, hC⟩ := inverse_square_tail S (zetaSpectrum_countAsymptotic rh)
  have h4 (j : S.index) : 4 < S.gamma j := by
    change (4 : ℝ) < j.val.im
    have h := actual_height_gt_ten j.val j.property.1
    rw [abs_of_pos j.property.2] at h
    exact (by norm_num : (4 : ℝ) < 10).trans h
  let e : {j : S.index // 4 < S.gamma j} ≃ S.index :=
    ⟨Subtype.val, fun j => ⟨j, h4 j⟩, fun _ => rfl, fun _ => rfl⟩
  let f (j : S.index) := (4 : ℝ) * ((S.mult j : ℝ) / (S.gamma j) ^ 2)
  have hf : Summable (f ∘ e) := (hC 4 le_rfl).1.mul_left 4
  exact (e.summable_iff.mp hf).of_nonneg_of_le
    (positiveWeight_nonneg S y) (positiveWeight_le S y)

private lemma occurrence_weight (rh : RiemannHypothesis) (y : ℝ) (k : ℕ) :
    ‖actualCoeff k‖ * (1 - cos ((actualZero k).im * y)) =
      ordinateWeight y (actualZero k).im := by
  rw [coeff_real rh k, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (by positivity))]
  simp [ordinateWeight, div_eq_mul_inv, mul_comm]

private lemma deficit_hasSum (rh : RiemannHypothesis) (y : ℝ) :
    HasSum (fun k : ℕ => ‖actualCoeff k‖ * (1 - cos ((actualZero k).im * y))) (phaseDeficit y) := by
  simpa only [phaseDeficit, Pi.sub_apply, mul_sub, mul_one] using
    (coeff_norm_hasSum rh).sub (actual_series rh y)

private lemma sum_positiveWeight (rh : RiemannHypothesis) (y : ℝ) :
    (∑' j, positiveWeight (zetaSpectrum rh) y j) = phaseDeficit y := by
  have hw := deficit_hasSum rh y
  simp_rw [occurrence_weight rh y] at hw
  have h := tsum_occurrences_eq_twice_positive (fun z => ordinateWeight y z.im)
    (fun z => by simp [ordinateWeight, Complex.conj_im]) hw.summable
  rw [hw.tsum_eq] at h
  rw [h, ← tsum_mul_left]
  apply tsum_congr
  intro j
  unfold positiveWeight
  change 2 * (Zeta23.zeroMult j.val : ℝ) * ordinateWeight y j.val.im =
    2 * ((Zeta23.zeroMult j.val : ℝ) * ordinateWeight y j.val.im)
  ring

private def massOn (S : Spectrum) (y : ℝ) (A : Set ℝ) (j : S.index) : ℝ :=
  Set.indicator {j | shift 1 y * S.gamma j ∈ A} (positiveWeight S y) j

private lemma massOn_of_mem {S : Spectrum} {y : ℝ} {A : Set ℝ} {j : S.index}
    (h : shift 1 y * S.gamma j ∈ A) : massOn S y A j = positiveWeight S y j :=
  Set.indicator_of_mem (show j ∈ {i | shift 1 y * S.gamma i ∈ A} from h) _

private lemma massOn_of_notMem {S : Spectrum} {y : ℝ} {A : Set ℝ} {j : S.index}
    (h : shift 1 y * S.gamma j ∉ A) : massOn S y A j = 0 :=
  Set.indicator_of_notMem (show j ∉ {i | shift 1 y * S.gamma i ∈ A} from h) _

private lemma massOn_nonneg (S : Spectrum) (y : ℝ) (A : Set ℝ) (j : S.index) :
    0 ≤ massOn S y A j := by
  classical
  unfold massOn
  exact indicator_nonneg (fun j _ => positiveWeight_nonneg S y j) j

private lemma massOn_le (S : Spectrum) (y : ℝ) (A : Set ℝ) (j : S.index) :
    massOn S y A j ≤ positiveWeight S y j := by
  classical
  unfold massOn
  exact indicator_le_self' (fun j _ => positiveWeight_nonneg S y j) j

private lemma summable_massOn (rh : RiemannHypothesis) (y : ℝ) (A : Set ℝ) :
    Summable (massOn (zetaSpectrum rh) y A) :=
  (summable_positiveWeight rh y).of_nonneg_of_le
    (massOn_nonneg _ _ _) (massOn_le _ _ _)

private lemma scaled_tail {C R : ℝ} (hR : 0 < R) :
    Tendsto (fun y => 4 * C / R * (log (R * cutoff y) / y)) atTop (𝓝 (2 * C / R)) := by
  have hconst : Tendsto (fun y : ℝ => log R / y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (log R)
  have h := (hconst.add log_cutoff_div).const_mul (4 * C / R)
  rw [zero_add, show 4 * C / R * (1 / 2) = 2 * C / R by ring] at h
  apply h.congr'
  filter_upwards [cutoff_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with y hy
  simp only [log_mul hR.ne' hy.ne', add_div]

private lemma eventually_small_tail (rh : RiemannHypothesis) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ y : ℝ in atTop,
      (∑' j, massOn (zetaSpectrum rh) y (Ioi R) j) ≤ scale y / 192 := by
  let S := zetaSpectrum rh
  obtain ⟨C, hC, htail⟩ := inverse_square_tail S (zetaSpectrum_countAsymptotic rh)
  let R : ℝ := 384 * C + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hlim : 2 * C / R < 1 / 192 := by
    apply (div_lt_iff₀ hR).mpr
    dsimp [R]
    linarith
  refine ⟨R, hR, ?_⟩
  have hcut : Tendsto (fun y => R * cutoff y) atTop atTop := cutoff_tendsto.const_mul_atTop hR
  filter_upwards [hcut.eventually (eventually_ge_atTop (4 : ℝ)),
    (scaled_tail (C := C) hR).eventually_lt_const hlim, eventually_gt_atTop (0 : ℝ)]
    with y hy4 hyb hy
  have hs : 0 < shift 1 y := by rw [shift_one]; exact mul_pos hy (negativeExp_pos _)
  have hset : {j : S.index | shift 1 y * S.gamma j ∈ Ioi R} =
      {j : S.index | R * cutoff y < S.gamma j} := by
    ext j
    change R < shift 1 y * S.gamma j ↔ R * cutoff y < S.gamma j
    rw [cutoff, ← div_eq_mul_inv, div_lt_iff₀ hs, mul_comm (S.gamma j)]
  have heq : (∑' j, massOn S y (Ioi R) j) =
      ∑' j : {j : S.index // R * cutoff y < S.gamma j}, positiveWeight S y j.val := by
    unfold massOn
    rw [hset]
    exact (tsum_subtype {j : S.index | R * cutoff y < S.gamma j} (positiveWeight S y)).symm
  obtain ⟨hsum, hbound⟩ := htail (R * cutoff y) hy4
  have hratio : 4 * (C * log (R * cutoff y) / (R * cutoff y)) =
      scale y * (4 * C / R * (log (R * cutoff y) / y)) := by
    rw [scale_eq]
    unfold cutoff
    field_simp [hR.ne', hs.ne', hy.ne']
  rw [heq]
  calc
    _ ≤ ∑' j : {j : S.index // R * cutoff y < S.gamma j},
        4 * ((S.mult j.val : ℝ) / (S.gamma j.val)^2) :=
      ((summable_positiveWeight rh y).subtype _).tsum_mono (hsum.mul_left 4)
        (fun j => positiveWeight_le S y j.val)
    _ ≤ 4 * (C * log (R * cutoff y) / (R * cutoff y)) := by
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ ≤ scale y / 192 := by
      rw [hratio]
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hyb.le (scale_pos hy).le

private lemma scaled_band (rh : RiemannHypothesis) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    Tendsto (fun y => (4 / u^2) *
      (((zetaSpectrum rh).N (v * cutoff y) : ℝ) - (zetaSpectrum rh).N (u * cutoff y)) /
        (cutoff y * log (cutoff y)) * (log (cutoff y) / y))
      atTop (𝓝 ((v - u) / (π * u ^ 2))) := by
  have h := (((scaled_count_asymptotic (hu.trans huv)).sub
    (scaled_count_asymptotic hu)).comp cutoff_tendsto).const_mul (4 / u^2)
  have h' := h.mul log_cutoff_div
  rw [show (4 / u^2) * (v / (2 * π) - u / (2 * π)) * (1 / 2) =
      (v - u) / (π * u ^ 2) by ring] at h'
  convert h' using 1
  funext y
  simp only [Function.comp_apply, zetaSpectrum_N, Zeta23.zetaZeroConfig_N]
  ring

private lemma eventually_small_band (rh : RiemannHypothesis) {u v η : ℝ} (hu : 0 < u)
    (huv : u < v) (hη : (v - u) / (π * u ^ 2) < η) :
    ∀ᶠ y : ℝ in atTop,
      (∑' j, massOn (zetaSpectrum rh) y (Ioc u v) j) ≤ η * scale y := by
  classical
  let S := zetaSpectrum rh
  filter_upwards [(scaled_band rh hu huv).eventually_lt_const hη,
    eventually_gt_atTop (0 : ℝ), cutoff_tendsto.eventually (eventually_gt_atTop (1 : ℝ))]
    with y hlim hy hT
  have hs : 0 < shift 1 y := by rw [shift_one]; exact mul_pos hy (negativeExp_pos _)
  have hT0 : 0 < cutoff y := zero_lt_one.trans hT
  have hcut (a : ℝ) (j : S.index) : j ∈ S.cut (a * cutoff y) ↔
      shift 1 y * S.gamma j ≤ a := by
    simp only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [cutoff, ← div_eq_mul_inv, le_div_iff₀ hs, mul_comm (S.gamma j)]
  let band := S.cut (v * cutoff y) \ S.cut (u * cutoff y)
  have hband (j : S.index) : j ∈ band ↔ shift 1 y * S.gamma j ∈ Ioc u v := by
    simp only [band, Finset.mem_sdiff, hcut, not_le, mem_Ioc, and_comm]
  have hnested : S.cut (u * cutoff y) ⊆ S.cut (v * cutoff y) := by
    intro j hj
    exact (hcut v j).mpr (((hcut u j).mp hj).trans huv.le)
  have hcount : (∑ j ∈ band, (S.mult j : ℝ)) =
      (S.N (v * cutoff y) : ℝ) - (S.N (u * cutoff y) : ℝ) := by
    unfold band Spectrum.N
    push_cast
    exact eq_sub_of_add_eq (Finset.sum_sdiff hnested)
  have hmass : (∑' j, massOn S y (Ioc u v) j) = ∑ j ∈ band, positiveWeight S y j := by
    rw [tsum_eq_sum (s := band)]
    · exact Finset.sum_congr rfl (fun j hj => massOn_of_mem ((hband j).mp hj))
    · intro j hj
      exact massOn_of_notMem (fun h => hj ((hband j).mpr h))
  have hpoint (j : S.index) (hj : j ∈ band) :
      positiveWeight S y j ≤ ((4 / u^2) * (shift 1 y) ^ 2) * (S.mult j : ℝ) := by
    have hleft := ((hband j).mp hj).1
    have hn : (u / shift 1 y) ^ 2 ≤ (S.gamma j) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg hu.le hs.le)
        ((div_le_iff₀ hs).mpr (by simpa [mul_comm] using hleft.le)) 2
    refine (positiveWeight_le S y j).trans ?_
    calc
      _ ≤ 4 * ((S.mult j : ℝ) / (u / shift 1 y) ^ 2) := by
        gcongr
      _ = _ := by field_simp [hu.ne', hs.ne']
  have hratio : ((4 / u^2) * (shift 1 y) ^ 2) *
      ((S.N (v * cutoff y) : ℝ) - (S.N (u * cutoff y) : ℝ)) =
      scale y * ((4 / u ^ 2) * ((S.N (v * cutoff y) : ℝ) - (S.N (u * cutoff y) : ℝ)) /
        (cutoff y * log (cutoff y)) * (log (cutoff y) / y)) := by
    rw [scale_eq]
    generalize hlog : log (cutoff y) = L at *
    unfold cutoff
    field_simp [hu.ne', hs.ne', (hlog ▸ (log_pos hT).ne' : L ≠ 0), hy.ne']
  rw [hmass]
  calc
    _ ≤ ∑ j ∈ band, ((4 / u^2) * (shift 1 y) ^ 2) * (S.mult j : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = _ := by rw [← Finset.mul_sum, hcount, hratio]
    _ ≤ η * scale y := by
      rw [mul_comm η]
      exact mul_le_mul_of_nonneg_left hlim.le (scale_pos hy).le

private lemma kernel_pos_off_bands {R ε : ℝ} {N : ℕ} (hε : 0 < ε)
    (hR : R < 4 * π * N) {t : ℝ} (ht : t ∈ Icc 0 R)
    (hoff : ∀ n ∈ Finset.range N, t ∉ Ioo (4 * π * (n + 1) - ε) (4 * π * (n + 1) + ε)) :
    0 < triangularKernel t := by
  rcases ht.1.eq_or_lt with h0 | h0
  · simp [← h0, triangularKernel]
  · by_contra! hnonpos
    have hz : sinc (t / 4) ^ 2 = 0 := le_antisymm hnonpos (kernel_nonneg t)
    have hsin : sin (t / 4) = 0 := by
      rw [sinc_of_ne_zero (by positivity : t / 4 ≠ 0), pow_eq_zero_iff (by decide),
        div_eq_zero_iff] at hz
      exact hz.resolve_right (by positivity)
    obtain ⟨z, hz⟩ := sin_eq_zero_iff.mp hsin
    have hz0 : 0 < (z : ℝ) := pos_of_mul_pos_left (hz ▸ (by positivity : 0 < t / 4)) pi_pos.le
    have hzN : (z : ℝ) < N := by
      apply (mul_lt_mul_iff_of_pos_right pi_pos).mp
      rw [hz]
      linarith only [ht.2, hR]
    have hz0' : 0 < z := by exact_mod_cast hz0
    have hzN' : z < (N : ℤ) := by exact_mod_cast hzN
    let n := z.toNat - 1
    have hn : n < N := by omega
    have hcast : (n : ℝ) + 1 = z := by
      have h_int : (n : ℤ) + 1 = z := by omega
      exact_mod_cast h_int
    apply hoff n (Finset.mem_range.mpr hn)
    rw [hcast]
    constructor <;> linarith only [hz, hε]

private lemma compact_kernel_lower {R ε : ℝ} {N : ℕ} (hR : 0 < R) (hε : 0 < ε)
    (hR' : R < 4 * π * N) (hlo : ∀ n : ℕ, 0 < 4 * π * (n + 1) - ε) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Icc 0 R,
      (∀ n ∈ Finset.range N, t ∉ Ioo (4 * π * (n + 1) - ε) (4 * π * (n + 1) + ε)) →
      m ≤ triangularKernel t := by
  let bad : Set ℝ := ⋃ n ∈ (↑(Finset.range N) : Set ℕ),
    Ioo (4 * π * (n + 1) - ε) (4 * π * (n + 1) + ε)
  let good : Set ℝ := Icc 0 R \ bad
  have hopen : IsOpen bad := isOpen_biUnion fun _ _ => isOpen_Ioo
  have hcompact : IsCompact good := isCompact_Icc.diff hopen
  have hgood (t : ℝ) : t ∈ good ↔ t ∈ Icc 0 R ∧
      ∀ n ∈ Finset.range N, t ∉ Ioo (4 * π * (n + 1) - ε) (4 * π * (n + 1) + ε) := by
    simp only [good, bad, Set.mem_sdiff, mem_iUnion, not_exists, Finset.mem_coe]
  have hzero : 0 ∈ good :=
    (hgood 0).mpr ⟨⟨le_rfl, hR.le⟩, fun n _ hn => (not_lt_of_gt (hlo n)) hn.1⟩
  have hcont : Continuous triangularKernel := (continuous_sinc.comp (by fun_prop)).pow 2
  obtain ⟨t, ht, hmin⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩ hcont.continuousOn
  have ht' := (hgood t).mp ht
  exact ⟨_, kernel_pos_off_bands hε hR' ht'.1 ht'.2,
    fun x hx hoff => hmin ((hgood x).mpr ⟨hx, hoff⟩)⟩

private lemma positive_spectrum_margin (rh : RiemannHypothesis) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ y : ℝ in atTop, δ * scale y ≤
      ∑' j, positiveWeight (zetaSpectrum rh) y j *
        triangularKernel (shift 1 y * (zetaSpectrum rh).gamma j) := by
  classical
  let S := zetaSpectrum rh
  obtain ⟨R, hR, htail⟩ := eventually_small_tail rh
  obtain ⟨N, hN⟩ := exists_nat_gt (R / (4 * π))
  have hRN : R < 4 * π * N := by
    simpa [mul_comm (N : ℝ)] using (div_lt_iff₀ (by positivity : 0 < 4 * π)).mp hN
  let η : ℝ := 1 / (192 * ((N : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  let ε : ℝ := min π (η * (π * (2 * π)^2) / 4)
  have hε : 0 < ε := lt_min pi_pos (by positivity)
  let u (n : ℕ) := 4 * π * (n + 1) - ε
  let v (n : ℕ) := 4 * π * (n + 1) + ε
  have hu (n : ℕ) : 2 * π ≤ u n := by
    dsimp [u]
    nlinarith [min_le_left π (η * (π * (2 * π)^2) / 4),
      mul_nonneg pi_pos.le (Nat.cast_nonneg (α := ℝ) n)]
  have hu0 (n : ℕ) : 0 < u n := (by positivity : 0 < 2 * π).trans_le (hu n)
  have huv (n : ℕ) : u n < v n := by dsimp [u, v]; linarith
  have hlimit (n : ℕ) : (v n - u n) / (π * (u n) ^ 2) < η := by
    have hπ : 0 < π * (2 * π)^2 := by positivity
    have hwidth : v n - u n = 2 * ε := by dsimp [u, v]; ring
    calc
      _ ≤ (2 * ε) / (π * (2 * π)^2) := by
        rw [hwidth]
        gcongr
        exact hu n
      _ ≤ η / 2 := by
        apply (div_le_iff₀ hπ).mpr
        dsimp [ε]
        linarith only [min_le_right π (η * (π * (2 * π)^2) / 4)]
      _ < η := by linarith
  obtain ⟨m, hm, hmin⟩ := compact_kernel_lower hR hε hRN hu0
  refine ⟨m / 192, by positivity, ?_⟩
  have hbands := (eventually_all_finset (Finset.range N)).mpr
    (fun n _ => eventually_small_band rh (hu0 n) (huv n) (hlimit n))
  filter_upwards [htail, hbands, deficit_lower rh, eventually_gt_atTop (0 : ℝ)]
    with y htail hbands hdef hy
  let w := positiveWeight S y
  let κ (j : S.index) := triangularKernel (shift 1 y * S.gamma j)
  let tail := massOn S y (Ioi R)
  let bands (n : ℕ) := massOn S y (Ioc (u n) (v n))
  have hw : Summable w := summable_positiveWeight rh y
  have hwκ : Summable (fun j => w j * κ j) :=
    hw.of_nonneg_of_le (fun j => mul_nonneg (positiveWeight_nonneg S y j) (kernel_nonneg _))
      (fun j => mul_le_of_le_one_right (positiveWeight_nonneg S y j) (kernel_le_one _))
  have ht : Summable tail := summable_massOn rh y _
  have hb (n : ℕ) : Summable (bands n) := summable_massOn rh y _
  have hb' : Summable (fun j => ∑ n ∈ Finset.range N, bands n j) :=
    summable_sum (s := Finset.range N) (fun n _ => hb n)
  have hpoint (j : S.index) : m * w j ≤ w j * κ j +
      m * (tail j + ∑ n ∈ Finset.range N, bands n j) := by
    have hw0 := positiveWeight_nonneg S y j
    have hk0 := kernel_nonneg (shift 1 y * S.gamma j)
    have htail0 : 0 ≤ tail j := massOn_nonneg S y _ j
    have hbands0 : 0 ≤ ∑ n ∈ Finset.range N, bands n j :=
      Finset.sum_nonneg (fun _ _ => massOn_nonneg S y _ j)
    by_cases hRj : R < shift 1 y * S.gamma j
    · have htj : tail j = w j := massOn_of_mem (A := Ioi R) hRj
      rw [htj]
      nlinarith only [mul_nonneg hw0 hk0, mul_nonneg hm.le hbands0]
    by_cases hbad : ∃ n ∈ Finset.range N, shift 1 y * S.gamma j ∈ Ioo (u n) (v n)
    · obtain ⟨n, hn, hnj⟩ := hbad
      have hbjn : bands n j = w j :=
        massOn_of_mem (A := Ioc (u n) (v n)) ⟨hnj.1, hnj.2.le⟩
      have hle : w j ≤ ∑ i ∈ Finset.range N, bands i j := by
        rw [← hbjn]
        exact Finset.single_le_sum (f := fun i => bands i j)
          (fun i _ => massOn_nonneg S y _ j) hn
      have hle' := mul_le_mul_of_nonneg_left (hle.trans (le_add_of_nonneg_left htail0)) hm.le
      exact hle'.trans (le_add_of_nonneg_left (mul_nonneg hw0 hk0))
    · have hlo : 0 ≤ shift 1 y * S.gamma j := by
        rw [shift_one]
        exact mul_nonneg (mul_nonneg hy.le (negativeExp_pos _).le) (S.gamma_pos j).le
      have hoff (n : ℕ) (hn : n ∈ Finset.range N) :
          shift 1 y * S.gamma j ∉ Ioo (u n) (v n) := fun h => hbad ⟨n, hn, h⟩
      have hκ := hmin _ ⟨hlo, le_of_not_gt hRj⟩ hoff
      exact (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hκ hw0 :
        m * w j ≤ w j * κ j).trans
          (le_add_of_nonneg_right (mul_nonneg hm.le (add_nonneg htail0 hbands0)))
  have hsum := (hw.mul_left m).tsum_mono (hwκ.add ((ht.add hb').mul_left m)) hpoint
  rw [tsum_mul_left, hwκ.tsum_add ((ht.add hb').mul_left m), tsum_mul_left,
    ht.tsum_add hb', Summable.tsum_finsetSum (fun n _ => hb n), sum_positiveWeight rh y] at hsum
  have htotal : (∑ n ∈ Finset.range N, ∑' j, bands n j) ≤ scale y / 192 := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, η * scale y := Finset.sum_le_sum hbands
      _ = (N : ℝ) * η * scale y := by simp [mul_assoc]
      _ ≤ _ := by
        rw [div_eq_mul_inv, mul_comm (scale y)]
        apply mul_le_mul_of_nonneg_right _ (scale_pos hy).le
        dsimp [η]
        have hden : 0 < 192 * ((N : ℝ) + 1) := by positivity
        rw [mul_one_div]
        apply (div_le_iff₀ hden).mpr
        ring_nf
        linarith
  have hbad := mul_le_mul_of_nonneg_left (add_le_add htail htotal) hm.le
  have hgood := mul_le_mul_of_nonneg_left hdef hm.le
  linarith only [hsum, hbad, hgood]

/-- The actual occurrence-weighted triangular transform is eventually bounded
below by a fixed positive multiple of the logarithmic scale. -/
theorem eventually_positive_triangular_margin (rh : RiemannHypothesis) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ y : ℝ in atTop, δ * (negativeExp y * y ^ 2) ≤
      ∑' k : ℕ, ‖actualCoeff k‖ * (1 - cos ((actualZero k).im * y)) *
        sinc ((y * negativeExp y) * (actualZero k).im / 4) ^ 2 := by
  obtain ⟨δ, hδ, h⟩ := positive_spectrum_margin rh
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [h] with y hy
  let f (t : ℝ) := triangularKernel (shift 1 y * t)
  have hw := (deficit_hasSum rh y).summable
  have hf : Summable (fun k : ℕ => ordinateWeight y (actualZero k).im * f (actualZero k).im) := by
    simp_rw [← occurrence_weight rh y]
    refine hw.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    · exact mul_nonneg
        (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr (cos_le_one _))) (kernel_nonneg _)
    · exact mul_le_of_le_one_right
        (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr (cos_le_one _))) (kernel_le_one _)
  have hfconj (z : ℂ) : ordinateWeight y (conj z).im * f (conj z).im =
      ordinateWeight y z.im * f z.im := by
    simp only [Complex.conj_im, ordinateWeight, f, triangularKernel, neg_mul, cos_neg,
      neg_sq, mul_neg, neg_div, sinc_neg]
  have htransfer := tsum_occurrences_eq_twice_positive
    (fun z => ordinateWeight y z.im * f z.im) hfconj hf
  have heq : (∑' k : ℕ, ordinateWeight y (actualZero k).im * f (actualZero k).im) =
      ∑' j, positiveWeight (zetaSpectrum rh) y j *
        triangularKernel (shift 1 y * (zetaSpectrum rh).gamma j) := by
    rw [htransfer, ← tsum_mul_left]
    apply tsum_congr
    intro j
    unfold positiveWeight f
    change 2 * ((Zeta23.zeroMult j.val : ℝ) *
        (ordinateWeight y j.val.im * triangularKernel (shift 1 y * j.val.im))) =
      2 * (Zeta23.zeroMult j.val : ℝ) * ordinateWeight y j.val.im *
        triangularKernel (shift 1 y * j.val.im)
    ring
  rw [← heq] at hy
  simpa only [← occurrence_weight rh y, scale, f, triangularKernel, shift_one] using hy


local instance : IsProbabilityMeasure triangularLaw := triangularLaw_probability

private lemma triangular_cosine_sinc (t : ℝ) :
    cosineTransform triangularLaw t = sinc (t / 4) ^ 2 := by
  by_cases ht : t = 0
  · subst t
    simp [cosineTransform]
  have ht4 : t / 4 ≠ 0 := div_ne_zero ht (by norm_num)
  rw [triangularLaw_cosineTransform ht, sinc_of_ne_zero ht4,
    show t / 2 = 2 * (t / 4) by ring, cos_two_mul_eq_one_sub]
  field_simp [ht]
  ring

private lemma triangular_mem :
    ∀ᵐ b ∂triangularLaw, b ∈ Icc (0 : ℝ) (1 / 2) :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

private lemma triangular_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f triangularLaw := by
  have hc : IsCompact (Icc (0 : ℝ) (1 / 2)) := isCompact_Icc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hf.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [triangular_mem] with b hb using hC b hb

private lemma triangular_first_moment : (∫ b, b ∂triangularLaw) = 1 / 6 := by
  rw [integral_triangularLaw]
  have hderiv (b : ℝ) :
      HasDerivAt (fun x : ℝ => 2 * x ^ 2 - (8 / 3) * x ^ 3) ((4 - 8 * b) * b) b := by
    convert (((hasDerivAt_id b).pow 2).const_mul 2).sub
      (((hasDerivAt_id b).pow 3).const_mul (8 / 3)) using 1
    · funext x
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · norm_num
      ring
  have hc : Continuous (fun b : ℝ => (4 - 8 * b) * b) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun b _ => hderiv b)
    (hc.intervalIntegrable _ _)]
  norm_num

private lemma triangular_gap_moment : (∫ b, (b / 2 - b ^ 2) ∂triangularLaw) = 1 / 24 := by
  have hcos (n : ℕ) (_ : 0 < n) : 0 ≤ cosineTransform triangularLaw (4 * π * n) := by
    rw [triangular_cosine_sinc]
    positivity
  apply (MangoldtFejerOptimality.integral_gap_le_and_eq_iff triangularLaw triangular_mem hcos).2.mpr
  intro n hn
  rw [triangularLaw_cosineTransform (by positivity),
    show 4 * π * (n : ℝ) / 2 = n * (2 * π) by ring, cos_nat_mul_two_pi]
  simp

private def triangularWeightedTerm (y : ℝ) (k : ℕ) : ℝ :=
  ‖actualCoeff k‖ * (1 - cos ((actualZero k).im * y)) *
    sinc (shift 1 y * (actualZero k).im / 4) ^ 2

private lemma integral_triangular_defect (rh : RiemannHypothesis) (y : ℝ) :
    (∫ b, (2 * phaseDeficit (shift b y) - curvature y (shift b y)) ∂triangularLaw) =
      2 * phaseDeficit y - 2 * (∑' k, triangularWeightedTerm y k) := by
  let A (k : ℕ) := 2 * ‖actualCoeff k‖ * (1 - cos ((actualZero k).im * y))
  let T (k : ℕ) := shift 1 y * (actualZero k).im
  let F (k : ℕ) (b : ℝ) := A k * (1 - cos (T k * b))
  have hA : HasSum A (2 * phaseDeficit y) := by
    simpa only [A, mul_assoc] using (deficit_hasSum rh y).mul_left 2
  have hA₀ (k : ℕ) : 0 ≤ A k :=
    mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (sub_nonneg.mpr (cos_le_one _))
  have hnorm (k : ℕ) (b : ℝ) : ‖F k b‖ ≤ 2 * A k := by
    change ‖A k * (1 - cos (T k * b))‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (hA₀ k) (sub_nonneg.mpr (cos_le_one _)))]
    rw [mul_comm 2 (A k)]
    exact mul_le_mul_of_nonneg_left (by linarith [neg_one_le_cos (T k * b)]) (hA₀ k)
  have hF (k : ℕ) : Integrable (F k) triangularLaw :=
    triangular_integrable (by dsimp only [F]; fun_prop)
  have hmajor : Summable (fun k => ∫ b, ‖F k b‖ ∂triangularLaw) := by
    apply (hA.mul_left 2).summable.of_nonneg_of_le
    · exact fun k => integral_nonneg (fun b => norm_nonneg (F k b))
    · intro k
      simpa using integral_mono_ae (hF k).norm (integrable_const (2 * A k))
        (.of_forall (hnorm k))
  have hterm (k : ℕ) :
      (∫ b, F k b ∂triangularLaw) = A k - 2 * triangularWeightedTerm y k := by
    have hcos : Integrable (fun b : ℝ => cos (T k * b)) triangularLaw :=
      triangular_integrable (by fun_prop)
    unfold F
    rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hcos]
    change A k * ((∫ _ : ℝ, (1 : ℝ) ∂triangularLaw) -
      cosineTransform triangularLaw (T k)) = _
    rw [triangular_cosine_sinc]
    simp only [integral_const, probReal_univ, one_smul, A, T, triangularWeightedTerm]
    ring
  have hshift (k : ℕ) (b : ℝ) : T k * b = (actualZero k).im * shift b y := by
    dsimp only [T, shift]
    ring
  have hpoint (b : ℝ) : (∑' k, F k b) =
      2 * phaseDeficit (shift b y) - curvature y (shift b y) := by
    simpa only [F, A, hshift] using (defect_series rh y (shift b y)).tsum_eq
  have hs := hA.sub (hasSum_integral_of_summable_integral_norm hF hmajor)
  change HasSum (fun k => A k - (∫ b, F k b ∂triangularLaw)) _ at hs
  simp_rw [hterm, sub_sub_cancel] at hs
  have heq : (∫ b, (∑' k, F k b) ∂triangularLaw) =
      ∫ b, (2 * phaseDeficit (shift b y) - curvature y (shift b y)) ∂triangularLaw :=
    integral_congr_ae (.of_forall hpoint)
  rw [heq] at hs
  have hsum := hs.tsum_eq
  rw [tsum_mul_left] at hsum
  linarith only [hsum]

private lemma average_uniform_pairs (rh : RiemannHypothesis) (y : ℝ)
    (h : ∀ b ∈ Icc (0 : ℝ) (1 / 2),
      negativeExp y * ((b / 2 - b ^ 2) * y ^ 2 - b * y * log y -
        loss * b * y - 12 * residualConstant) ≤
      (2 * phaseDeficit (shift b y) - curvature y (shift b y)) - 2 * (G y - K y)) :
    negativeExp y * (y ^ 2 / 24 - y * log y / 6 - loss * y / 6 -
      12 * residualConstant) ≤
      2 * (firstLiMass - G y) - 2 * (∑' k, triangularWeightedTerm y k) := by
  let L (b : ℝ) := negativeExp y *
    ((b / 2 - b ^ 2) * y ^ 2 - b * (y * log y) - b * (loss * y) -
      12 * residualConstant)
  let D (b : ℝ) := 2 * phaseDeficit (shift b y) - curvature y (shift b y)
  have hp : Integrable (fun b : ℝ => (b / 2 - b ^ 2) * y ^ 2) triangularLaw :=
    triangular_integrable (by fun_prop)
  have hb (a : ℝ) : Integrable (fun b : ℝ => b * a) triangularLaw :=
    triangular_integrable (by fun_prop)
  have hL : (∫ b, L b ∂triangularLaw) =
      negativeExp y * (y ^ 2 / 24 - y * log y / 6 - loss * y / 6 -
        12 * residualConstant) := by
    dsimp only [L]
    have h₁ : Integrable (fun b : ℝ => (b / 2 - b ^ 2) * y ^ 2 - b * (y * log y))
        triangularLaw := hp.sub (hb (y * log y))
    have h₂ : Integrable (fun b : ℝ => (b / 2 - b ^ 2) * y ^ 2 - b * (y * log y) -
        b * (loss * y)) triangularLaw := h₁.sub (hb (loss * y))
    rw [integral_const_mul, integral_sub h₂ (integrable_const _),
      integral_sub h₁ (hb (loss * y)), integral_sub hp (hb (y * log y))]
    simp only [integral_mul_const, triangular_gap_moment,
      triangular_first_moment, integral_const, probReal_univ, one_smul]
    ring
  have hiD : Integrable D triangularLaw := by
    have ht : Continuous (fun b : ℝ => shift b y) := by unfold shift; fun_prop
    have hd : Continuous (fun b : ℝ => phaseDeficit (shift b y)) :=
      continuous_const.sub (K_continuous.comp ht)
    have hc : Continuous (fun b : ℝ => curvature y (shift b y)) :=
      (continuous_const.sub (K_continuous.comp (continuous_const.add ht))).sub
        (K_continuous.comp (continuous_const.sub ht))
    exact triangular_integrable ((hd.const_mul 2).sub hc)
  have hae : L ≤ᵐ[triangularLaw] (fun b => D b - 2 * (G y - K y)) := by
    filter_upwards [triangular_mem] with b hb
    dsimp only [L, D]
    linarith only [h b hb]
  have hiL : Integrable L triangularLaw :=
    triangular_integrable (by dsimp only [L]; fun_prop)
  have havg := integral_mono_ae hiL (hiD.sub (integrable_const _)) hae
  have hD : (∫ b, D b ∂triangularLaw) =
      2 * phaseDeficit y - 2 * (∑' k, triangularWeightedTerm y k) :=
    integral_triangular_defect rh y
  rw [hL, integral_sub' hiD (integrable_const _), hD] at havg
  simp only [integral_const, probReal_univ, one_smul, phaseDeficit] at havg
  linarith only [havg]

/-- RH is equivalent to a Mangoldt upper envelope whose squared-logarithm
coefficient is strictly greater than 1 / 48. -/
theorem rh_iff_eventually_weighted_fejer_gap :
    RiemannHypothesis ↔ ∃ c : ℝ, 1 / 48 < c ∧ ∀ᶠ x : ℝ in atTop,
      U x ≤ firstLiMass * sqrt x - c * (log x) ^ 2 := by
  constructor
  · intro rh
    obtain ⟨δ, hδ, hmargin⟩ := eventually_positive_triangular_margin rh
    refine ⟨1 / 48 + δ / 2, by linarith, ?_⟩
    have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hsmall : Tendsto (fun y : ℝ =>
        log y / y / 6 + (loss / 6) * y⁻¹ + (12 * residualConstant) * (y⁻¹) ^ 2)
        atTop (𝓝 0) := by
      simpa using ((tendsto_log_div.div_const 6).add (hinv.const_mul (loss / 6))).add
        ((hinv.pow 2).const_mul (12 * residualConstant))
    have herr : ∀ᶠ y : ℝ in atTop,
        y * log y / 6 + loss * y / 6 + 12 * residualConstant ≤ δ * y ^ 2 := by
      filter_upwards [hsmall.eventually_le_const hδ, eventually_gt_atTop (0 : ℝ)]
        with y hy hy₀
      have heq : (log y / y / 6 + (loss / 6) * y⁻¹ +
          (12 * residualConstant) * (y⁻¹) ^ 2) * y ^ 2 =
          y * log y / 6 + loss * y / 6 + 12 * residualConstant := by
        field_simp [hy₀.ne']
      rw [← heq]
      exact mul_le_mul_of_nonneg_right hy (sq_nonneg y)
    have hgap : ∀ᶠ y : ℝ in atTop,
        (1 / 48 + δ / 2) * scale y ≤ firstLiMass - G y := by
      filter_upwards [uniform_pairs rh, hmargin, herr] with y hp hm he
      have ha := average_uniform_pairs rh y hp
      have he' := mul_le_mul_of_nonneg_left he (negativeExp_pos y).le
      have hm' : δ * (negativeExp y * y ^ 2) ≤ ∑' k, triangularWeightedTerm y k := by
        simpa only [triangularWeightedTerm, shift_one] using hm
      change (1 / 48 + δ / 2) * (negativeExp y * y ^ 2) ≤ _
      linarith only [ha, hm', he']
    filter_upwards [tendsto_log_atTop.eventually hgap, eventually_gt_atTop (1 : ℝ)]
      with x hx hx₁
    have hx₀ := zero_lt_one.trans hx₁
    have hw : negativeExp (log x) * sqrt x = 1 := by
      simpa [positiveExp, exp_half, exp_log hx₀] using negativeExp_mul_positiveExp (log x)
    rw [G, exp_log hx₀] at hx
    change (1 / 48 + δ / 2) * (negativeExp (log x) * (log x) ^ 2) ≤
      firstLiMass - negativeExp (log x) * U x at hx
    apply le_of_mul_le_mul_left (a := negativeExp (log x)) _ (negativeExp_pos _)
    linarith only [hx, congrArg (fun t : ℝ => firstLiMass * t) hw]
  · rintro ⟨c, hc, h⟩
    apply rh_iff_eventually_fejer_gap.mpr
    intro d hd
    filter_upwards [h] with x hx
    have hdc := mul_le_mul_of_nonneg_right (show d ≤ c by linarith) (sq_nonneg (log x))
    linarith only [hx, hdc]


#print axioms eventually_positive_triangular_margin
#print axioms rh_iff_eventually_weighted_fejer_gap

end D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerWeightedMargin
