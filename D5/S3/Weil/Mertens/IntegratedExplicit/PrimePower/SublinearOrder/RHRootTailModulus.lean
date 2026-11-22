/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootTailModulus
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootTailModulus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp symmetric root-spectrum scale on each logarithmic tail. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootLateIncrement

/-! The full cosine kernel majorizes the symmetric increment at every start. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualZero)
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c R cusp_remainder_bound)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity (K K_zero)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity
  (actual_cosine_hasSum weight)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower (rootCoeff rootCoeff_bound)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder (phaseOrbit_eq_mode)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (coeff_real)

private theorem phase_as_orbit (hRH : RiemannHypothesis) (r u : ℝ) (k : ℕ) :
    Complex.exp (frequency k / (r : ℂ) * (u : ℂ)) = (phaseOrbit (u / r) k : ℂ) := by
  rw [phaseOrbit_eq_mode hRH]
  congr 1
  push_cast
  ring

private theorem cosine_majorant_hasSum (hRH : RiemannHypothesis) (r t : ℝ) :
    HasSum (fun k => (2 * r) * (weight k * (1 - Real.cos ((actualZero k).im * t))))
      ((2 * r) * (K 0 - K t)) := by
  have h := ((Complex.hasSum_re (actual_cosine_hasSum hRH 0)).sub
    (Complex.hasSum_re (actual_cosine_hasSum hRH t))).mul_left (2 * r)
  convert h using 1
  funext k
  simp only [Complex.ofReal_re, mul_zero, Real.cos_zero, mul_one, weight]
  ring

private theorem symmetric_increment_majorant (hRH : RiemannHypothesis) {r : ℝ}
    (hr : 1 < r) (h u : ℝ) :
    |rootSignal r (u + h) + rootSignal r (u - h) - 2 * rootSignal r u| ≤
      (2 * r) * (K 0 - K (h / r)) / (1 / 2 - (2 * r)⁻¹) := by
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  have hr0 : 0 < r := by linarith
  have hs : 0 < s := by
    dsimp [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  let mode := fun (v : ℝ) (k : ℕ) => (phaseOrbit (v / r) k : ℂ)
  let term := fun (v : ℝ) (k : ℕ) => (rootCoeff r k * mode v k).re
  let total := fun v => (∑' k, rootCoeff r k * mode v k).re
  have hsum (v : ℝ) : HasSum (term v) (total v) := by
    simpa only [term, total, mode, phase_as_orbit hRH] using root_series_hasSum hRH hr v
  have hscale (v : ℝ) : rootSignal r v = total v / s := by
    simp only [rootSignal, total, mode, s, phase_as_orbit hRH]
  have hparts := ((hsum (u + h)).add (hsum (u - h))).sub ((hsum u).mul_left (2 : ℝ))
  have hmajor := cosine_majorant_hasSum hRH r (h / r)
  have hadd (x y : ℝ) (k : ℕ) : mode (x + y) k = mode x k * mode y k := by
    simp only [mode, add_div, phaseOrbit, add_mul, Circle.exp_add, Circle.coe_mul]
  have hb (k : ℕ) :
      |term (u + h) k + term (u - h) k - 2 * term u k| ≤
        (2 * r) * (weight k * (1 - Real.cos ((actualZero k).im * (h / r)))) := by
    let x := (actualZero k).im * (h / r)
    have hmode : mode h k + mode (-h) k - 2
        = ((2 * (Real.cos x - 1) : ℝ) : ℂ) := by
      have hpos : mode h k = Complex.exp ((x : ℂ) * Complex.I) := by
        simp only [mode, phaseOrbit, Circle.coe_exp, x]
        congr 1
        push_cast
        ring
      have hneg : mode (-h) k = Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
        simp only [mode, phaseOrbit, neg_div, neg_mul, Circle.coe_exp, x]
        rw [mul_comm (h / r)]
      rw [hpos, hneg, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
        Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    have hcollapse :
        term (u + h) k + term (u - h) k - 2 * term u k =
          (rootCoeff r k * mode u k * (mode h k + mode (-h) k - 2)).re := by
      simp only [term, sub_eq_add_neg u h, hadd, mul_add, mul_sub, Complex.add_re,
        Complex.sub_re, ← mul_assoc, mul_comm (_ * _) (2 : ℂ)]
      simp [Complex.mul_re]
      ring
    have hnorm : ‖rootCoeff r k‖ ≤ r * weight k := by
      have hw : 0 ≤ weight k := by unfold weight; positivity
      have hw_eq : actualCoeff k = (weight k : ℂ) := coeff_real hRH k
      simpa only [hw_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
        using rootCoeff_bound hr k
    have hphase : ‖mode u k‖ = 1 := Circle.norm_coe _
    have hcos : 0 ≤ 1 - Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
    have hmul : ‖((2 * (Real.cos x - 1) : ℝ) : ℂ)‖ = 2 * (1 - Real.cos x) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    rw [hcollapse, hmode]
    calc
      _ ≤ ‖rootCoeff r k * mode u k * ((2 * (Real.cos x - 1) : ℝ) : ℂ)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖rootCoeff r k‖ * (2 * (1 - Real.cos x)) := by
        rw [norm_mul, norm_mul, hphase, mul_one, hmul]
      _ ≤ (r * weight k) * (2 * (1 - Real.cos x)) :=
        mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ = _ := by dsimp [x]; ring
  rw [hscale, hscale, hscale, ← mul_div_assoc, ← add_div, ← sub_div, abs_div, abs_of_pos hs]
  apply div_le_div_of_nonneg_right ?_ hs.le
  rw [← hparts.tsum_eq, ← hmajor.tsum_eq, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hparts.summable.norm).trans
    (hparts.summable.norm.tsum_le_tsum (fun k => by simpa only [Real.norm_eq_abs] using hb k)
      hmajor.summable)

/-- On RH, the absolute symmetric difference has the same two-term cusp scale on every tail. -/
theorem root_signal_symmetric_tail_modulus (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    ∃ C > 0, ∀ U h : ℝ, 0 < h → h ≤ r / 2 →
      let values := (fun u : ℝ =>
        |rootSignal r (u + h) + rootSignal r (u - h) - 2 * rootSignal r u|) '' Ici U
      values.Nonempty ∧ BddAbove values ∧
        |sSup values - (h / s) * (Real.log (1 / h) + Real.log r - 2 * c)| ≤ C * h ^ 2 := by
  dsimp only
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  have hr0 : 0 < r := by linarith
  have hs : 0 < s := by
    dsimp [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  obtain ⟨C, hC, hcusp⟩ := root_signal_symmetric_cusp hRH hr
  refine ⟨C + 4 / (r * s), by positivity, ?_⟩
  intro U h hh hh'
  let t := h / r
  let D := fun u => rootSignal r (u + h) + rootSignal r (u - h) - 2 * rootSignal r u
  let V := (fun u => |D u|) '' Ici U
  let A := (h / s) * (Real.log (1 / h) + Real.log r - 2 * c)
  let B := (2 * r) * (K 0 - K t) / s
  change V.Nonempty ∧ BddAbove V ∧ |sSup V - A| ≤ (C + 4 / (r * s)) * h ^ 2
  have hV : V.Nonempty := ⟨|D U|, U, mem_Ici.mpr le_rfl, rfl⟩
  have hB : ∀ x ∈ V, x ≤ B := by
    rintro _ ⟨u, _, rfl⟩
    exact symmetric_increment_majorant hRH hr h u
  have hbounded : BddAbove V := ⟨B, hB⟩
  have horigin : D 0 ≤ sSup V := by
    by_contra! hlt
    have hb : sSup V < rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0 := by
      simpa only [D, zero_add, zero_sub] using hlt
    obtain ⟨u, hu, hdu⟩ := symmetric_difference_returns hRH hr h U hb
    exact (hdu.trans_le ((le_abs_self (D u)).trans (le_csSup hbounded ⟨u, hu, rfl⟩))).false
  have ht : 0 < t := div_pos hh hr0
  have ht' : t ≤ 1 / 2 := (div_le_iff₀ hr0).2 (by linarith)
  have hlog : Real.log (1 / h) + Real.log r = -Real.log t := by
    rw [one_div, Real.log_inv, Real.log_div hh.ne' hr0.ne']
    ring
  have hscale : r * t = h := by dsimp [t]; field_simp
  have hremainder : B - A = -(2 * r) * R t / s := by
    dsimp only [B, A]
    rw [hlog, R, K_zero, eq_div_iff hs.ne', sub_mul, div_mul_cancel₀ _ hs.ne',
      mul_right_comm (h / s), div_mul_cancel₀ _ hs.ne']
    rw [← hscale]
    ring
  have hupper : |B - A| ≤ (4 / (r * s)) * h ^ 2 := by
    rw [hremainder, abs_div, abs_of_pos hs, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * r)]
    calc
      _ ≤ (2 * r) * (2 * t ^ 2) / s :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (cusp_remainder_bound ht ht') (by positivity)) hs.le
      _ = _ := by dsimp [t]; field_simp [hr0.ne', hs.ne'] <;> ring
  have hlower : |D 0 - A| ≤ C * h ^ 2 := by
    simpa only [D, A, zero_add, zero_sub] using hcusp h hh hh'
  refine ⟨hV, hbounded, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hnonneg : 0 ≤ (4 / (r * s)) * h ^ 2 := by positivity
    linarith only [horigin, (abs_le.mp hlower).1, hnonneg]
  · have hnonneg : 0 ≤ C * h ^ 2 := by positivity
    linarith only [csSup_le hV hB, (abs_le.mp hupper).2, hnonneg]

#print axioms root_signal_symmetric_tail_modulus

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
