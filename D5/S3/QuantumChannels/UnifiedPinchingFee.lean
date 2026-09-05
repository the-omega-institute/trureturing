/- GID: D5/S3/QuantumChannels/UnifiedPinchingFee
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/UnifiedPinchingFee
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform pinching-fee transition and endpoint laws. -/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open Filter Set Topology Real

noncomputable section

namespace D5.S3.QuantumChannels.UnifiedPinchingFee

/-- The hand-tremor scale `t = delta^2 / 4` from the source theorem. -/
def handTremor (delta : ℝ) : ℝ := delta ^ 2 / 4

/-- The distance `u = 1 - r` from the pure-state boundary. -/
def doorGap (r : ℝ) : ℝ := 1 - r

/-- The transition coordinate `x = u / (2t)`. -/
def transitionCoordinate (r t : ℝ) : ℝ := doorGap r / (2 * t)

private def entropyIncrement (p shift : ℝ) : ℝ :=
  Real.binEntropy (p + shift) - Real.binEntropy p

/-- The binary-entropy fee at radius `r` and quadratic scale `t`. -/
def quadraticPinchingFee (r t : ℝ) : ℝ :=
  entropyIncrement ((1 - r) / 2) (r * t)

private def regularEntropy (p : ℝ) : ℝ := Real.negMulLog (1 - p)

/-- The uniform transition coefficient multiplying `t`. -/
def transitionLeading (t x : ℝ) : ℝ :=
  Real.log t⁻¹ + 1 + x * Real.log x - (x + 1) * Real.log (x + 1)

/-- The scale-independent correction in the uniform transition coefficient. -/
def transitionCorrection (x : ℝ) : ℝ :=
  1 + x * Real.log x - (x + 1) * Real.log (x + 1)

/-- The radius `r = 1 - 2tx` associated with a fixed transition coordinate. -/
def boundaryRadius (t x : ℝ) : ℝ := 1 - 2 * t * x

/-- The pinching fee along the boundary scaling `r = 1 - 2tx`. -/
def boundaryPinchingFee (t x : ℝ) : ℝ :=
  quadraticPinchingFee (boundaryRadius t x) t

/-- The shifted upper eigenvalue along the boundary scaling. -/
def boundaryUpperProbability (t x : ℝ) : ℝ :=
  t * (x + 1) - 2 * x * t ^ 2

private theorem regularEntropy_boundary_limit (x : ℝ) :
    Tendsto
      (fun t : ℝ =>
        (regularEntropy (boundaryUpperProbability t x) - regularEntropy (t * x)) / t)
      (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
  have hlinear := (hasDerivAt_id (x := (0 : ℝ))).mul_const (x + 1)
  have hquadratic := ((hasDerivAt_id (x := (0 : ℝ))).mul
    (hasDerivAt_id (x := (0 : ℝ)))).const_mul (2 * x)
  have hupper := hlinear.sub hquadratic
  simp only [Pi.mul_apply, id_eq, one_mul, mul_zero, zero_mul,
    add_zero, sub_zero] at hupper
  have hleftInner := hupper.const_sub 1
  simp only [Pi.sub_apply] at hleftInner
  have hleftOuter :
      HasDerivAt Real.negMulLog (-1)
        (1 - (((fun y : ℝ => y * (x + 1)) - fun y : ℝ => 2 * x * (y * y)) 0)) := by
    simpa using Real.hasDerivAt_negMulLog (by norm_num : (1 : ℝ) ≠ 0)
  have hleft := (hleftOuter.comp 0 hleftInner).tendsto_slope_zero
  have hrightInner : HasDerivAt (fun t : ℝ => 1 - t * x) (-x) 0 :=
    by simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (x := (0 : ℝ))).mul_const x).const_sub 1
  have hrightOuter : HasDerivAt Real.negMulLog (-1) (1 - (0 : ℝ) * x) := by
    simpa using Real.hasDerivAt_negMulLog (by norm_num : (1 : ℝ) ≠ 0)
  have hright := (hrightOuter.comp 0 hrightInner).tendsto_slope_zero
  have hslope := hleft.sub hright
  have hraw :
      Tendsto
        (fun t : ℝ =>
          t⁻¹ * Real.negMulLog (1 - boundaryUpperProbability t x) -
            t⁻¹ * Real.negMulLog (1 - t * x))
        (𝓝[≠] 0) (𝓝 ((x + 1) - x)) := by
    simpa only [Function.comp_apply, zero_add, zero_mul, mul_zero, sub_zero,
      Real.negMulLog_one, smul_eq_mul, boundaryUpperProbability, pow_two,
      neg_mul, neg_neg, one_mul] using hslope
  have hslope' :
      Tendsto
        (fun t : ℝ => t⁻¹ *
          (Real.negMulLog (1 - boundaryUpperProbability t x) -
            Real.negMulLog (1 - t * x)))
        (𝓝[≠] 0) (𝓝 1) := by
    convert hraw using 1
    · funext t
      ring
    · congr 1
      ring
  have hrestricted :
      Tendsto
        (fun t : ℝ => t⁻¹ *
          ((regularEntropy (boundaryUpperProbability t x) - regularEntropy (t * x)) -
            (regularEntropy (boundaryUpperProbability 0 x) -
              regularEntropy (0 * x))))
        (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
    simpa [regularEntropy, boundaryUpperProbability] using hslope'.mono_left
      (nhdsWithin_mono 0 (by intro y hy; exact ne_of_gt hy))
  simpa [div_eq_inv_mul, boundaryUpperProbability, regularEntropy] using hrestricted

private theorem singular_boundary_identity (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t)
    (hy : 0 < x + 1 - 2 * t * x) :
    (Real.negMulLog (boundaryUpperProbability t x) - Real.negMulLog (t * x)) / t -
        (Real.log t⁻¹ + x * Real.log x - (x + 1) * Real.log (x + 1)) =
      2 * x * (t * Real.log t) -
        (x + 1 - 2 * t * x) * Real.log (x + 1 - 2 * t * x) +
          (x + 1) * Real.log (x + 1) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [boundaryUpperProbability, Real.negMulLog]
    field_simp [ht.ne']
    ring_nf
  have hx0 : x ≠ 0 := hx.ne'
  have hy0 : x + 1 - 2 * t * x ≠ 0 := hy.ne'
  have hupper :
      boundaryUpperProbability t x = t * (x + 1 - 2 * t * x) := by
    simp only [boundaryUpperProbability]
    ring_nf
  rw [hupper, Real.negMulLog, Real.negMulLog,
    Real.log_mul ht.ne' hy0, Real.log_mul ht.ne' hx0, Real.log_inv]
  field_simp [ht.ne']
  ring

/-- The singular entropy remainder vanishes uniformly along the fixed-`x` boundary scale.
This is the nontrivial analytic step behind the multiplicative transition law. -/
theorem singular_boundary_error_limit (x : ℝ) (hx : 0 ≤ x) :
    Tendsto
      (fun t : ℝ =>
        (Real.negMulLog (boundaryUpperProbability t x) - Real.negMulLog (t * x)) / t -
          (Real.log t⁻¹ + x * Real.log x - (x + 1) * Real.log (x + 1)))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have htLog :
      Tendsto (fun t : ℝ => t * Real.log t) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have h :
        Tendsto (fun t : ℝ => t * Real.log t) (𝓝 (0 : ℝ))
          (𝓝 ((0 : ℝ) * Real.log 0)) :=
      Real.continuous_mul_log.continuousAt
    simpa using h.mono_left (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0)
  have hfirst :
      Tendsto (fun t : ℝ => 2 * x * (t * Real.log t))
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    simpa using htLog.const_mul (2 * x)
  have hyTendsto :
      Tendsto (fun t : ℝ => x + 1 - 2 * t * x)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (x + 1)) := by
    have hcont : ContinuousAt (fun t : ℝ => x + 1 - 2 * t * x) 0 := by fun_prop
    convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 1
    congr 1
    ring_nf
  have hyMulLog :
      Tendsto
        (fun t : ℝ => (x + 1 - 2 * t * x) * Real.log (x + 1 - 2 * t * x))
        (nhdsWithin 0 (Ioi 0)) (𝓝 ((x + 1) * Real.log (x + 1))) :=
    Real.continuous_mul_log.continuousAt.tendsto.comp hyTendsto
  have hformula :
      Tendsto
        (fun t : ℝ =>
          2 * x * (t * Real.log t) -
            (x + 1 - 2 * t * x) * Real.log (x + 1 - 2 * t * x) +
              (x + 1) * Real.log (x + 1))
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    convert (hfirst.sub hyMulLog).add_const ((x + 1) * Real.log (x + 1)) using 1
    ring_nf
  apply hformula.congr'
  have hyPositive : ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < x + 1 - 2 * t * x := by
    apply hyTendsto.eventually
    exact Ioi_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, hyPositive] with t ht hy
  exact (singular_boundary_identity x t hx ht hy).symm

private theorem boundary_pinching_fee_asymptotic (x : ℝ) (hx : 0 ≤ x) :
    Tendsto
      (fun t : ℝ => boundaryPinchingFee t x / t -
        (Real.log t⁻¹ + x * Real.log x - (x + 1) * Real.log (x + 1)))
      (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
  have hsum := (singular_boundary_error_limit x hx).add (regularEntropy_boundary_limit x)
  convert hsum using 1
  · funext t
    have hbase : (1 - boundaryRadius t x) / 2 = t * x := by
      simp only [boundaryRadius]
      ring
    have hupper : t * x + boundaryRadius t x * t = boundaryUpperProbability t x := by
      simp only [boundaryRadius, boundaryUpperProbability]
      ring
    rw [boundaryPinchingFee, quadraticPinchingFee, entropyIncrement, hbase, hupper,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    change
      ((Real.negMulLog (boundaryUpperProbability t x) +
          regularEntropy (boundaryUpperProbability t x)) -
        (Real.negMulLog (t * x) + regularEntropy (t * x))) / t - _ =
        ((Real.negMulLog (boundaryUpperProbability t x) - Real.negMulLog (t * x)) / t - _) +
          (regularEntropy (boundaryUpperProbability t x) - regularEntropy (t * x)) / t
    ring
  · norm_num

private theorem boundary_pinching_fee_ratio (x : ℝ) (hx : 0 ≤ x) :
    Tendsto
      (fun t : ℝ => boundaryPinchingFee t x / (t * transitionLeading t x))
      (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
  have hbase := boundary_pinching_fee_asymptotic x hx
  have herror :
      Tendsto
        (fun t : ℝ => boundaryPinchingFee t x / t - transitionLeading t x)
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have h := hbase.sub_const 1
    convert h using 1
    · funext t
      simp only [transitionLeading]
      ring
    · norm_num
  have hloginv :
      Tendsto (fun t : ℝ => Real.log t⁻¹) (nhdsWithin 0 (Ioi 0)) atTop := by
    simpa only [Real.log_inv] using
      (tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero)
  have hlead :
      Tendsto (fun t : ℝ => transitionLeading t x)
        (nhdsWithin 0 (Ioi 0)) atTop := by
    have hconst :
        Tendsto
          (fun _t : ℝ => 1 + x * Real.log x - (x + 1) * Real.log (x + 1))
          (nhdsWithin 0 (Ioi 0))
          (𝓝 (1 + x * Real.log x - (x + 1) * Real.log (x + 1))) :=
      tendsto_const_nhds
    convert hloginv.atTop_add hconst using 1
    funext t
    simp only [transitionLeading]
    ring
  have hfrac := herror.div_atTop hlead
  have hadd :
      Tendsto
        (fun t : ℝ => 1 +
          (boundaryPinchingFee t x / t - transitionLeading t x) / transitionLeading t x)
        (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hfrac)
  refine hadd.congr' ?_
  have hleadPos : ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < transitionLeading t x :=
    hlead.eventually (eventually_gt_atTop 0)
  filter_upwards [self_mem_nhdsWithin, hleadPos] with t ht htLead
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hlead0 : transitionLeading t x ≠ 0 := ne_of_gt htLead
  field_simp [ht0, hlead0]
  ring

private theorem transition_correction_pure_limit :
    Tendsto transitionCorrection (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
  have hcont : ContinuousAt transitionCorrection 0 := by
    unfold transitionCorrection
    fun_prop
  simpa [transitionCorrection] using hcont.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0)

private theorem transition_correction_mixed_limit :
    Tendsto (fun x : ℝ => transitionCorrection x + Real.log x) atTop (𝓝 0) := by
  have hmain := Real.tendsto_mul_log_one_add_div_atTop 1
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hinner : Tendsto (fun x : ℝ => 1 + x⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hlog : Tendsto (fun x : ℝ => Real.log (1 + x⁻¹)) atTop (𝓝 0) := by
    change Tendsto (Real.log ∘ fun x : ℝ => 1 + x⁻¹) atTop (𝓝 0)
    simpa only [Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hinner
  have hproduct :
      Tendsto (fun x : ℝ => (x + 1) * Real.log (1 + 1 / x)) atTop (𝓝 1) := by
    have hsum := hmain.add hlog
    convert hsum using 1
    · funext x
      simp only [one_div]
      ring
    · norm_num
  have hzero :
      Tendsto (fun x : ℝ => 1 - (x + 1) * Real.log (1 + 1 / x)) atTop (𝓝 0) := by
    have honeT : Tendsto (fun _x : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using honeT.sub hproduct
  refine hzero.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : x ≠ 0 := hx.ne'
  have hone : 1 + 1 / x ≠ 0 := by positivity
  have hfactor : x + 1 = x * (1 + 1 / x) := by
    field_simp [hx0]
  rw [transitionCorrection, hfactor, Real.log_mul hx0 hone]
  field_simp [hx0]
  ring

private theorem transition_leading_mixed_limit (r : ℝ) (hr1 : r < 1) :
    Tendsto
      (fun x : ℝ => transitionLeading (doorGap r / (2 * x)) x)
      atTop (𝓝 (Real.log (2 / doorGap r))) := by
  have hbase := transition_correction_mixed_limit.add_const
    (Real.log (2 / doorGap r))
  have heq :
      (fun x : ℝ => transitionLeading (doorGap r / (2 * x)) x) =ᶠ[atTop]
        fun x : ℝ =>
          transitionCorrection x + Real.log x + Real.log (2 / doorGap r) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hgap0 : doorGap r ≠ 0 := by
      unfold doorGap
      linarith
    have hfactor : (doorGap r / (2 * x))⁻¹ = x * (2 / doorGap r) := by
      field_simp [hx0, hgap0]
    rw [transitionLeading, hfactor, Real.log_mul hx0 (by positivity)]
    unfold transitionCorrection
    ring
  apply Tendsto.congr' heq.symm
  simpa using hbase

private theorem mixed_state_coefficient (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun t : ℝ => quadraticPinchingFee r t / t)
      (𝓝[>] 0) (𝓝 (2 * r * Real.artanh r)) := by
  let p : ℝ := (1 - r) / 2
  have hp0 : p ≠ 0 := by
    dsimp [p]
    linarith
  have hp1 : p ≠ 1 := by
    dsimp [p]
    linarith
  have hinner : HasDerivAt (fun t : ℝ => p + r * t) r 0 := by
    simpa using ((hasDerivAt_id (x := (0 : ℝ))).const_mul r).const_add p
  have hderiv :
      HasDerivAt
        (fun t : ℝ => Real.binEntropy (p + r * t) - Real.binEntropy p)
        ((Real.log (1 - p) - Real.log p) * r) 0 := by
    have houter :
        HasDerivAt Real.binEntropy (Real.log (1 - p) - Real.log p) (p + r * 0) := by
      simpa using Real.hasDerivAt_binEntropy hp0 hp1
    exact (houter.comp 0 hinner).sub_const _
  have hslope := hderiv.tendsto_slope_zero
  have hrestricted :
      Tendsto
        (fun t : ℝ => t⁻¹ *
          ((Real.binEntropy (p + r * t) - Real.binEntropy p) -
            (Real.binEntropy (p + r * 0) - Real.binEntropy p)))
        (𝓝[>] 0) (𝓝 ((Real.log (1 - p) - Real.log p) * r)) := by
    simpa [smul_eq_mul] using hslope.mono_left
      (nhdsWithin_mono 0 (by intro x hx; exact ne_of_gt hx))
  have hartanh : Real.log (1 - p) - Real.log p = 2 * Real.artanh r := by
    rw [Real.artanh_eq_half_log (show r ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)]
    have hplus : (1 + r) / 2 ≠ 0 := by positivity
    have hminus : (1 - r) / 2 ≠ 0 := by positivity
    dsimp [p]
    rw [show 1 - (1 - r) / 2 = (1 + r) / 2 by ring]
    rw [show 2 * (1 / 2 * Real.log ((1 + r) / (1 - r))) =
      Real.log ((1 + r) / (1 - r)) by ring]
    rw [← Real.log_div hplus hminus]
    congr 1
    field_simp
  convert hrestricted using 1
  · funext t
    simp only [quadraticPinchingFee, entropyIncrement]
    dsimp [p]
    ring_nf
  · rw [hartanh]
    ring_nf

private theorem mixed_state_delta_coefficient (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto
      (fun delta : ℝ => quadraticPinchingFee r (handTremor delta) / delta ^ 2)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (r * Real.artanh r / 2)) := by
  have hscale :
      Tendsto (fun δ : ℝ => δ ^ 2 / 4)
        (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun δ : ℝ => δ ^ 2 / 4) 0 := by
        fun_prop
      simpa using hcont.tendsto.mono_left
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < δ at hδ
      exact div_pos (sq_pos_of_pos hδ) (by norm_num)
  have hcomposed := (mixed_state_coefficient r hr0 hr1).comp hscale
  have hscaled := hcomposed.div_const 4
  convert hscaled using 1
  · funext delta
    by_cases hdelta0 : delta = 0
    · simp [hdelta0, handTremor, quadraticPinchingFee, entropyIncrement]
    · simp only [Function.comp_apply, handTremor]
      field_simp [hdelta0]
  · ring_nf

/-- **Unified pinching-fee law.** Along `r = 1 - 2tx`, the exact binary-entropy fee is
asymptotic to `t` times the uniform transition coefficient. Its correction tends to one at the
pure-state end, while the fixed-gap scaling tends to `log (2/u)`. For fixed `0 < r < 1`, returning
to `t = delta^2/4` gives the coefficient `r * artanh r / 2`. -/
theorem unified_pinching_fee_law (x r : ℝ)
    (hx : 0 ≤ x) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto
        (fun t : ℝ => boundaryPinchingFee t x / (t * transitionLeading t x))
        (nhdsWithin 0 (Ioi 0)) (𝓝 1) ∧
      Tendsto transitionCorrection (nhdsWithin 0 (Ioi 0)) (𝓝 1) ∧
      Tendsto
          (fun y : ℝ => transitionLeading (doorGap r / (2 * y)) y)
          atTop (𝓝 (Real.log (2 / doorGap r))) ∧
      Tendsto
          (fun delta : ℝ => quadraticPinchingFee r (handTremor delta) / delta ^ 2)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (r * Real.artanh r / 2)) := by
  exact ⟨boundary_pinching_fee_ratio x hx, transition_correction_pure_limit,
    transition_leading_mixed_limit r hr1, mixed_state_delta_coefficient r hr0 hr1⟩

#print axioms unified_pinching_fee_law

end D5.S3.QuantumChannels.UnifiedPinchingFee
