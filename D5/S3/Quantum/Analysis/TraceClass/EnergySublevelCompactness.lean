/- GID: D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace-norm compactness of complete singular spectral-energy state sublevels. -/

import D5.S3.Quantum.Analysis.TraceClass.FiniteCompression
import Mathlib.Topology.MetricSpace.Pseudo.Basic

noncomputable section
open scoped ComplexOrder InnerProductSpace ENNReal
open Filter Topology

namespace QuantumLogEnergy
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The entire positive trace-one energy sublevel, in the trace-class Banach space. -/
def energySublevel (T : Reference H) (M : ℝ) : Set (TraceClass H) :=
  {rho | 0 ≤ rho.1 ∧ (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1 ∧
    spectralEnergy T rho ≤ ENNReal.ofReal M}

private theorem lowerSemicontinuous_regularizedSupremum_state (T : Reference H) :
    LowerSemicontinuous (regularizedSupremum T) := by
  apply lowerSemicontinuous_iSup
  intro n
  exact (ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp
    (TraceClass.tracePairing (logRegularization ((n : ℝ) + 1)⁻¹ T.1.1)).continuous)).lowerSemicontinuous

/-- Singular energy is lower semicontinuous in the state on its full positive cone. -/
theorem lowerSemicontinuousOn_spectralEnergy_state (T : Reference H) :
    LowerSemicontinuousOn (spectralEnergy T) {rho : TraceClass H | 0 ≤ rho.1} := by
  intro rho hrho
  apply ((lowerSemicontinuous_regularizedSupremum_state T).lowerSemicontinuousWithinAt _ rho).congr_of_eventuallyEq hrho
  exact eventually_nhdsWithin_of_forall fun gamma hgamma =>
    (spectralEnergy_eq_regularizedSupremum T gamma hgamma).symm

/-- Positivity, normalization and the singular energy bound are closed in trace norm. -/
theorem isClosed_energySublevel (T : Reference H) (M : ℝ) :
    IsClosed (energySublevel T M) := by
  have hpos : IsClosed {rho : TraceClass H | 0 ≤ rho.1} :=
    CStarAlgebra.isClosed_nonneg.preimage (operatorCLM (H := H)).continuous
  obtain ⟨v, hv, heq⟩ := lowerSemicontinuousOn_iff_preimage_Iic.mp
    (lowerSemicontinuousOn_spectralEnergy_state T) (ENNReal.ofReal M)
  have htrace : Continuous (fun rho : TraceClass H =>
      (trace rho.1 (TraceClass.isTraceClass_coe rho)).re) := by
    have hc : Continuous (fun rho : TraceClass H =>
        (TraceClass.tracePairing (1 : H →L[ℂ] H) rho).re) :=
      Complex.continuous_re.comp (TraceClass.tracePairing (1 : H →L[ℂ] H)).continuous
    apply hc.congr
    intro rho
    exact congrArg Complex.re (TraceClass.trace_transport (one_mul rho.1)
      (TraceClass.isTraceClass_mul_coe 1 rho))
  have hset : energySublevel T M =
      ({rho : TraceClass H | 0 ≤ rho.1} ∩ v) ∩
      {rho : TraceClass H | (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1} := by
    rw [← heq]
    ext rho
    simp only [energySublevel, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Iic]
    tauto
  rw [hset]
  exact (hpos.inter hv).inter (isClosed_eq htrace continuous_const)

private theorem finite_spectral_threshold {w : Set H} (s : w → ℝ)
    (hs : Summable s) (R : ℝ) : {i | Real.exp (-R) ≤ s i}.Finite := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hs.tsum_ofReal_ne_top
    (show ENNReal.ofReal (Real.exp (-R)) ≠ 0 from
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))).subset
  intro i hi
  exact ENNReal.ofReal_le_ofReal hi

private theorem singularLog_threshold {t R : ℝ} (ht : 0 ≤ t)
    (h : t < Real.exp (-R)) : ENNReal.ofReal R ≤ singularLog t := by
  by_cases hz : t = 0
  · simp [singularLog, hz]
  · rw [singularLog, if_neg hz]
    apply ENNReal.ofReal_le_ofReal
    have hh := Real.log_lt_log (lt_of_le_of_ne ht (Ne.symm hz)) h
    rw [Real.log_exp] at hh
    linarith

private theorem tailMass_le_energy {w : Set H} (T : Reference H)
    (b : HilbertBasis w ℂ H) (s : w → ℝ) (hs : ∀ i, 0 ≤ s i)
    (heigen : ∀ i, T.1.1 (b i) = (s i : ℂ) • b i)
    (F : Finset w) (R : ℝ) (hR : 0 < R)
    (hF : ∀ i, i ∉ F → s i < Real.exp (-R))
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) (M : ℝ) (hM : 0 ≤ M)
    (henergy : spectralEnergy T rho ≤ ENNReal.ofReal M) :
    TraceClassCompression.tailMass b F rho ≤ M / R := by
  classical
  let p := diagonal b rho
  have hp (i : w) : 0 ≤ p i :=
    (rho.1.nonneg_iff_isPositive.mp hrho).re_inner_nonneg_right (b i)
  let q : w → ℝ := fun i => if i ∈ F then 0 else p i
  have hq (i : w) : 0 ≤ q i := by
    dsimp [q]
    split_ifs
    · exact le_rfl
    · exact hp i
  have hqp (i : w) : q i ≤ p i := by dsimp [q]; split_ifs <;> simp_all
  have hsum : Summable q := Summable.of_nonneg_of_le hq hqp (diagonal_hasSum b rho).summable
  have hbound : ENNReal.ofReal R * ENNReal.ofReal (∑' i, q i) ≤ spectralEnergy T rho := by
    rw [ENNReal.ofReal_tsum_of_nonneg hq hsum, ← ENNReal.tsum_mul_left,
      ← spectralSeries_eq_spectralEnergy T b s hs heigen rho hrho]
    apply ENNReal.tsum_le_tsum
    intro i
    by_cases hi : i ∈ F
    · simp [q, hi]
    · simp only [q, if_neg hi]
      simpa only [mul_comm] using mul_le_mul' (le_refl (ENNReal.ofReal (p i)))
        (singularLog_threshold (hs i) (hF i hi))
  have hb : R * (∑' i, q i) ≤ M := by
    apply (ENNReal.ofReal_le_ofReal_iff hM).mp
    rw [ENNReal.ofReal_mul hR.le]
    exact hbound.trans henergy
  change (∑' i, q i) ≤ M / R
  exact (le_div_iff₀ hR).mpr (by simpa only [mul_comm] using hb)

/-- The entire state sublevel is totally bounded in the actual trace norm. -/
theorem totallyBounded_energySublevel (T : Reference H) (M : ℝ) (hM : 0 ≤ M) :
    TotallyBounded (energySublevel T M) := by
  classical
  obtain ⟨w, b, s, hs, heigen, hsum, _⟩ :=
    TraceClassSpectral.exists_nonneg_trace_spectral_data T.2.1
      (TraceClass.isTraceClass_coe T.1)
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  let d : ℝ := ε / 4
  have hd : 0 < d := by dsimp [d]; positivity
  let R : ℝ := (M + 1) / d ^ 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall : 2 * Real.sqrt (M / R) < ε / 2 := by
    have hdiv : M / R < d ^ 2 := by
      apply (div_lt_iff₀ hR).mpr
      dsimp [R]
      rw [mul_div_cancel₀ _ (ne_of_gt (sq_pos_of_pos hd))]
      linarith
    have hsqrt : Real.sqrt (M / R) < d := (Real.sqrt_lt' hd).mpr hdiv
    dsimp [d] at hsqrt
    linarith
  let F : Finset w := (finite_spectral_threshold s hsum R).toFinset
  have hF (i : w) : i ∉ F → s i < Real.exp (-R) := by
    simpa only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] using
      (fun h : ¬ Real.exp (-R) ≤ s i => lt_of_not_ge h)
  obtain ⟨K, hK, hcompress⟩ := TraceClassCompression.exists_compact_compressions
    (TraceClassCompression.finiteSpan b F)
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
    (ε / 2) (by positivity)
  refine ⟨t, ht, ?_⟩
  intro rho hrho
  have hnorm : ‖rho‖ = 1 := by
    rw [TraceClass.norm_eq_traceNorm, traceNorm_eq_re_trace _ hrho.1, hrho.2.1]
  let c := TraceClassCompression.compress
    (TraceClassCompression.finiteSpan b F).starProjection rho
  have hc : c ∈ K := hcompress rho hnorm.le
  have herror : dist rho c < ε / 2 := by
    rw [dist_eq_norm]
    exact ((TraceClassCompression.norm_sub_compress_le b F rho hrho.1 hrho.2.1).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
        (tailMass_le_energy T b s hs heigen F R hR hF rho hrho.1 M hM hrho.2.2))
        (by norm_num))).trans_lt hsmall
  obtain ⟨z, hzt, hcz⟩ := Set.mem_iUnion₂.mp (hcover hc)
  apply Set.mem_iUnion₂.mpr
  refine ⟨z, hzt, ?_⟩
  exact (dist_triangle rho c z).trans_lt (by
    have hh : dist c z < ε / 2 := hcz
    linarith)

/-- For every positive trace-class contraction on an arbitrary complete complex
Hilbert space, its complete positive trace-one singular-energy sublevel is
compact in the genuine trace norm. -/
theorem isCompact_energySublevel (T : Reference H) (M : ℝ) (hM : 0 ≤ M) :
    IsCompact (energySublevel T M) :=
  (totallyBounded_energySublevel T M hM).isCompact_of_isClosed (isClosed_energySublevel T M)

#print axioms lowerSemicontinuousOn_spectralEnergy_state
#print axioms isCompact_energySublevel

end QuantumLogEnergy
