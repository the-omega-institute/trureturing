/- GID: D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/SpectralEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular spectral logarithmic energy on full native eigenbases and its actual trace regularization. -/

import D5.S3.Quantum.Analysis.TraceClass.LogRegularization
import D5.S3.Quantum.Analysis.TraceClass.Spectral
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
open scoped ComplexOrder InnerProductSpace ENNReal
open Filter Topology

namespace QuantumLogEnergy
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The singular nonnegative logarithm; its value at zero is infinity. -/
def singularLog (t : ℝ) : ℝ≥0∞ := if t = 0 then ∞ else ENNReal.ofReal (-Real.log t)

/-- The actual positive diagonal of the first trace-class argument. -/
def diagonal {w : Set H} (b : HilbertBasis w ℂ H) (rho : TraceClass H) (i : w) : ℝ :=
  (⟪b i, rho.1 (b i)⟫_ℂ).re

/-- Full-basis energy, retaining zero eigenspaces and the convention zero times infinity is zero. -/
def spectralSeries {w : Set H} (b : HilbertBasis w ℂ H) (s : w → ℝ)
    (rho : TraceClass H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (diagonal b rho i) * singularLog (s i)

private theorem diagonal_nonneg {w : Set H} (b : HilbertBasis w ℂ H)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) (i : w) : 0 ≤ diagonal b rho i :=
  (rho.1.nonneg_iff_isPositive.mp hrho).re_inner_nonneg_right (b i)

/-- The diagonal is genuinely summable and has the actual trace mass. -/
theorem diagonal_hasSum {w : Set H} (b : HilbertBasis w ℂ H) (rho : TraceClass H) :
    HasSum (diagonal b rho) (trace rho.1 (TraceClass.isTraceClass_coe rho)).re := by
  have h := summable_trace_diagonal_of_isTraceClass (TraceClass.isTraceClass_coe rho) b
  rw [trace_eq_of_hilbertBasis (TraceClass.isTraceClass_coe rho) b]
  exact h.hasSum.mapL Complex.reCLM

/-- Every eigenvalue of the actual contraction is at most one. -/
theorem spectral_value_le_one (T : Reference H) {w : Set H}
    (b : HilbertBasis w ℂ H) (s : w → ℝ)
    (heigen : ∀ i, T.1.1 (b i) = (s i : ℂ) • b i) (i : w) : s i ≤ 1 := by
  have h := ((1 - T.1.1).nonneg_iff_isPositive.mp (sub_nonneg.mpr T.2.2)).re_inner_nonneg_right (b i)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
    heigen i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i,
    one_pow, Complex.ofReal_one, mul_one, Complex.sub_re, Complex.one_re, Complex.ofReal_re] at h
  norm_num at h
  linarith

private def scalarRegularization (n : ℕ) (t : ℝ) : ℝ :=
  Real.log (1 + ((n : ℝ) + 1)⁻¹) - Real.log (t + ((n : ℝ) + 1)⁻¹)

private theorem scalarRegularization_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    0 ≤ scalarRegularization n t := by
  apply sub_nonneg.mpr
  exact Real.log_le_log (by positivity) (by linarith)

private theorem scalarRegularization_monotone {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Monotone (fun n => ENNReal.ofReal (scalarRegularization n t)) := by
  intro m n hmn
  apply ENNReal.ofReal_le_ofReal
  dsimp [scalarRegularization]
  have hmn' : ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ :=
    inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  rw [← Real.log_div (by positivity) (by positivity),
    ← Real.log_div (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

private theorem scalarRegularization_iSup {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (⨆ n, ENNReal.ofReal (scalarRegularization n t)) = singularLog t := by
  have hgrid : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply iSup_eq_of_tendsto (scalarRegularization_monotone ht ht1)
  by_cases ht0 : t = 0
  · rw [singularLog, if_pos ht0]
    apply ENNReal.tendsto_ofReal_nhds_top.mpr
    have hpoint (n : ℕ) : scalarRegularization n t = Real.log ((n : ℝ) + 2) := by
      rw [ht0]
      dsimp [scalarRegularization]
      rw [zero_add, ← Real.log_div (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    simp_rw [hpoint]
    exact Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  · rw [singularLog, if_neg ht0]
    have hlim := ((hgrid.const_add 1).log (by norm_num : (1 : ℝ) + 0 ≠ 0)).sub
      ((hgrid.const_add t).log (by simpa using ht0))
    exact ENNReal.tendsto_ofReal (by simpa [scalarRegularization] using hlim)

/-- Bounded CFC trace evaluation uses actual trace-class-product summability. -/
theorem regularizedEnergy_hasSum (T : Reference H) {w : Set H}
    (b : HilbertBasis w ℂ H) (s : w → ℝ)
    (heigen : ∀ i, T.1.1 (b i) = (s i : ℂ) • b i)
    (rho : TraceClass H) (n : ℕ) :
    HasSum (fun i => diagonal b rho i * scalarRegularization n (s i))
      (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 rho) := by
  let B := logRegularization ((n : ℝ) + 1)⁻¹ T.1.1
  have hB : B.IsPositive := B.nonneg_iff_isPositive.mp
    (logRegularization_nonneg (by positivity) T.2.1 T.2.2)
  have hdiag (i : w) : (⟪b i, (B * rho.1) (b i)⟫_ℂ).re =
      diagonal b rho i * scalarRegularization n (s i) := by
    rw [ContinuousLinearMap.mul_apply, ← hB.inner_left_eq_inner_right]
    have heB : B (b i) = (scalarRegularization n (s i) : ℂ) • b i := by
      simpa only [scalarRegularization, Complex.ofReal_sub] using
        logRegularization_apply_eigenvector (epsilon := ((n : ℝ) + 1)⁻¹)
          (by positivity) T.2.1 (s i) (b i) (heigen i)
    rw [heB, inner_smul_left]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, diagonal]
    ring
  have htc := TraceClass.isTraceClass_mul_coe B rho
  have hh := (summable_trace_diagonal_of_isTraceClass htc b).hasSum.mapL Complex.reCLM
  rw [← trace_eq_of_hilbertBasis htc b] at hh
  change HasSum (fun i => (⟪b i, (B * rho.1) (b i)⟫_ℂ).re)
    (trace (B * rho.1) htc).re at hh
  simpa only [hdiag, regularizedEnergy, TraceClass.tracePairing_apply, B] using hh

private theorem tsum_iSup_of_monotone {ι : Type*} (f : ℕ → ι → ℝ≥0∞)
    (hf : ∀ i, Monotone (fun n => f n i)) :
    (∑' i, ⨆ n, f n i) = ⨆ n, ∑' i, f n i := by
  classical
  have hfinite (s : Finset ι) : (∑ i ∈ s, ⨆ n, f n i) = ⨆ n, ∑ i ∈ s, f n i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs =>
      simp only [Finset.sum_insert hi, hs]
      exact ENNReal.iSup_add_iSup_of_monotone (hf i)
        (fun m n h => Finset.sum_le_sum fun j _ => hf j h)
  simp_rw [ENNReal.tsum_eq_iSup_sum, hfinite]
  exact iSup_comm

/-- The singular series equals the same actual operator regularization supremum.
The basis may have an arbitrary index and includes the entire zero eigenspace. -/
theorem spectralSeries_eq_regularizedSupremum (T : Reference H) {w : Set H}
    (b : HilbertBasis w ℂ H) (s : w → ℝ) (hs : ∀ i, 0 ≤ s i)
    (heigen : ∀ i, T.1.1 (b i) = (s i : ℂ) • b i)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    spectralSeries b s rho = regularizedSupremum T rho := by
  have hbound := spectral_value_le_one T b s heigen
  have heq (i : w) : ENNReal.ofReal (diagonal b rho i) * singularLog (s i) =
      ⨆ n, ENNReal.ofReal (diagonal b rho i * scalarRegularization n (s i)) := by
    rw [← scalarRegularization_iSup (hs i) (hbound i), ENNReal.mul_iSup]
    congr 1
    funext n
    exact (ENNReal.ofReal_mul (diagonal_nonneg b rho hrho i)).symm
  unfold spectralSeries
  simp_rw [heq]
  rw [tsum_iSup_of_monotone _ (fun i m n h => by
    dsimp only
    rw [ENNReal.ofReal_mul (diagonal_nonneg b rho hrho i),
      ENNReal.ofReal_mul (diagonal_nonneg b rho hrho i)]
    exact mul_le_mul_right (scalarRegularization_monotone (hs i) (hbound i) h) _)]
  congr 1
  funext n
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (diagonal_nonneg b rho hrho i)
    (scalarRegularization_nonneg (hs i) (hbound i) n)) (regularizedEnergy_hasSum T b s heigen rho n).summable,
    (regularizedEnergy_hasSum T b s heigen rho n).tsum_eq]

/-- Spectral data for the actual operator, with a complete native basis and its zero fibers. -/
structure SpectralResolution (T : Reference H) where
  index : Set H
  basis : HilbertBasis index ℂ H
  values : index → ℝ
  nonneg : ∀ i, 0 ≤ values i
  eigen : ∀ i, T.1.1 (basis i) = (values i : ℂ) • basis i

/-- The resolution is constructed by the native positive trace-class spectral theorem. -/
def nativeResolution (T : Reference H) : SpectralResolution T := by
  classical
  exact Classical.choice (show Nonempty (SpectralResolution T) from by
    obtain ⟨w, b, s, hs, heigen, _⟩ := TraceClassSpectral.exists_nonneg_trace_spectral_data
      T.2.1 (TraceClass.isTraceClass_coe T.1)
    exact ⟨⟨w, b, s, hs, heigen⟩⟩)

/-- Singular energy is an actual eigenvalue series on the supplied complete native basis. -/
def spectralEnergy (T : Reference H) (rho : TraceClass H) : ℝ≥0∞ :=
  spectralSeries (nativeResolution T).basis (nativeResolution T).values rho

/-- The actual native spectral energy is the already defined operator supremum. -/
theorem spectralEnergy_eq_regularizedSupremum (T : Reference H) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) : spectralEnergy T rho = regularizedSupremum T rho :=
  spectralSeries_eq_regularizedSupremum T (nativeResolution T).basis
    (nativeResolution T).values (nativeResolution T).nonneg (nativeResolution T).eigen rho hrho

/-- The explicit series is independent of the chosen full spectral basis. -/
theorem spectralSeries_eq_spectralEnergy (T : Reference H) {w : Set H}
    (b : HilbertBasis w ℂ H) (s : w → ℝ) (hs : ∀ i, 0 ≤ s i)
    (heigen : ∀ i, T.1.1 (b i) = (s i : ℂ) • b i)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    spectralSeries b s rho = spectralEnergy T rho := by
  rw [spectralSeries_eq_regularizedSupremum T b s hs heigen rho hrho,
    spectralEnergy_eq_regularizedSupremum T rho hrho]

/-- Genuine singular energy reverses noncommuting reference order. -/
theorem spectralEnergy_antitone (P Q : Reference H) (hPQ : P.1.1 ≤ Q.1.1)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) : spectralEnergy Q rho ≤ spectralEnergy P rho := by
  rw [spectralEnergy_eq_regularizedSupremum Q rho hrho,
    spectralEnergy_eq_regularizedSupremum P rho hrho]
  exact regularizedSupremum_antitone P Q hPQ rho hrho

/-- Reference trace-norm lower semicontinuity for the identified singular energy. -/
theorem lowerSemicontinuous_spectralEnergy (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    LowerSemicontinuous (fun T : Reference H => spectralEnergy T rho) := by
  simpa only [spectralEnergy_eq_regularizedSupremum _ rho hrho] using
    lowerSemicontinuous_regularizedSupremum (H := H) rho

/-- Arbitrary two-term nonnegative first-slot linearity includes zero coefficients. -/
theorem spectralEnergy_nonneg_linear (T : Reference H) (rho gamma : TraceClass H)
    (hrho : 0 ≤ rho.1) (hgamma : 0 ≤ gamma.1) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    spectralEnergy T ((a : ℂ) • rho + (b : ℂ) • gamma) =
      ENNReal.ofReal a * spectralEnergy T rho + ENNReal.ofReal b * spectralEnergy T gamma := by
  have hmix : 0 ≤ (((a : ℂ) • rho + (b : ℂ) • gamma : TraceClass H).1) := by
    change 0 ≤ (a : ℂ) • rho.1 + (b : ℂ) • gamma.1
    rw [Complex.coe_smul, Complex.coe_smul]
    exact add_nonneg (smul_nonneg ha hrho) (smul_nonneg hb hgamma)
  simp only [spectralEnergy_eq_regularizedSupremum _ _ hmix,
    spectralEnergy_eq_regularizedSupremum _ rho hrho,
    spectralEnergy_eq_regularizedSupremum _ gamma hgamma]
  exact regularizedSupremum_nonneg_linear T rho gamma hrho hgamma a b ha hb

/-- Singular scaling has the actual unnormalized trace mass. -/
theorem spectralEnergy_scaleReference (T : Reference H) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) :
    spectralEnergy (scaleReference T w hw hw1) rho = spectralEnergy T rho +
      ENNReal.ofReal (trace rho.1 (TraceClass.isTraceClass_coe rho)).re *
        ENNReal.ofReal (-Real.log w) := by
  simp only [spectralEnergy_eq_regularizedSupremum _ rho hrho]
  exact regularizedSupremum_scaleReference T rho hrho w hw hw1

/-- Entropy is the separate nonnegative eigenvalue series, with eta(0)=0. -/
def spectralEntropy (rho : Reference H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (-(nativeResolution rho).values i * Real.log ((nativeResolution rho).values i))

/-- Self energy equals the actual eigenvalue entropy series, including the singular fibers. -/
theorem spectralEnergy_self (rho : Reference H) : spectralEnergy rho rho.1 = spectralEntropy rho := by
  unfold spectralEnergy spectralSeries spectralEntropy
  apply tsum_congr
  intro i
  have he := (nativeResolution rho).eigen i
  have hdiag : diagonal (nativeResolution rho).basis rho.1 i = (nativeResolution rho).values i := by
    unfold diagonal
    rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K,
      (nativeResolution rho).basis.orthonormal.1 i]
    simp
  rw [hdiag]
  by_cases hz : (nativeResolution rho).values i = 0
  · simp [singularLog, hz]
  · rw [singularLog, if_neg hz, ← ENNReal.ofReal_mul ((nativeResolution rho).nonneg i)]
    congr 1
    ring

/-- Noncommuting domination by a positive normalized state gives the logarithmic entropy bound. -/
theorem spectralEnergy_le_entropy_add (rho : TraceClass H) (hrho : 0 ≤ rho.1)
    (htrace : (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1)
    (tau : Reference H) (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hdom : (w : ℂ) • rho.1 ≤ tau.1.1) :
    spectralEnergy tau rho ≤
      spectralEntropy (⟨rho, hrho, density_le_one rho hrho htrace⟩ : Reference H) +
        ENNReal.ofReal (-Real.log w) := by
  let r : Reference H := ⟨rho, hrho, density_le_one rho hrho htrace⟩
  have h := spectralEnergy_antitone (scaleReference r w hw hw1) tau hdom rho hrho
  rw [spectralEnergy_scaleReference r rho hrho w hw hw1, htrace,
    ENNReal.ofReal_one, one_mul] at h
  exact h.trans_eq (congrArg (fun z => z + ENNReal.ofReal (-Real.log w))
    (spectralEnergy_self r))

/-- Finite actual entropy implies finite cross energy under the same domination hypotheses. -/
theorem spectralEnergy_lt_top_of_entropy_lt_top (rho : TraceClass H) (hrho : 0 ≤ rho.1)
    (htrace : (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1)
    (tau : Reference H) (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hdom : (w : ℂ) • rho.1 ≤ tau.1.1)
    (hS : spectralEntropy (⟨rho, hrho, density_le_one rho hrho htrace⟩ : Reference H) < ∞) :
    spectralEnergy tau rho < ∞ :=
  (spectralEnergy_le_entropy_add rho hrho htrace tau w hw hw1 hdom).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hS, ENNReal.ofReal_lt_top⟩)

end QuantumLogEnergy
