/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/TwoMeanBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/TwoMeanBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual noisy-GHZ TwoMeanBound in the original finite-ensemble semantics. -/


import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.Foundations


open scoped BigOperators ComplexOrder MatrixOrder
open _root_.Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word)
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation (IsUnitState)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)
open D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof

noncomputable section

/-- Finite positive metrics, including the affine certificate family. -/
def metric (n d : ℕ) (a b : ℝ) :
    Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  a • rankOneDensity (ghz n d) +
    b • (supportProjector n d - rankOneDensity (ghz n d)) + complementProjector n d

private def metricInverse (n d : ℕ) (a b : ℝ) :
    Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  a⁻¹ • rankOneDensity (ghz n d) +
    b⁻¹ • (supportProjector n d - rankOneDensity (ghz n d)) + complementProjector n d

private lemma metric_positive {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b) :
    (metric n d a b).PosDef := by
  have he : metric n d a b =
      a • (1 : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) +
      (b - a) • (supportProjector n d - rankOneDensity (ghz n d)) +
      (1 - a) • complementProjector n d := by
    dsimp [metric, complementProjector]
    module
  rw [he]
  exact ((Matrix.PosDef.one.smul ha).add_posSemidef
    ((orthogonal_positive hn hd).1.smul (sub_nonneg.mpr hab))).add_posSemidef
      ((orthogonal_positive hn hd).2.smul (sub_nonneg.mpr ha1))

private lemma metric_inverse {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    metric n d a b * metricInverse n d a b = 1 := by
  classical
  obtain ⟨hpp, hpg, hgp, hgg⟩ := projector_data hn hd
  simp only [metric, metricInverse, complementProjector,
    add_mul, mul_add, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, one_mul, mul_one, hpp, hpg, hgp, hgg]
  match_scalars <;> field_simp <;> ring

private lemma metric_weighted_cs {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b)
    (φ ψ : Word (Fin d) n → ℂ) :
    Complex.normSq (star φ ⬝ᵥ ψ) ≤
      readout (metricInverse n d a b) φ * readout (metric n d a b) ψ := by
  classical
  have hb : 0 < b := ha.trans_le hab
  have hi : (metricInverse n d a b).PosSemidef := by
    exact (((posSemidef_vecMulVec_self_star (ghz n d)).smul
      (inv_nonneg.mpr ha.le)).add
      ((orthogonal_positive hn hd).1.smul (inv_nonneg.mpr hb.le))).add
        (orthogonal_positive hn hd).2
  have hm : metric n d a b *ᵥ (metricInverse n d a b *ᵥ φ) = φ := by
    rw [mulVec_mulVec, metric_inverse hn hd ha.ne' hb.ne', one_mulVec]
  have hr : star (metricInverse n d a b *ᵥ φ) ⬝ᵥ φ =
      star φ ⬝ᵥ metricInverse n d a b *ᵥ φ := by
    rw [star_mulVec, hi.isHermitian.eq, ← dotProduct_mulVec]
  have hc := D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.psd_cauchy_schwarz
    (metric n d a b) (metric_positive hn hd ha ha1 hab).posSemidef
      ψ (metricInverse n d a b *ᵥ φ)
  rw [hm, hr] at hc
  rw [← Complex.normSq_eq_norm_sq,
    D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.normSq_overlap_comm ψ φ] at hc
  simpa only [readout, mul_comm] using hc

lemma expectation_add {n d : ℕ}
    (a c : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ)
    (ψ : Word (Fin d) n → ℂ) : readout (a + c) ψ = readout a ψ + readout c ψ := by
  exact RHLinalg.hermForm_add a c ψ

lemma expectation_sub {n d : ℕ}
    (a c : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ)
    (ψ : Word (Fin d) n → ℂ) : readout (a - c) ψ = readout a ψ - readout c ψ := by
  exact RHLinalg.hermForm_sub a c ψ

lemma expectation_smul {n d : ℕ} (r : ℝ)
    (a : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ)
    (ψ : Word (Fin d) n → ℂ) : readout (r • a) ψ = r * readout a ψ := by
  change (star ψ ⬝ᵥ ((r • a) *ᵥ ψ)).re = r * (star ψ ⬝ᵥ (a *ᵥ ψ)).re
  rw [← Complex.coe_smul r a]
  exact D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.quadratic_smul ψ r a

lemma expectation_one {n d : ℕ} (ψ : Word (Fin d) n → ℂ) :
    readout 1 ψ = ∑ x, Complex.normSq (ψ x) := by
  simpa only [RHLinalg.hermForm, readout, RCLike.re_to_complex,
    Complex.normSq_eq_norm_sq] using RHLinalg.hermForm_one ψ

private lemma metric_inverse_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (he : a⁻¹ + (d - 1 : ℝ) * b⁻¹ = d)
    (φ : Word (Fin d) n → ℂ) (hφ : IsBiseparable φ) :
    readout (metricInverse n d a b) φ ≤ 1 := by
  have hu : readout 1 φ = 1 := by rw [expectation_one]; exact hφ.1
  have h := biseparable_overlap hn hd φ hφ
  have hc : 0 ≤ a⁻¹ - b⁻¹ := sub_nonneg.mpr (inv_anti₀ ha hab)
  have hm := mul_nonneg hc (sub_nonneg.mpr h)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [metricInverse, complementProjector, expectation_add,
    expectation_sub, expectation_smul, hu]
  have he' := congrArg (fun z : ℝ => z * readout (supportProjector n d) φ) he
  nlinarith

lemma pure_metric_lower {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b)
    (he : a⁻¹ + (d - 1 : ℝ) * b⁻¹ = d)
    (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    (1 - b) * readout (supportProjector n d) ψ +
      (b - a) * readout (rankOneDensity (ghz n d)) ψ ≤ geometricMeasurePure ψ := by
  have hn' : 0 < n := by omega
  have hpos : 0 ≤ readout (metric n d a b) ψ :=
    RHLinalg.hermForm_nonneg_of_posSemidef
      (metric_positive hn' hd ha ha1 hab).posSemidef ψ
  have hs : sSup {t : ℝ | ∃ φ, IsBiseparable φ ∧
      t = Complex.normSq (star φ ⬝ᵥ ψ)} ≤ readout (metric n d a b) ψ := by
    apply csSup_le (overlap_values_nonempty hn hd ψ)
    rintro t ⟨φ, hφ, rfl⟩
    exact (metric_weighted_cs hn' hd ha ha1 hab φ ψ).trans
      (mul_le_of_le_one_left hpos (metric_inverse_bound hn' hd ha hab he φ hφ))
  have hu : readout 1 ψ = 1 := by rw [expectation_one]; exact hψ
  simp only [metric, complementProjector, expectation_add,
    expectation_sub, expectation_smul, hu] at hs
  unfold geometricMeasurePure
  linarith

/-- An observable mean in the original complex matrix representation. -/
def observableMean {n d : ℕ}
    (ρ A : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) : ℝ :=
  (trace (ρ * A)).re

lemma trace_average {n d k : ℕ} (p : Fin k → ℝ)
    (ψ : Fin k → Word (Fin d) n → ℂ)
    (A : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    observableMean (∑ i, p i • rankOneDensity (ψ i)) A =
      ∑ i, p i * readout A (ψ i) := by
  classical
  unfold observableMean
  rw [trace_mul_comm]
  have ht := congrArg Complex.re
    (D5.S3.Zeros.CriticalPoints.RankOneTraceBound.trace_rank_one_sum
      (fun i => WithLp.toLp 2 (ψ i)) p (fun _ => 1) A)
  simpa only [mul_one, rankOneDensity, Complex.coe_smul,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, Complex.re_sum, Complex.re_ofReal_mul, readout,
    dotProduct_comm] using ht

/-- The full finite-metric supporting family applies to every actual density
state and the original finite-ensemble roof. Its proof uses nonempty roof and
overlap sets, and the all-cut biseparable inequality. -/
theorem metric_roof_bound {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b)
    (he : a⁻¹ + (d - 1 : ℝ) * b⁻¹ = d)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    (1 - b) * observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) +
      (b - a) * observableMean (CStarMatrix.ofMatrix.symm ρ.1)
        (rankOneDensity (ghz n d)) ≤ geometricMeasure (CStarMatrix.ofMatrix.symm ρ.1) := by
  classical
  apply le_csInf (ensemble_values_nonempty ρ)
  rintro t ⟨k, p, ψ, hp, hs, hu, heρ, rfl⟩
  rw [heρ, trace_average, trace_average]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (pure_metric_lower hn hd ha ha1 hab he (ψ i) (hu i)) (hp i))
  convert h using 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def metricA (d : ℕ) (t : ℝ) : ℝ := (t + d - 1) / (d * t)
def metricB (d : ℕ) (t : ℝ) : ℝ := (t + d - 1) / d

lemma metric_parameters {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (ht : 1 ≤ t) :
    0 < metricA d t ∧ metricA d t ≤ 1 ∧ metricA d t ≤ metricB d t ∧
      (metricA d t)⁻¹ + (d - 1 : ℝ) * (metricB d t)⁻¹ = d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have ht0 : 0 < t := by linarith
  have hsum : 0 < t + d - 1 := by linarith
  have hdt : 0 < (d : ℝ) * t := mul_pos hd0 ht0
  refine ⟨div_pos hsum hdt, (div_le_one hdt).mpr ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd0.le) (sub_nonneg.mpr ht)]
  · unfold metricA metricB
    rw [div_le_div_iff₀ hdt hd0]
    nlinarith [mul_nonneg (mul_nonneg hsum.le hd0.le) (sub_nonneg.mpr ht)]
  · unfold metricA metricB
    rw [inv_div, inv_div]
    field_simp
    <;> ring

/-- All finite supporting lines, parametrized without singular coefficients.
The endpoint where the two means coincide is obtained by their supremum. -/
theorem supporting_line {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d)
    {t : ℝ} (ht : 1 ≤ t)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    (observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) +
      (d - 2 : ℝ) * observableMean (CStarMatrix.ofMatrix.symm ρ.1)
        (rankOneDensity (ghz n d)) -
      t * (observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) -
        observableMean (CStarMatrix.ofMatrix.symm ρ.1) (rankOneDensity (ghz n d))) -
      (d - 1 : ℝ) * observableMean (CStarMatrix.ofMatrix.symm ρ.1)
        (rankOneDensity (ghz n d)) / t) / d ≤
      geometricMeasure (CStarMatrix.ofMatrix.symm ρ.1) := by
  obtain ⟨ha, ha1, hab, he⟩ := metric_parameters hd ht
  have h := metric_roof_bound hn (by omega) ha ha1 hab he ρ
  convert h using 1
  unfold metricA metricB
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
  field_simp
  <;> ring

private lemma mean_add {n d : ℕ}
    (ρ A B : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    observableMean ρ (A + B) = observableMean ρ A + observableMean ρ B := by
  simp [observableMean, mul_add, trace_add]

lemma mean_sub {n d : ℕ}
    (ρ A B : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    observableMean ρ (A - B) = observableMean ρ A - observableMean ρ B := by
  simp [observableMean, mul_sub, trace_sub]

lemma mean_smul {n d : ℕ} (r : ℝ)
    (ρ A : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    observableMean ρ (r • A) = r * observableMean ρ A := by
  simp [observableMean, Matrix.mul_smul, trace_smul, Complex.real_smul]

lemma mean_one {n d : ℕ}
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    observableMean (CStarMatrix.ofMatrix.symm ρ.1) 1 = 1 := by
  have h : trace (CStarMatrix.ofMatrix.symm ρ.1) = 1 := ρ.2.2
  simpa [observableMean] using congrArg Complex.re h

/-- The universal analytic affine certificate, for every density operator,
in the original witness and complementary-projector readouts. -/
theorem affine_certificate {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    -(d - 1 : ℝ) / (d * (d - 2)) *
        observableMean (CStarMatrix.ofMatrix.symm ρ.1) (witnessOp n d) +
      1 / ((d : ℝ)^2 * (d - 2)) *
        observableMean (CStarMatrix.ofMatrix.symm ρ.1) (complementProjector n d) -
      1 / ((d : ℝ)^2 * (d - 2)) ≤
        geometricMeasure (CStarMatrix.ofMatrix.symm ρ.1) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd2 : (d - 2 : ℝ) ≠ 0 := by linarith
  have hd1 : (d - 1 : ℝ) ≠ 0 := by linarith
  have ht : (1 : ℝ) ≤ (d - 1 : ℝ) / (d - 2) := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  have h := supporting_line (by omega : 2 ≤ n) (by omega : 2 ≤ d) ht ρ
  convert h using 1
  simp only [witnessOp, complementProjector, mean_sub, mean_smul, mean_one]
  field_simp [hd0, hd1, hd2]
  <;> ring

/-- The complete two-observable value, with its zero region retained. The
older `twoMeanValue` denotes only the radical branch. -/
def twoMeanOptimum (d : ℕ) (f y : ℝ) : ℝ :=
  if (d : ℝ) * f ≤ y then 0 else twoMeanValue d f y

lemma supporting_envelope {d : ℕ} (hd : 2 ≤ d) {f y E : ℝ}
    (hf : 0 ≤ f) (hfy : f ≤ y) (hE : 0 ≤ E)
    (hline : ∀ t : ℝ, 1 ≤ t →
      (y + (d - 2 : ℝ) * f - t * (y - f) - (d - 1 : ℝ) * f / t) / d ≤ E) :
    twoMeanOptimum d f y ≤ E := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdne : (d : ℝ) ≠ 0 := hdpos.ne'
  unfold twoMeanOptimum
  split_ifs with hlow
  · exact hE
  by_cases heq : f = y
  · subst y
    have hB : twoMeanValue d f f = (d - 1 : ℝ) * f / d := by
      simp only [twoMeanValue, sub_self, mul_zero, Real.sqrt_zero, sub_zero]
      ring
    rw [hB]
    let c : ℝ := (d - 1 : ℝ) * f / d
    change c ≤ E
    by_contra h
    have hδ : 0 < c - E := sub_pos.mpr (lt_of_not_ge h)
    have hc : 0 ≤ c := div_nonneg (mul_nonneg (by linarith) hf) hdpos.le
    let t : ℝ := 1 + c / (c - E)
    have ht : 1 ≤ t := by dsimp [t]; exact le_add_of_nonneg_right (div_nonneg hc hδ.le)
    have htpos : 0 < t := zero_lt_one.trans_le ht
    have hdt : (c - E) * t = (c - E) + c := by
      dsimp [t]
      field_simp
      <;> ring
    have hct : c / t < c - E := (div_lt_iff₀ htpos).mpr (by rw [hdt]; linarith)
    have hb := hline t ht
    have hform :
        (f + (d - 2 : ℝ) * f - t * (f - f) - (d - 1 : ℝ) * f / t) / d = c - c / t := by
      dsimp [c]
      field_simp
      <;> ring
    rw [hform] at hb
    linarith
  · have hlt : f < y := lt_of_le_of_ne hfy heq
    have hfpos : 0 < f := by nlinarith
    let X := Real.sqrt ((d - 1 : ℝ) * f)
    let Y := Real.sqrt (y - f)
    have hX : 0 < X := Real.sqrt_pos.mpr (mul_pos (by linarith) hfpos)
    have hY : 0 < Y := Real.sqrt_pos.mpr (sub_pos.mpr hlt)
    have hXs : X ^ 2 = (d - 1 : ℝ) * f := Real.sq_sqrt (mul_nonneg (by linarith) hf)
    have hYs : Y ^ 2 = y - f := Real.sq_sqrt (sub_nonneg.mpr hfy)
    have hXY : Y ≤ X := by nlinarith
    let t := X / Y
    have ht : 1 ≤ t := (le_div_iff₀ hY).mpr (by simpa using hXY)
    have hfirst : t * (y - f) = X * Y := by
      rw [← hYs]
      dsimp [t]
      field_simp
      <;> ring
    have hsecond : (d - 1 : ℝ) * f / t = X * Y := by
      rw [← hXs]
      dsimp [t]
      field_simp
      <;> ring
    have hroot : Real.sqrt ((d - 1 : ℝ) * f * (y - f)) = X * Y :=
      Real.sqrt_mul (mul_nonneg (by linarith) hf) _
    have hb := hline t ht
    rw [hfirst, hsecond] at hb
    unfold twoMeanValue
    rw [hroot]
    convert hb using 1 <;> ring

private lemma mean_positive {n d : ℕ}
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n))
    (A : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) (hA : A.PosSemidef) :
    0 ≤ observableMean (CStarMatrix.ofMatrix.symm ρ.1) A := by
  classical
  obtain ⟨_, k, p, ψ, hp, hs, hu, he, hv⟩ := ensemble_values_nonempty ρ
  rw [he, trace_average]
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hp i) (RHLinalg.hermForm_nonneg_of_posSemidef hA (ψ i)))

/-- The measured means of every density state lie in the required triangle. -/
theorem means_triangle {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    0 ≤ observableMean (CStarMatrix.ofMatrix.symm ρ.1) (rankOneDensity (ghz n d)) ∧
    observableMean (CStarMatrix.ofMatrix.symm ρ.1) (rankOneDensity (ghz n d)) ≤
      observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) ∧
    observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) ≤ 1 := by
  have hf := mean_positive ρ _ (posSemidef_vecMulVec_self_star (ghz n d))
  have hfy := mean_positive ρ _ (orthogonal_positive hn hd).1
  have hy := mean_positive ρ _ (orthogonal_positive hn hd).2
  simp only [complementProjector, mean_sub, mean_one] at hfy hy
  exact ⟨hf, by linarith, by linarith⟩

/-- The universal two-mean lower bound in actual density and finite-ensemble
semantics, including both coincident means and the complete zero region. -/
theorem two_mean_lower {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    twoMeanOptimum d
      (observableMean (CStarMatrix.ofMatrix.symm ρ.1) (rankOneDensity (ghz n d)))
      (observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d)) ≤
      geometricMeasure (CStarMatrix.ofMatrix.symm ρ.1) := by
  obtain ⟨hf, hfy, _⟩ := means_triangle (by omega : 0 < n) (by omega : 0 < d) ρ
  exact supporting_envelope (by omega) hf hfy (density_measure_nonneg (by omega) (by omega) ρ)
    (fun t ht => supporting_line (by omega) (by omega) ht ρ)

lemma pure_means_triangle {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    0 ≤ readout (rankOneDensity (ghz n d)) ψ ∧
    readout (rankOneDensity (ghz n d)) ψ ≤ readout (supportProjector n d) ψ ∧
    readout (supportProjector n d) ψ ≤ 1 := by
  have hf := RHLinalg.hermForm_nonneg_of_posSemidef
    (posSemidef_vecMulVec_self_star (ghz n d)) ψ
  have hfy := RHLinalg.hermForm_nonneg_of_posSemidef (orthogonal_positive hn hd).1 ψ
  have hy := RHLinalg.hermForm_nonneg_of_posSemidef (orthogonal_positive hn hd).2 ψ
  change 0 ≤ readout (rankOneDensity (ghz n d)) ψ at hf
  change 0 ≤ readout (supportProjector n d - rankOneDensity (ghz n d)) ψ at hfy
  change 0 ≤ readout (complementProjector n d) ψ at hy
  have hu : readout 1 ψ = 1 := by rw [expectation_one]; exact hψ
  simp only [complementProjector, expectation_sub, hu] at hfy hy
  exact ⟨hf, by linarith, by linarith⟩

private lemma pure_supporting_line {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d)
    {t : ℝ} (ht : 1 ≤ t) (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    (readout (supportProjector n d) ψ + (d - 2 : ℝ) *
        readout (rankOneDensity (ghz n d)) ψ -
      t * (readout (supportProjector n d) ψ - readout (rankOneDensity (ghz n d)) ψ) -
      (d - 1 : ℝ) * readout (rankOneDensity (ghz n d)) ψ / t) / d ≤
      geometricMeasurePure ψ := by
  obtain ⟨ha, ha1, hab, he⟩ := metric_parameters hd ht
  have h := pure_metric_lower hn (by omega) ha ha1 hab he ψ hψ
  convert h using 1
  unfold metricA metricB
  field_simp
  <;> ring

/-- The same two-mean bound holds for every normalized pure vector and its
actual supremum over all biseparable cuts. -/
theorem pure_two_mean_lower {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    twoMeanOptimum d (readout (rankOneDensity (ghz n d)) ψ)
      (readout (supportProjector n d) ψ) ≤ geometricMeasurePure ψ := by
  obtain ⟨hf, hfy, _⟩ := pure_means_triangle (by omega : 0 < n) (by omega : 0 < d) ψ hψ
  exact supporting_envelope (by omega) hf hfy (pure_measure_bounds (by omega) (by omega) ψ hψ).1
    (fun t ht => pure_supporting_line (by omega) (by omega) ht ψ hψ)

lemma biseparable_measure_zero {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (φ : Word (Fin d) n → ℂ) (hφ : IsBiseparable φ) : geometricMeasurePure φ = 0 := by
  have hu : star φ ⬝ᵥ φ = 1 :=
    (D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.unit_norm_iff φ).mpr hφ.1
  have hself : (1 : ℝ) ∈ {t : ℝ | ∃ ψ, IsBiseparable ψ ∧
      t = Complex.normSq (star ψ ⬝ᵥ φ)} := by
    refine ⟨φ, hφ, ?_⟩
    simp [hu]
  have hl := le_csSup (overlap_values_bdd φ hφ.1) hself
  have hz := (pure_measure_bounds hn hd φ hφ.1).1
  unfold geometricMeasurePure at *
  linarith

/-- A finite normalized family is an actual competitor in the original roof,
with any finite index type, by explicit reindexing to `Fin`. -/
theorem finite_ensemble_upper {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (ψ : ι → Word (Fin d) n → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hu : ∀ i, IsUnitState (ψ i)) :
    geometricMeasure (∑ i, p i • rankOneDensity (ψ i)) ≤
      ∑ i, p i * geometricMeasurePure (ψ i) := by
  classical
  let e := (Fintype.equivFin ι).symm
  apply csInf_le (ensemble_values_bdd hn hd _)
  refine ⟨Fintype.card ι, p ∘ e, ψ ∘ e, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hp (e i)
  · simpa only [Function.comp_apply, Equiv.sum_comp] using hs
  · exact fun i => hu (e i)
  · exact (Equiv.sum_comp e (fun i => p i • rankOneDensity (ψ i))).symm
  · exact (Equiv.sum_comp e (fun i => p i * geometricMeasurePure (ψ i))).symm

lemma trace_rank_one {n d : ℕ} (ψ : Word (Fin d) n → ℂ) :
    trace (rankOneDensity ψ) = ((∑ x, Complex.normSq (ψ x) : ℝ) : ℂ) := by
  simpa only [rankOneDensity, trace_vecMulVec, dotProduct_comm, Complex.normSq_eq_norm_sq] using
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.dot_star_self ψ

/-- The density operator represented by a concrete normalized finite ensemble. -/
def ensembleDensity {n d : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (ψ : ι → Word (Fin d) n → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hu : ∀ i, IsUnitState (ψ i)) :
    D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n) := by
  classical
  refine ⟨CStarMatrix.ofMatrix (∑ i, p i • rankOneDensity (ψ i)), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact Finset.sum_nonneg (fun i _ =>
      ((posSemidef_vecMulVec_self_star (ψ i)).smul (hp i)).nonneg)
  · change trace (∑ i, p i • rankOneDensity (ψ i)) = 1
    have hu' : ∀ i, ∑ x, Complex.normSq (ψ i x) = 1 := hu
    simp only [trace_sum, trace_smul, trace_rank_one, hu', Complex.real_smul,
      mul_one, ← Complex.ofReal_sum, hs, Complex.ofReal_one]

/-- A concrete biseparable finite ensemble has zero actual convex roof. -/
theorem biseparable_ensemble_zero {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (φ : ι → Word (Fin d) n → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hφ : ∀ i, IsBiseparable (φ i)) :
    geometricMeasure (∑ i, p i • rankOneDensity (φ i)) = 0 := by
  have hl := density_measure_nonneg hn hd (ensembleDensity p φ hp hs (fun i => (hφ i).1))
  have hh := finite_ensemble_upper hn hd p φ hp hs (fun i => (hφ i).1)
  simp only [biseparable_measure_zero hn hd _ (hφ _), mul_zero, Finset.sum_const_zero] at hh
  exact le_antisymm hh hl

end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
