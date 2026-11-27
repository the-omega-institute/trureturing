/- GID: D5/S3/Quantum/Measurement/Sensitivity/PovmSensitivityDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Sensitivity/PovmSensitivityDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: BKM sensitivity loss for both relative entropy readouts of a prescribed POVM. -/

import D5.S3.Divergence.ClassicalDPI
import D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic
import D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMeasurementBKM
import D5.S3.Quantum.ProcessReconstruction.LiuWildProductProbes
import D5.S3.Weil.ZetaLinear.RankTrace

/-!
# Four-term BKM sensitivity loss for a finite POVM

The readout is the Born distribution of a prescribed POVM at a faithful state.
The decomposition applies to a real outcome score and specializes to both
orientations of finite relative entropy on the affine Born curve.
The reverse orientation includes a reference supported on a single outcome,
as in the setting of Céleri–Soares-Pinto, arXiv:2611.34788v1, Eq. (14).
-/

noncomputable section

namespace D5.S3.Quantum.Measurement.Sensitivity.PovmSensitivityDefect

set_option autoImplicit false

open _root_.Matrix
open scoped BigOperators ComplexOrder _root_.Matrix MatrixOrder Matrix.Norms.L2Operator
  InnerProductSpace
open D5.S3.Divergence.ClassicalDPI (klDivergence)
open D5.S3.Divergence.LogDerivTrace (logDeriv)
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow (trace_hermitian_product_real)
open D5.S3.Quantum.Recovery.BKMActualMetricCoordinates
  (bkmInner metricCoordinates metricCoordinates_inner)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (omega)
open UnitaryReconstruction.LiuWildProductProbes (FinitePOVM bornMass sum_bornMass)
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic (square_variance_identity)

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

local notation "Mat" => Matrix n n ℂ

/-- The classical Fisher score along the tangent, on outcomes of positive mass. -/
def fisherScore (E : FinitePOVM n ι) (ρ X : Mat) (i : ι) : ℝ :=
  bornMass E X i / bornMass E ρ i

/-- The operator obtained by weighting the POVM effects by a real outcome score. -/
def scoreObservable (E : FinitePOVM n ι) (a : ι → ℝ) : Mat :=
  ∑ i, a i • E.effect i

/-- The squared BKM distance from the logarithmic tangent to the score observable. -/
def metricResidual (ρ X B : Mat) : ℝ :=
  (bkmInner ρ (logDeriv ρ X - B) (logDeriv ρ X - B)).re

/-- The difference between the ordinary and logarithmic-mean second moments. -/
def logMeanGap (ρ B : Mat) : ℝ :=
  (ρ * B * B).trace.re - (bkmInner ρ B B).re

/-- The sum of the positive sandwiches measuring the POVM's score dispersion. -/
def measurementResidual (E : FinitePOVM n ι) (ρ : Mat) (a : ι → ℝ) : ℝ :=
  let B := scoreObservable E a
  ∑ i, (ρ * ((B - a i • (1 : Mat)) * E.effect i * (B - a i • (1 : Mat)))).trace.re

/-- The second moment of the readout score, its variance when centered. -/
def scoreVariance (p z : ι → ℝ) : ℝ :=
  ∑ i, p i * (z i) ^ 2

/-- The directional pairing of the Fisher score with the readout score. -/
def scoreSlope (p a z : ι → ℝ) : ℝ :=
  ∑ i, p i * a i * z i

/-- The squared residual after projecting the Fisher score onto the readout score. -/
def outcomeResidual (p a z : ι → ℝ) (slope : ℝ) : ℝ :=
  ∑ i, p i * (a i - (slope / scoreVariance p z) * z i) ^ 2

/-- Exact loss and positivity for the four successive defects of the sensitivity bound. -/
structure SensitivityDecomposition
    (E : FinitePOVM n ι) (ρ X : Mat) (z : ι → ℝ) (slope : ℝ) : Prop where
  identity :
    let p := bornMass E ρ
    let a := fisherScore E ρ X
    let B := scoreObservable E a
    (X * logDeriv ρ X).trace.re - slope ^ 2 / scoreVariance p z =
      metricResidual ρ X B + logMeanGap ρ B +
        measurementResidual E ρ a + outcomeResidual p a z slope
  metric_nonneg : 0 ≤ metricResidual ρ X (scoreObservable E (fisherScore E ρ X))
  commutator_bound :
    let B := scoreObservable E (fisherScore E ρ X)
    RHLinalg.frobSq (CFC.sqrt ρ * B - B * CFC.sqrt ρ) / 3 ≤ logMeanGap ρ B
  logMean_nonneg : 0 ≤ logMeanGap ρ (scoreObservable E (fisherScore E ρ X))
  measurement_nonneg : 0 ≤ measurementResidual E ρ (fisherScore E ρ X)
  outcome_nonneg : 0 ≤ outcomeResidual (bornMass E ρ) (fisherScore E ρ X) z slope
  stationary_of_zero_variance : scoreVariance (bornMass E ρ) z = 0 → slope = 0

private theorem scoreObservable_isHermitian (E : FinitePOVM n ι) (a : ι → ℝ) :
    (scoreObservable E a).IsHermitian := by
  classical
  change (∑ i, a i • E.effect i)ᴴ = ∑ i, a i • E.effect i
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact ((E.positive i).isHermitian.smul (IsSelfAdjoint.all (a i))).eq

omit [DecidableEq n] in
private theorem trace_real_mul_sum (A : Mat) (Y : ι → Mat) :
    (A * (∑ i, Y i)).trace.re = ∑ i, (A * Y i).trace.re := by
  rw [Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]

omit [DecidableEq n] in
private theorem trace_real_mul_smul (A Y : Mat) (c : ℝ) :
    (A * (c • Y)).trace.re = c * (A * Y).trace.re := by
  rw [mul_smul_comm, Matrix.trace_smul]
  change ((c : ℂ) * (A * Y).trace).re = _
  simp [Complex.mul_re]

private theorem mass_mul_fisherScore (E : FinitePOVM n ι) (ρ X : Mat)
    (hp : ∀ i, 0 < bornMass E ρ i) (i : ι) :
    bornMass E ρ i * fisherScore E ρ X i = bornMass E X i := by
  unfold fisherScore
  field_simp [(hp i).ne']

private theorem fisher_pair (E : FinitePOVM n ι) (ρ X : Mat) (hX : X.IsHermitian)
    (hp : ∀ i, 0 < bornMass E ρ i) :
    let a := fisherScore E ρ X
    (X * scoreObservable E a).trace =
      (↑(∑ i, bornMass E ρ i * (a i) ^ 2) : ℂ) := by
  classical
  dsimp only
  apply Complex.ext
  · rw [Complex.ofReal_re]
    unfold scoreObservable
    rw [trace_real_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [trace_real_mul_smul, Matrix.trace_mul_comm X (E.effect i)]
    change fisherScore E ρ X i * bornMass E X i =
      bornMass E ρ i * (fisherScore E ρ X i) ^ 2
    rw [← mass_mul_fisherScore E ρ X hp i]
    ring
  · rw [Complex.ofReal_im]
    exact trace_hermitian_product_real _ _ hX (scoreObservable_isHermitian E _)

private theorem metricResidual_expand (ρ X B : Mat) (hρ : ρ.PosDef)
    (hX : X.IsHermitian) (hB : B.IsHermitian) :
    0 ≤ metricResidual ρ X B ∧
      metricResidual ρ X B =
        (X * logDeriv ρ X).trace.re - 2 * (X * B).trace.re + (bkmInner ρ B B).re := by
  let L := logDeriv ρ X
  let J := metricCoordinates ρ hρ
  have hpair (A C : Mat) : inner ℂ (J A) (J C) = bkmInner ρ A C :=
    metricCoordinates_inner ρ hρ A C
  have hBL : (inner ℂ (J B) (J L)).re = (X * B).trace.re := by
    rw [hpair, bkmInner, AnchorMeasurement.omega_logDeriv hρ, hB.eq, Matrix.trace_mul_comm]
  have hLB : (inner ℂ (J L) (J B)).re = (X * B).trace.re := by
    rw [← inner_conj_symm (J L) (J B)]
    simpa only [Complex.star_def, Complex.conj_re] using hBL
  have hLL : (inner ℂ (J L) (J L)).re = (X * L).trace.re := by
    rw [hpair, bkmInner, AnchorMeasurement.omega_logDeriv hρ]
    have hstar : (Lᴴ * X).trace = star ((X * L).trace) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX.eq]
    rw [hstar, Complex.star_def, Complex.conj_re]
  have hnorm : metricResidual ρ X B = ‖J (L - B)‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hpair] <;> rfl
  refine ⟨by rw [hnorm]; exact sq_nonneg _, ?_⟩
  rw [hnorm, map_sub, norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [inner_sub_left, inner_sub_right]
  change (inner ℂ (J L) (J L) - inner ℂ (J B) (J L) -
    (inner ℂ (J L) (J B) - inner ℂ (J B) (J B))).re = _
  simp only [Complex.sub_re]
  rw [hLL, hBL, hLB, hpair]
  change (X * L).trace.re - (X * B).trace.re - ((X * B).trace.re - (bkmInner ρ B B).re) =
    (X * L).trace.re - 2 * (X * B).trace.re + (bkmInner ρ B B).re
  ring

private theorem logMeanGap_bound (ρ B : Mat) (hρ : ρ.PosDef) (hB : B.IsHermitian) :
    0 ≤ RHLinalg.frobSq (CFC.sqrt ρ * B - B * CFC.sqrt ρ) / 3 ∧
      RHLinalg.frobSq (CFC.sqrt ρ * B - B * CFC.sqrt ρ) / 3 ≤ logMeanGap ρ B := by
  let S := CFC.sqrt ρ
  let C := S * B - B * S
  have hS : Sᴴ = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ)).star_eq
  have hSS : S * S = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  have h₁ : (B * (S * S) * B).trace = (ρ * B * B).trace := by
    rw [hSS, mul_assoc B ρ B, Matrix.trace_mul_comm B (ρ * B)]
  have h₂ : (S * B * B * S).trace = (ρ * B * B).trace := by
    rw [Matrix.trace_mul_comm (S * B * B) S, ← mul_assoc S (S * B) B,
      ← mul_assoc S S B, hSS]
  have h₃ : (B * S * B * S).trace = (S * B * S * B).trace := by
    rw [Matrix.trace_mul_comm (B * S * B) S]
    simp only [mul_assoc]
  have hC : Cᴴ * C = B * (S * S) * B + S * B * B * S -
      B * S * B * S - S * B * S * B := by
    dsimp only [C]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS, hB.eq]
    noncomm_ring
  have hnorm : RHLinalg.frobSq C =
      2 * ((ρ * B * B).trace.re - (S * B * S * B).trace.re) := by
    change (Cᴴ * C).trace.re = _
    rw [hC]
    simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, h₁, h₂, h₃]
    ring
  have hpos : 0 ≤ RHLinalg.frobSq C :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self C).trace_nonneg).1
  have hsimpson := AnchorMeasurement.omega_le_simpson hρ B hB
  change (B * omega ρ B).trace.re ≤
    (ρ * B * B).trace.re / 3 + 2 * (S * B * S * B).trace.re / 3 at hsimpson
  change 0 ≤ RHLinalg.frobSq C / 3 ∧ RHLinalg.frobSq C / 3 ≤ logMeanGap ρ B
  refine ⟨div_nonneg hpos (by norm_num), ?_⟩
  rw [hnorm, logMeanGap, bkmInner, hB.eq]
  linarith only [hsimpson]

private theorem measurementResidual_expand (E : FinitePOVM n ι) (ρ : Mat)
    (hρ : ρ.PosSemidef) (a : ι → ℝ) :
    0 ≤ measurementResidual E ρ a ∧
      measurementResidual E ρ a =
        (∑ i, bornMass E ρ i * (a i) ^ 2) -
          (ρ * scoreObservable E a * scoreObservable E a).trace.re := by
  classical
  let B := scoreObservable E a
  let D (i : ι) : Mat := B - a i • (1 : Mat)
  have hB : B.IsHermitian := scoreObservable_isHermitian E a
  have hD (i : ι) : (D i).IsHermitian :=
    hB.sub ((Matrix.isHermitian_one : (1 : Mat).IsHermitian).smul (IsSelfAdjoint.all (a i)))
  change 0 ≤ ∑ i, (ρ * (D i * E.effect i * D i)).trace.re ∧
    (∑ i, (ρ * (D i * E.effect i * D i)).trace.re) =
      (∑ i, bornMass E ρ i * (a i) ^ 2) - (ρ * B * B).trace.re
  constructor
  · apply Finset.sum_nonneg
    intro i _
    have h := (E.positive i).conjTranspose_mul_mul_same (D i)
    rw [(hD i).eq] at h
    exact RHLinalg.trace_mul_nonneg_of_posSemidef hρ h
  have hsum : (∑ i, D i * E.effect i * D i) =
      (∑ i, (a i) ^ 2 • E.effect i) - B * B := by
    have h := square_variance_identity E.effect a E.complete
    change (∑ i, (a i • (1 : Mat) - B) * E.effect i * (a i • (1 : Mat) - B)) =
      (∑ i, (a i) ^ 2 • E.effect i) - B * B at h
    have hneg (i : ι) : a i • (1 : Mat) - B = -(D i) := by
      change a i • (1 : Mat) - B = -(B - a i • (1 : Mat))
      rw [neg_sub]
    simpa only [hneg, neg_mul, mul_neg, neg_neg] using h
  rw [← trace_real_mul_sum, hsum, mul_sub, Matrix.trace_sub, Complex.sub_re,
    ← mul_assoc ρ B B, trace_real_mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_real_mul_smul, Matrix.trace_mul_comm ρ (E.effect i)]
  exact mul_comm ((a i) ^ 2) (bornMass E ρ i)

private theorem scoreSlope_eq_zero_of_variance_eq_zero (p a z : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hV : scoreVariance p z = 0) : scoreSlope p a z = 0 := by
  classical
  have hsum : ∑ i, p i * (z i) ^ 2 = 0 := hV
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hp i).le (sq_nonneg (z i)))).mp hsum
  have hz (i : ι) : z i = 0 := by
    have hi : (z i) ^ 2 = 0 :=
      (mul_eq_zero.mp (hterm i (Finset.mem_univ i))).resolve_left (hp i).ne'
    simpa only [pow_two, mul_self_eq_zero] using hi
  simp [scoreSlope, hz]

private theorem outcomeResidual_expand (p a z : ι → ℝ) (hp : ∀ i, 0 < p i) :
    outcomeResidual p a z (scoreSlope p a z) =
      (∑ i, p i * (a i) ^ 2) - (scoreSlope p a z) ^ 2 / scoreVariance p z := by
  by_cases hV : scoreVariance p z = 0
  · have hr := scoreSlope_eq_zero_of_variance_eq_zero p a z hp hV
    simp [outcomeResidual, hr]
  let r := scoreSlope p a z
  let V := scoreVariance p z
  have hterm (i : ι) : p i * (a i - (r / V) * z i) ^ 2 =
      p i * (a i) ^ 2 - (2 * (r / V)) * (p i * a i * z i) +
        (r / V) ^ 2 * (p i * (z i) ^ 2) := by ring
  change (∑ i, p i * (a i - (r / V) * z i) ^ 2) = (∑ i, p i * (a i) ^ 2) - r ^ 2 / V
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (∑ i, p i * (a i) ^ 2) - (2 * (r / V)) * r + (r / V) ^ 2 * V =
    (∑ i, p i * (a i) ^ 2) - r ^ 2 / V
  have hVne : V ≠ 0 := hV
  field_simp [hVne]
  ring

/-- The exact four-term sensitivity loss for a finite POVM and a readout score.
At zero second moment the slope and the normalized sensitivity term are zero. -/
theorem sensitivity_decomposition (E : FinitePOVM n ι) (ρ X : Mat)
    (hρ : ρ.PosDef) (hX : X.IsHermitian) (hp : ∀ i, 0 < bornMass E ρ i)
    (z : ι → ℝ) :
    SensitivityDecomposition E ρ X z (scoreSlope (bornMass E ρ) (fisherScore E ρ X) z) := by
  let p := bornMass E ρ
  let a := fisherScore E ρ X
  let B := scoreObservable E a
  let F := ∑ i, p i * (a i) ^ 2
  have hB : B.IsHermitian := scoreObservable_isHermitian E a
  have hpair : (X * B).trace.re = F := by
    have h : (X * B).trace = (F : ℂ) := fisher_pair E ρ X hX hp
    rw [h, Complex.ofReal_re]
  obtain ⟨hmetric, hmetric_eq⟩ := metricResidual_expand ρ X B hρ hX hB
  obtain ⟨hcomm_nonneg, hcomm⟩ := logMeanGap_bound ρ B hρ hB
  obtain ⟨hmeasure, hmeasure_eq⟩ := measurementResidual_expand E ρ hρ.posSemidef a
  have houtcome : 0 ≤ outcomeResidual p a z (scoreSlope p a z) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i).le (sq_nonneg _)
  refine ⟨?_, hmetric, hcomm, hcomm_nonneg.trans hcomm, hmeasure, houtcome,
    scoreSlope_eq_zero_of_variance_eq_zero p a z hp⟩
  change (X * logDeriv ρ X).trace.re - (scoreSlope p a z) ^ 2 / scoreVariance p z =
    metricResidual ρ X B + logMeanGap ρ B + measurementResidual E ρ a +
      outcomeResidual p a z (scoreSlope p a z)
  rw [hmetric_eq, hpair, logMeanGap, hmeasure_eq, outcomeResidual_expand p a z hp]
  change (X * logDeriv ρ X).trace.re - (scoreSlope p a z) ^ 2 / scoreVariance p z =
    (X * logDeriv ρ X).trace.re - 2 * F + (bkmInner ρ B B).re +
      ((ρ * B * B).trace.re - (bkmInner ρ B B).re) +
      (F - (ρ * B * B).trace.re) + (F - (scoreSlope p a z) ^ 2 / scoreVariance p z)
  ring

/-- Centered score for the readout `D(q‖p)`, including zero entries of `q`. -/
def reverseScore (p q : ι → ℝ) (i : ι) : ℝ :=
  1 - q i / p i

/-- Centered score for the readout `D(p‖q)`. -/
def forwardScore (p q : ι → ℝ) (i : ι) : ℝ :=
  Real.log (p i / q i) - klDivergence p q

private theorem bornMass_add_smul (E : FinitePOVM n ι) (ρ X : Mat) (t : ℝ) (i : ι) :
    bornMass E (ρ + t • X) i = bornMass E ρ i + t * bornMass E X i := by
  unfold bornMass
  rw [mul_add, Matrix.trace_add, Complex.add_re, trace_real_mul_smul]

private theorem hasDerivAt_bornMass (E : FinitePOVM n ι) (ρ X : Mat) (i : ι) :
    HasDerivAt (fun t : ℝ => bornMass E (ρ + t • X) i) (bornMass E X i) 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (bornMass E X i)).const_add
    (bornMass E ρ i)
  simpa only [one_mul, bornMass_add_smul] using h

private theorem sum_bornTangent_eq_zero (E : FinitePOVM n ι) (X : Mat)
    (hXtrace : X.trace = 0) : ∑ i, bornMass E X i = 0 := by
  rw [sum_bornMass, hXtrace, Complex.zero_re]

/-- The affine Born curve for reverse KL has precisely the score-pairing
derivative, and the four-term identity uses that derivative. A zero reference
component contributes the constant zero to the KL sum. -/
theorem reverseKL_decomposition (E : FinitePOVM n ι) (ρ X : Mat)
    (hρ : ρ.PosDef) (hρtrace : ρ.trace = 1) (hX : X.IsHermitian) (hXtrace : X.trace = 0)
    (hp : ∀ i, 0 < bornMass E ρ i) (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hqsum : ∑ i, q i = 1) :
    let p := bornMass E ρ
    let z := reverseScore p q
    let R := fun t : ℝ => klDivergence q (bornMass E (ρ + t • X))
    (∑ i, p i * z i) = 0 ∧
      HasDerivAt R (scoreSlope p (fisherScore E ρ X) z) 0 ∧
      SensitivityDecomposition E ρ X z (deriv R 0) := by
  classical
  dsimp only
  let p := bornMass E ρ
  let v := bornMass E X
  let z := reverseScore p q
  have hv : ∑ i, v i = 0 := sum_bornTangent_eq_zero E X hXtrace
  have hpsum : ∑ i, p i = 1 := by
    change ∑ i, bornMass E ρ i = 1
    rw [sum_bornMass, hρtrace, Complex.one_re]
  have hcenter : ∑ i, p i * z i = 0 := by
    have he (i : ι) : p i * z i = p i - q i := by
      have hpi : p i ≠ 0 := (hp i).ne'
      change p i * (1 - q i / p i) = p i - q i
      field_simp [hpi]
    simp only [he, Finset.sum_sub_distrib, hpsum, hqsum, sub_self]
  have hterm (i : ι) :
      HasDerivAt (fun t : ℝ => q i * Real.log (q i / bornMass E (ρ + t • X) i))
        (-(q i * (v i / p i))) 0 := by
    by_cases hqi : q i = 0
    · simpa only [hqi, zero_mul, neg_zero] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hqpos := lt_of_le_of_ne (hq i) (Ne.symm hqi)
      have hbase : bornMass E (ρ + (0 : ℝ) • X) i = p i := by
        simp only [zero_smul, add_zero, p]
      have hpi : p i ≠ 0 := (hp i).ne'
      have hden : bornMass E (ρ + (0 : ℝ) • X) i ≠ 0 := by
        rw [hbase]
        exact hpi
      have hquot := (hasDerivAt_const (0 : ℝ) (q i)).fun_div
        (hasDerivAt_bornMass E ρ X i) hden
      have hprod := (hquot.log (div_ne_zero hqpos.ne' hden)).const_mul (q i)
      convert hprod using 1
      simp only [hbase, zero_mul, zero_sub]
      change -(q i * (v i / p i)) = q i * ((-(q i * v i) / (p i) ^ 2) / (q i / p i))
      field_simp [hpi, hqi]
  have hcoeff : scoreSlope p (fisherScore E ρ X) z = ∑ i, -(q i * (v i / p i)) := by
    have he (i : ι) : p i * fisherScore E ρ X i * z i = v i + -(q i * (v i / p i)) := by
      rw [show p i * fisherScore E ρ X i = v i from mass_mul_fisherScore E ρ X hp i]
      change v i * (1 - q i / p i) = v i + -(q i * (v i / p i))
      ring
    simp only [scoreSlope, he, Finset.sum_add_distrib, hv, zero_add]
  have hd : HasDerivAt (fun t : ℝ => klDivergence q (bornMass E (ρ + t • X)))
      (scoreSlope p (fisherScore E ρ X) z) 0 := by
    simp only [hcoeff, klDivergence]
    exact HasDerivAt.fun_sum fun i _ => hterm i
  refine ⟨hcenter, hd, ?_⟩
  rw [hd.deriv]
  exact sensitivity_decomposition E ρ X hρ hX hp z

/-- The affine Born curve for forward KL has the centered log-ratio derivative,
and the four-term identity uses that derivative. Both distributions are positive. -/
theorem forwardKL_decomposition (E : FinitePOVM n ι) (ρ X : Mat)
    (hρ : ρ.PosDef) (hρtrace : ρ.trace = 1) (hX : X.IsHermitian) (hXtrace : X.trace = 0)
    (hp : ∀ i, 0 < bornMass E ρ i) (q : ι → ℝ)
    (hq : (∀ i, 0 < q i) ∧ ∑ i, q i = 1) :
    let p := bornMass E ρ
    let z := forwardScore p q
    let R := fun t : ℝ => klDivergence (bornMass E (ρ + t • X)) q
    (∑ i, p i * z i) = 0 ∧
      HasDerivAt R (scoreSlope p (fisherScore E ρ X) z) 0 ∧
      SensitivityDecomposition E ρ X z (deriv R 0) := by
  classical
  dsimp only
  let p := bornMass E ρ
  let v := bornMass E X
  let z := forwardScore p q
  have hv : ∑ i, v i = 0 := sum_bornTangent_eq_zero E X hXtrace
  have hpsum : ∑ i, p i = 1 := by
    change ∑ i, bornMass E ρ i = 1
    rw [sum_bornMass, hρtrace, Complex.one_re]
  have hcenter : ∑ i, p i * z i = 0 := by
    change (∑ i, p i * (Real.log (p i / q i) - klDivergence p q)) = 0
    rw [show (∑ i, p i * (Real.log (p i / q i) - klDivergence p q)) =
        klDivergence p q - (∑ i, p i * klDivergence p q) by
      simp only [mul_sub, Finset.sum_sub_distrib, klDivergence]]
    rw [← Finset.sum_mul, hpsum, one_mul, sub_self]
  have hterm (i : ι) :
      HasDerivAt (fun t : ℝ => bornMass E (ρ + t • X) i *
        Real.log (bornMass E (ρ + t • X) i / q i))
        (v i * (Real.log (p i / q i) + 1)) 0 := by
    have hbase : bornMass E (ρ + (0 : ℝ) • X) i = p i := by
      simp only [zero_smul, add_zero, p]
    have hpi : p i ≠ 0 := (hp i).ne'
    have hqi : q i ≠ 0 := (hq.1 i).ne'
    have hden : bornMass E (ρ + (0 : ℝ) • X) i ≠ 0 := by
      rw [hbase]
      exact hpi
    have hline := hasDerivAt_bornMass E ρ X i
    have hprod := hline.fun_mul ((hline.div_const (q i)).log (div_ne_zero hden hqi))
    convert hprod using 1
    simp only [hbase]
    change v i * (Real.log (p i / q i) + 1) =
      v i * Real.log (p i / q i) + p i * ((v i / q i) / (p i / q i))
    field_simp [hpi, hqi]
  have hcoeff : scoreSlope p (fisherScore E ρ X) z =
      ∑ i, v i * (Real.log (p i / q i) + 1) := by
    have he (i : ι) : p i * fisherScore E ρ X i * z i =
        v i * (Real.log (p i / q i) + 1) - v i * (klDivergence p q + 1) := by
      rw [show p i * fisherScore E ρ X i = v i from mass_mul_fisherScore E ρ X hp i]
      change v i * (Real.log (p i / q i) - klDivergence p q) = _
      ring
    simp only [scoreSlope, he, Finset.sum_sub_distrib, ← Finset.sum_mul, hv, zero_mul, sub_zero]
  have hd : HasDerivAt (fun t : ℝ => klDivergence (bornMass E (ρ + t • X)) q)
      (scoreSlope p (fisherScore E ρ X) z) 0 := by
    simp only [hcoeff, klDivergence]
    exact HasDerivAt.fun_sum fun i _ => hterm i
  refine ⟨hcenter, hd, ?_⟩
  rw [hd.deriv]
  exact sensitivity_decomposition E ρ X hρ hX hp z

end D5.S3.Quantum.Measurement.Sensitivity.PovmSensitivityDefect
