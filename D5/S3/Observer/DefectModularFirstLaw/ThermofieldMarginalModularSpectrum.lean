/- GID: D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum
   generality: I
   mirror-B: D5/B/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The thermofield marginal has the geometric entropy law and modular spacing. -/

import D5.S3.Observer.DefectModularFirstLaw.EntropyDerivativeEqualsModularGap
import D5.S3.Analytic.Zeta.PrimeMarginalEntropy
import D5.S3.Quantum.PureState.PureStateHandshake
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Topology.Instances.Matrix

/- Library-search audit trail (2026-09-05):
   * D5 searches for partial trace, reduced density, geometric thermal states, relative
     modular Hamiltonians, and level spacing found finite-dimensional Bell/GHZ marginal
     owners, the countable diagonal `SinglePrimeThermalState`, and the exact frozen
     derivative owner imported above. None constructs the countable two-mode marginal or
     identifies its negative-log density spacing.
   * Pinned Mathlib exact searches for `partialTrace`, `vonNeumannEntropy`, `relative modular`,
     `modular Hamiltonian`, and `level spacing` returned no declaration. Its geometric
     measure, infinite-sum, real-log, matrix, and square-root primitives are reused below.
   * GitHub Lean-code searches found finite-dimensional partial-trace/entropy implementations
     in `zblore/csd-lean4` and `QuAIR/Lean-QIT`, plus a scalar modular-flow surrogate in
     `jagg-ix/catept-main`; none states this countable geometric thermofield theorem.
   * The exact-carrier probe `/private/tmp/w73d38-atom1-probe.lean` constructed the countable
     Schmidt amplitude, infinite partial trace, diagonal entropy, and modular spectrum and
     exited 0 before these repository artifacts were written. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

noncomputable section

namespace D5.S3.Observer.DefectModularFirstLaw.ThermofieldMarginalModularSpectrum

open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Observer.DefectModularFirstLaw.EntropyDerivativeEqualsModularGap
open D5.S3.Quantum.PureState.PureStateHandshake

/-- The countable two-mode Schmidt amplitude with geometric visible weights. -/
def thermofieldAmplitude (q : Real) (index : Nat × Nat) : Complex :=
  if index.1 = index.2 then
    (Real.sqrt ((1 - q) * q ^ index.1) : Complex)
  else 0

/-- Trace out the second countable mode by summing its diagonal matrix blocks. -/
def countablePartialTraceRight
    (joint : Matrix (Nat × Nat) (Nat × Nat) Complex) : Matrix Nat Nat Complex :=
  fun i j => ∑' k : Nat, joint (i, k) (j, k)

/-- The diagonal geometric density with visible weight `(1-q)q^n` at occupation `n`. -/
def geometricDiagonalDensity (q : Real) : Matrix Nat Nat Complex :=
  Matrix.diagonal fun n => (((1 - q) * q ^ n : Real) : Complex)

/-- Entropy of a countable diagonal density, evaluated on its real diagonal weights. -/
def diagonalEntropy (density : Matrix Nat Nat Complex) : Real :=
  ∑' n : Nat, Real.negMulLog (density n n).re

/-- The `n`-th spectral value of the relative modular Hamiltonian `-log rho_vis`. -/
def relativeModularEnergy (q : Real) (n : Nat) : Real :=
  -Real.log ((1 - q) * q ^ n)

private def thermalSuccessParameter
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) : unitInterval :=
  ⟨1 - q, sub_nonneg.mpr hq1.le, sub_le_self 1 hq0.le⟩

private def thermalPMF (q : Real) (hq0 : 0 < q) (hq1 : q < 1) : PMF Nat :=
  (ProbabilityTheory.geometricMeasure (thermalSuccessParameter q hq0 hq1)).toPMF

private theorem thermalPMF_apply
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) (n : Nat) :
    pmfReal (thermalPMF q hq0 hq1) n = (1 - q) * q ^ n := by
  let p := thermalSuccessParameter q hq0 hq1
  have hp : p ≠ 0 := by
    intro h
    have hval := congrArg Subtype.val h
    dsimp [p, thermalSuccessParameter] at hval
    linarith
  rw [pmfReal, thermalPMF, MeasureTheory.Measure.toPMF_apply,
    ProbabilityTheory.geometricMeasure_singleton hp]
  rw [ENNReal.toReal_ofReal (ProbabilityTheory.geometricMeasure_nonneg p n)]
  dsimp [p, thermalSuccessParameter]
  ring

private theorem thermofield_partial_trace
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) :
    countablePartialTraceRight (rankOneDensity (thermofieldAmplitude q)) =
      geometricDiagonalDensity q := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [countablePartialTraceRight, tsum_eq_single i]
    · simp only [rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply,
        thermofieldAmplitude, if_pos, geometricDiagonalDensity,
        Matrix.diagonal_apply_eq, Complex.star_def, Complex.conj_ofReal,
        ← Complex.ofReal_mul]
      norm_cast
      simpa [pow_two] using Real.sq_sqrt
        (mul_nonneg (sub_nonneg.mpr hq1.le) (pow_nonneg hq0.le _))
    · intro k hki
      simp [rankOneDensity, Matrix.vecMulVec_apply, thermofieldAmplitude, Ne.symm hki]
  · rw [countablePartialTraceRight]
    have hzero : (fun k : Nat =>
        (if i = k then (Real.sqrt ((1 - q) * q ^ i) : Complex) else 0) *
          star (if j = k then (Real.sqrt ((1 - q) * q ^ j) : Complex) else 0)) = 0 := by
      funext k
      by_cases hik : i = k
      · have hjk : j ≠ k := by
          intro h
          exact hij (hik.trans h.symm)
        simp [hik, hjk]
      · simp [hik]
    simp only [rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply,
      thermofieldAmplitude, hzero, geometricDiagonalDensity,
      Matrix.diagonal_apply_ne _ hij]
    exact tsum_zero

private theorem geometricDiagonalDensity_normalized
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) :
    ∑' n : Nat, (geometricDiagonalDensity q n n).re = 1 := by
  have hgeom : Summable (fun n : Nat => q ^ n) :=
    summable_geometric_of_lt_one hq0.le hq1
  simp_rw [geometricDiagonalDensity, Matrix.diagonal_apply_eq, Complex.ofReal_re]
  rw [hgeom.tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
  exact mul_inv_cancel₀ (sub_pos.mpr hq1).ne'

private theorem geometricDiagonalDensity_mean_occupation
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) :
    (∑' n : Nat, (n : Real) * (geometricDiagonalDensity q n n).re) =
      rankOneThermalOccupation q := by
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0]
    exact hq1
  simp_rw [geometricDiagonalDensity, Matrix.diagonal_apply_eq, Complex.ofReal_re]
  have hfactor : ∀ n : Nat,
      (n : Real) * ((1 - q) * q ^ n) = (1 - q) * ((n : Real) * q ^ n) := by
    intro n
    ring
  simp_rw [hfactor]
  rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  unfold rankOneThermalOccupation
  field_simp [(sub_pos.mpr hq1).ne']

private theorem diagonalEntropy_geometric_eq_rankOneThermalEntropy
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) :
    diagonalEntropy (geometricDiagonalDensity q) =
      rankOneThermalEntropy (q / (1 - q)) := by
  let P := thermalPMF q hq0 hq1
  have hmass : ∀ n, pmfReal P n = (1 - q) * q ^ n := by
    exact thermalPMF_apply q hq0 hq1
  have hclosed := geometric_entropy_eq P q (-Real.log q) hq0 hq1 (by ring) hmass
  have hdiag : diagonalEntropy (geometricDiagonalDensity q) = countableEntropy P := by
    unfold diagonalEntropy countableEntropy
    apply tsum_congr
    intro n
    rw [hmass n]
    rw [geometricDiagonalDensity, Matrix.diagonal_apply_eq, Complex.ofReal_re]
  rw [hdiag, hclosed]
  unfold rankOneThermalEntropy
  have h1q : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hq : q ≠ 0 := hq0.ne'
  have hocc : q / (1 - q) + 1 = (1 - q)⁻¹ := by
    field_simp
    ring
  rw [hocc, Real.log_inv, Real.log_div hq h1q]
  field_simp
  ring

private theorem relativeModularEnergy_spacing
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) (n : Nat) :
    relativeModularEnergy q (n + 1) - relativeModularEnergy q n = -Real.log q := by
  have h1q : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hq : q ≠ 0 := hq0.ne'
  rw [relativeModularEnergy, relativeModularEnergy, pow_succ]
  rw [Real.log_mul h1q (mul_ne_zero (pow_ne_zero _ hq) hq)]
  rw [Real.log_mul h1q (pow_ne_zero _ hq)]
  rw [Real.log_mul (pow_ne_zero _ hq) hq]
  ring

/-- The local modular first law on the exact countable thermofield carrier. The frozen
derivative and differential are retained, while the new clauses construct the hidden-partner
partial trace, normalize its visible geometric density, compute its mean occupation, identify
its entropy with `S(N)`, and derive the adjacent relative modular energy spacing from
`-log rho_vis`. This is local rank-one modular thermodynamics, not a physical black-hole first
law. -/
theorem local_modular_first_law_from_thermofield_marginal
    (delta omega : Real) (homega : 0 < omega) (horizon : omega < delta) :
    let q := localModularWeight delta omega
    let occupation := rankOneThermalOccupation q
    let epsilon := defectModularGap delta omega
    let visibleDensity :=
      countablePartialTraceRight (rankOneDensity (thermofieldAmplitude q))
    ((HasDerivAt rankOneThermalEntropy
          (Real.log ((occupation + 1) / occupation)) occupation ∧
        Real.log ((occupation + 1) / occupation) = -Real.log q ∧
        -Real.log q = epsilon) ∧
      ((∀ dN : Real,
          (fderiv Real rankOneThermalEntropy occupation) dN = epsilon * dN) ∧
        epsilon = 2 * Real.log (delta / omega))) ∧
      visibleDensity = geometricDiagonalDensity q ∧
      (∑' n : Nat, (visibleDensity n n).re) = 1 ∧
      (∑' n : Nat, (n : Real) * (visibleDensity n n).re) = occupation ∧
      diagonalEntropy visibleDensity = rankOneThermalEntropy occupation ∧
      ∀ n : Nat,
        relativeModularEnergy q (n + 1) - relativeModularEnergy q n = epsilon := by
  have hdelta : 0 < delta := homega.trans horizon
  have hratioPos : 0 < omega / delta := div_pos homega hdelta
  have hratioLt : omega / delta < 1 := (div_lt_one hdelta).2 horizon
  have hq0 : 0 < localModularWeight delta omega := by
    unfold localModularWeight
    positivity
  have hq1 : localModularWeight delta omega < 1 := by
    unfold localModularWeight
    simpa using
      (sq_lt_sq₀ hratioPos.le (by norm_num : (0 : Real) ≤ 1)).2 hratioLt
  rcases entropy_derivative_equals_modular_gap delta omega homega horizon with
    ⟨hderivative, hdifferential⟩
  have htrace := thermofield_partial_trace (localModularWeight delta omega) hq0 hq1
  have hnormal := geometricDiagonalDensity_normalized
    (localModularWeight delta omega) hq0 hq1
  have hmean := geometricDiagonalDensity_mean_occupation
    (localModularWeight delta omega) hq0 hq1
  have hentropy := diagonalEntropy_geometric_eq_rankOneThermalEntropy
    (localModularWeight delta omega) hq0 hq1
  refine ⟨⟨hderivative, hdifferential⟩, htrace, ?_, ?_, ?_, ?_⟩
  · rw [htrace]
    exact hnormal
  · rw [htrace]
    exact hmean
  · rw [htrace]
    exact hentropy
  · intro n
    rw [relativeModularEnergy_spacing (localModularWeight delta omega) hq0 hq1 n]
    exact hderivative.2.2

#print axioms local_modular_first_law_from_thermofield_marginal

end D5.S3.Observer.DefectModularFirstLaw.ThermofieldMarginalModularSpectrum
