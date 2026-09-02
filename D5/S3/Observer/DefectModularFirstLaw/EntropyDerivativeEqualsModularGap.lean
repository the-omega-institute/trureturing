/- GID: D5/S3/Observer/DefectModularFirstLaw/EntropyDerivativeEqualsModularGap
   generality: G
   mirror-B: D5/B/S3/Observer/DefectModularFirstLaw/EntropyDerivativeEqualsModularGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The rank-one thermal entropy derivative equals its local modular gap. -/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * Current-tree searches for the local modular first law, rank-one thermal occupation,
     bosonic entropy, and its derivative found no declaration of this result.
   * Pinned Mathlib supplies `Real.hasDerivAt_mul_log`, `HasDerivAt.comp_add_const`,
     `Real.log_div`,
     `Real.log_inv`, `Real.log_pow`, and `fderiv_eq_deriv_mul`; these exact hits
     are imported and reused below.
   * Loogle and LeanSearch found the same Mathlib primitives, including binary-entropy
     derivatives, but no theorem for `(N+1) log (N+1) - N log N` at geometric
     occupation `N = q/(1-q)`. Anonymous GitHub search was rate/auth limited, and
     Reservoir exposed no declaration-level search endpoint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.DefectModularFirstLaw.EntropyDerivativeEqualsModularGap

/-- The local geometric weight `q = (omega / delta)^2`. -/
def localModularWeight (delta omega : ℝ) : ℝ :=
  (omega / delta) ^ 2

/-- The externally visible mean occupation of a rank-one geometric thermal state. -/
def rankOneThermalOccupation (q : ℝ) : ℝ :=
  q / (1 - q)

/-- The entropy of a rank-one geometric thermal state, expressed through its mean
occupation. -/
def rankOneThermalEntropy (occupation : ℝ) : ℝ :=
  (occupation + 1) * Real.log (occupation + 1) -
    occupation * Real.log occupation

/-- The dimensionless modular gap determined by defect depth and observation scale. -/
def defectModularGap (delta omega : ℝ) : ℝ :=
  2 * Real.log (delta / omega)

/-- For a positive observation scale strictly below the defect depth, the derivative
of rank-one thermal entropy forms the local modular first-law chain. The second
conjunct identifies the full differential on every occupation increment. -/
theorem entropy_derivative_equals_modular_gap
    (delta omega : ℝ) (homega : 0 < omega) (horizon : omega < delta) :
    let q := localModularWeight delta omega
    let occupation := rankOneThermalOccupation q
    let epsilon := defectModularGap delta omega
    (HasDerivAt rankOneThermalEntropy
          (Real.log ((occupation + 1) / occupation)) occupation ∧
        Real.log ((occupation + 1) / occupation) = -Real.log q ∧
        -Real.log q = epsilon) ∧
      ((∀ dN : ℝ,
          (fderiv ℝ rankOneThermalEntropy occupation) dN = epsilon * dN) ∧
        epsilon = 2 * Real.log (delta / omega)) := by
  have hdelta : 0 < delta := homega.trans horizon
  have hratioPos : 0 < omega / delta := div_pos homega hdelta
  have hratioLt : omega / delta < 1 := (div_lt_one hdelta).2 horizon
  let q := localModularWeight delta omega
  have hqPos : 0 < q := by
    dsimp only [q, localModularWeight]
    positivity
  have hqLt : q < 1 := by
    dsimp only [q, localModularWeight]
    simpa using
      (sq_lt_sq₀ hratioPos.le (by norm_num : (0 : ℝ) ≤ 1)).2 hratioLt
  have hqNe : q ≠ 0 := ne_of_gt hqPos
  have honeSubQPos : 0 < 1 - q := sub_pos.mpr hqLt
  have honeSubQNe : 1 - q ≠ 0 := ne_of_gt honeSubQPos
  let occupation := rankOneThermalOccupation q
  have hoccupationPos : 0 < occupation := by
    dsimp only [occupation, rankOneThermalOccupation]
    exact div_pos hqPos honeSubQPos
  have hoccupationNe : occupation ≠ 0 := ne_of_gt hoccupationPos
  have hoccupationPlusOnePos : 0 < occupation + 1 := by positivity
  have hoccupationPlusOneNe : occupation + 1 ≠ 0 :=
    ne_of_gt hoccupationPlusOnePos
  let epsilon := defectModularGap delta omega
  have hEntropyDerivative :
      HasDerivAt rankOneThermalEntropy
        (Real.log ((occupation + 1) / occupation)) occupation := by
    have hDifferentiable :
        DifferentiableAt ℝ rankOneThermalEntropy occupation := by
      unfold rankOneThermalEntropy
      fun_prop
    refine hDifferentiable.hasDerivAt.congr_deriv ?_
    unfold rankOneThermalEntropy
    rw [deriv_fun_sub]
    · rw [deriv_comp_add_const (fun x : ℝ ↦ x * Real.log x) 1 occupation,
        Real.deriv_mul_log hoccupationPlusOneNe,
        Real.deriv_mul_log hoccupationNe,
        Real.log_div hoccupationPlusOneNe hoccupationNe]
      ring
    all_goals fun_prop
  have hOccupationRatio : (occupation + 1) / occupation = q⁻¹ := by
    dsimp only [occupation, rankOneThermalOccupation]
    field_simp
    ring
  have hLogOccupation :
      Real.log ((occupation + 1) / occupation) = -Real.log q := by
    rw [hOccupationRatio, Real.log_inv]
  have hLogGap : -Real.log q = epsilon := by
    dsimp only [q, epsilon, localModularWeight, defectModularGap]
    rw [Real.log_pow, Real.log_div homega.ne' hdelta.ne']
    rw [Real.log_div hdelta.ne' homega.ne']
    ring
  have hDifferential : ∀ dN : ℝ,
      (fderiv ℝ rankOneThermalEntropy occupation) dN = epsilon * dN := by
    intro dN
    rw [fderiv_eq_deriv_mul, hEntropyDerivative.deriv, hLogOccupation, hLogGap]
  exact ⟨⟨hEntropyDerivative, hLogOccupation, hLogGap⟩,
    ⟨hDifferential, rfl⟩⟩

/- Reverse probe for boxed assertion 1388.3: the public chain exposes the modular
gap itself as the genuine entropy derivative, not merely as a scalar equality. -/
example (delta omega : ℝ) (homega : 0 < omega) (horizon : omega < delta) :
    let q := localModularWeight delta omega
    let occupation := rankOneThermalOccupation q
    HasDerivAt rankOneThermalEntropy (defectModularGap delta omega) occupation := by
  rcases entropy_derivative_equals_modular_gap delta omega homega horizon with
    ⟨⟨hDerivative, hLog, hGap⟩, _⟩
  exact hDerivative.congr_deriv (hLog.trans hGap)

/- Reverse probe for boxed assertion 1388.4: evaluating the public differential at
unit increment recovers the explicit modular energy spacing. -/
example (delta omega : ℝ) (homega : 0 < omega) (horizon : omega < delta) :
    let q := localModularWeight delta omega
    let occupation := rankOneThermalOccupation q
    (fderiv ℝ rankOneThermalEntropy occupation) 1 =
      2 * Real.log (delta / omega) := by
  rcases entropy_derivative_equals_modular_gap delta omega homega horizon with
    ⟨_, ⟨hDifferential, hGap⟩⟩
  simpa [hGap] using hDifferential 1

#print axioms entropy_derivative_equals_modular_gap

end D5.S3.Observer.DefectModularFirstLaw.EntropyDerivativeEqualsModularGap
