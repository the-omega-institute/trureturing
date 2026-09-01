/- GID: D5/S3/Weil/ZetaLinear/FiniteHeightCompletionVariance
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/FiniteHeightCompletionVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define finite-height completion variance and prove its nonnegativity. -/

import D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening

/- Library-search audit trail (2026-09-01):
   * Repository searches for completion variance, orbit variance, finite-height
     zero windows, weighted square sums, and the same-height zero coordinate
     found no equivalent definition. `BarycenterDefectDecomposition` supplies
     the adjacent plus/minus delta orbit, while `ReflectedZeroModePhaseFlattening`
     supplies the canonical `criticalDisplacement`; the latter is reused here.
   * `ZeroData.symmetricIndices` supplies finite symmetric spectral-radius
     cutoffs, not the source's one-sided condition `0 < Im rho <= T`. Since the
     atom does not state the required finiteness theorem, `FiniteZeroWindow`
     records that condition as an explicit premise rather than assuming it.
   * Pinned Mathlib supplies `Finset.sum_nonneg`, `mul_nonneg`, `sq_nonneg`,
     and nonnegativity of natural-number casts. Searches of Mathlib and the
     installed admissible third-party packages found no domain-level wrapper. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaLinear.FiniteHeightCompletionVariance

open D5.S3.Weil.Convention
open D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening

/-- A finite presentation of exactly the zeros in the source's positive
ordinate window. The finiteness field is explicit because it is not supplied
by the atom. -/
structure FiniteZeroWindow (xi : ℂ → ℂ) (T : ℝ) where
  height_pos : 0 < T
  points : Finset ℂ
  mem_iff : ∀ rho, rho ∈ points ↔ xi rho = 0 ∧ 0 < rho.im ∧ rho.im ≤ T

/-- Formula (631.1), with the completion function and multiplicities kept as
abstract parameters and the finite zero window supplied explicitly. -/
def completionVariance {xi : ℂ → ℂ} {T : ℝ}
    (window : FiniteZeroWindow xi T) (multiplicity : ℂ → ℕ) : ℝ :=
  ∑ rho ∈ window.points,
    (multiplicity rho : ℝ) * criticalDisplacement rho ^ 2

/-- Every multiplicity-weighted squared displacement in the finite-height
variance is nonnegative. -/
theorem completion_variance_term_nonnegative
    {xi : ℂ → ℂ} {T : ℝ} (window : FiniteZeroWindow xi T)
    (multiplicity : ℂ → ℕ) {rho : ℂ} (_hrho : rho ∈ window.points) :
    0 ≤ (multiplicity rho : ℝ) * criticalDisplacement rho ^ 2 := by
  exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- Formula (631.1) is termwise nonnegative, hence its finite sum is
nonnegative. -/
theorem finite_height_completion_variance_nonnegative
    {xi : ℂ → ℂ} {T : ℝ} (window : FiniteZeroWindow xi T)
    (multiplicity : ℂ → ℕ) :
    (∀ rho ∈ window.points,
        0 ≤ (multiplicity rho : ℝ) * criticalDisplacement rho ^ 2) ∧
      0 ≤ completionVariance window multiplicity := by
  constructor
  · intro rho hrho
    exact completion_variance_term_nonnegative window multiplicity hrho
  · unfold completionVariance
    exact Finset.sum_nonneg fun rho hrho =>
      completion_variance_term_nonnegative window multiplicity hrho

/-- A concrete completion function with one zero in the positive unit-height
window. -/
def witnessXi (rho : ℂ) : ℂ :=
  rho - Complex.I

/-- The concrete zero has multiplicity one. -/
def witnessMultiplicity (_rho : ℂ) : ℕ :=
  1

/-- The singleton is exactly the positive unit-height zero window of
`witnessXi`. -/
def witnessWindow : FiniteZeroWindow witnessXi 1 where
  height_pos := by norm_num
  points := {Complex.I}
  mem_iff := by
    intro rho
    constructor
    · intro hrho
      have hEq : rho = Complex.I := by simpa using hrho
      subst rho
      norm_num [witnessXi]
    · intro hrho
      have hEq : rho = Complex.I := by
        apply sub_eq_zero.mp
        simpa [witnessXi] using hrho.1
      simp [hEq]

/-- The definition is nonempty and nondegenerate: a singleton zero of
multiplicity one at `rho = i` has completion variance `1/4 > 0`. -/
theorem exists_positive_finite_height_completion_variance :
    ∃ (xi : ℂ → ℂ) (T : ℝ) (window : FiniteZeroWindow xi T)
        (multiplicity : ℂ → ℕ),
      window.points.Nonempty ∧
        completionVariance window multiplicity = 1 / 4 ∧
        0 < completionVariance window multiplicity := by
  refine ⟨witnessXi, 1, witnessWindow, witnessMultiplicity, ?_⟩
  norm_num [completionVariance, witnessWindow, witnessMultiplicity,
    criticalDisplacement, criticalAbscissa]

#print axioms completion_variance_term_nonnegative
#print axioms finite_height_completion_variance_nonnegative
#print axioms exists_positive_finite_height_completion_variance

end D5.S3.Weil.ZetaLinear.FiniteHeightCompletionVariance
