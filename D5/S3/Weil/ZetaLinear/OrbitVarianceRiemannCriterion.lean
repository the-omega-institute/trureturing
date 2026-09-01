/- GID: D5/S3/Weil/ZetaLinear/OrbitVarianceRiemannCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/OrbitVarianceRiemannCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize the critical-line condition by vanishing completion variance. -/

import D5.S3.Weil.ZetaLinear.FiniteHeightCompletionVariance

/- Library-search audit trail (2026-09-01):
   * Repository searches for orbit/completion variance, vanishing nonnegative
     sums, and critical-line criteria found no variance-zero iff. The adjacent
     `FiniteHeightCompletionVariance` definitions and nonnegativity theorems
     are reused without restatement. Existing critical-line criteria use
     mirror indices, curvature support, unitarity, or temperedness instead.
   * Pinned Mathlib supplies `Finset.sum_eq_zero_iff_of_nonneg` and
     `Finset.sum_pos_iff_of_nonneg`; these discharge the finite-sum core.
   * Searches of the installed admissible third-party Lean packages found no
     domain-level orbit-variance criterion.
   * `FiniteZeroWindow.mem_iff` includes `0 < rho.im`. Consequently, the full
     all-zero criterion explicitly requires every zero's real part to have a
     positive-ordinate representative; this bridge is not hidden in the RH
     predicate. Strict positivity of the natural multiplicities is likewise
     explicit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaLinear.OrbitVarianceRiemannCriterion

open D5.S3.Weil.Convention
open D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening
open D5.S3.Weil.ZetaLinear.FiniteHeightCompletionVariance

/-- Every zero represented at positive ordinate lies on the critical line. -/
def PositiveOrdinateCriticalLine (xi : ℂ → ℂ) : Prop :=
  ∀ rho, xi rho = 0 → 0 < rho.im → rho.re = criticalAbscissa

/-- The abstract critical-line statement for all zeros of a supplied
completion function. -/
def CriticalLineHypothesis (xi : ℂ → ℂ) : Prop :=
  ∀ rho, xi rho = 0 → rho.re = criticalAbscissa

/-- A finite completion variance vanishes exactly when all of its nonnegative
summands vanish. -/
theorem completion_variance_eq_zero_iff_terms_zero
    {xi : ℂ → ℂ} {T : ℝ} (window : FiniteZeroWindow xi T)
    (multiplicity : ℂ → ℕ) :
    completionVariance window multiplicity = 0 ↔
      ∀ rho ∈ window.points,
        (multiplicity rho : ℝ) * criticalDisplacement rho ^ 2 = 0 := by
  unfold completionVariance
  exact Finset.sum_eq_zero_iff_of_nonneg fun rho hrho ↦
    completion_variance_term_nonnegative window multiplicity hrho

/-- A positive-multiplicity zero off the critical line contributes a strictly
positive summand. -/
theorem completion_variance_term_positive
    (multiplicity : ℂ → ℕ) {rho : ℂ}
    (hMultiplicity : 0 < multiplicity rho)
    (hOffLine : rho.re ≠ criticalAbscissa) :
    0 < (multiplicity rho : ℝ) * criticalDisplacement rho ^ 2 := by
  apply mul_pos
  · exact_mod_cast hMultiplicity
  · apply sq_pos_of_ne_zero
    simpa [criticalDisplacement] using sub_ne_zero.mpr hOffLine

/-- An off-line zero at positive ordinate is detected at the explicit height
`T = rho.im + 1`. -/
theorem exists_positive_completion_variance_of_offline_zero
    {xi : ℂ → ℂ} (multiplicity : ℂ → ℕ)
    (windows : ∀ T : ℝ, 0 < T → FiniteZeroWindow xi T)
    (hMultiplicityPositive :
      ∀ rho, xi rho = 0 → 0 < rho.im → 0 < multiplicity rho)
    {rho : ℂ} (hZero : xi rho = 0) (hIm : 0 < rho.im)
    (hOffLine : rho.re ≠ criticalAbscissa) :
    ∃ (T : ℝ) (hT : 0 < T),
      rho.im < T ∧ 0 < completionVariance (windows T hT) multiplicity := by
  let T : ℝ := rho.im + 1
  have hT : 0 < T := by
    dsimp [T]
    linarith
  let window := windows T hT
  have hRhoMem : rho ∈ window.points := by
    apply (window.mem_iff rho).2
    refine ⟨hZero, hIm, ?_⟩
    dsimp [T]
    linarith
  refine ⟨T, hT, by dsimp [T]; linarith, ?_⟩
  unfold completionVariance
  exact (Finset.sum_pos_iff_of_nonneg fun sigma hSigma ↦
    completion_variance_term_nonnegative window multiplicity hSigma).2
      ⟨rho, hRhoMem,
        completion_variance_term_positive multiplicity
          (hMultiplicityPositive rho hZero hIm) hOffLine⟩

/-- On the positive-ordinate zero set, vanishing completion variance at every
positive height is equivalent to the critical-line condition. -/
theorem positive_ordinate_orbit_variance_criterion
    (xi : ℂ → ℂ) (multiplicity : ℂ → ℕ)
    (windows : ∀ T : ℝ, 0 < T → FiniteZeroWindow xi T)
    (hMultiplicityPositive :
      ∀ rho, xi rho = 0 → 0 < rho.im → 0 < multiplicity rho) :
    PositiveOrdinateCriticalLine xi ↔
      ∀ (T : ℝ) (hT : 0 < T),
        completionVariance (windows T hT) multiplicity = 0 := by
  constructor
  · intro hCritical T hT
    apply (completion_variance_eq_zero_iff_terms_zero
      (windows T hT) multiplicity).2
    intro rho hRho
    have hData := ((windows T hT).mem_iff rho).1 hRho
    have hLine := hCritical rho hData.1 hData.2.1
    simp [criticalDisplacement, hLine]
  · intro hVariance rho hZero hIm
    let T : ℝ := rho.im + 1
    have hT : 0 < T := by
      dsimp [T]
      linarith
    let window := windows T hT
    have hRhoMem : rho ∈ window.points := by
      apply (window.mem_iff rho).2
      refine ⟨hZero, hIm, ?_⟩
      dsimp [T]
      linarith
    have hTerm :
        (multiplicity rho : ℝ) * criticalDisplacement rho ^ 2 = 0 :=
      (completion_variance_eq_zero_iff_terms_zero window multiplicity).1
        (hVariance T hT) rho hRhoMem
    have hCast : (multiplicity rho : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hMultiplicityPositive rho hZero hIm))
    have hSquare : criticalDisplacement rho ^ 2 = 0 :=
      (mul_eq_zero.mp hTerm).resolve_left hCast
    have hDisplacement : criticalDisplacement rho = 0 := by
      nlinarith [sq_nonneg (criticalDisplacement rho)]
    change rho.re - criticalAbscissa = 0 at hDisplacement
    exact sub_eq_zero.mp hDisplacement

/-- Orbit-variance RH criterion. The positive-representative premise is the
explicit bridge from the all-zero predicate to the positive-ordinate window
used by formula (631.1). -/
theorem orbit_variance_rh_criterion
    (xi : ℂ → ℂ) (multiplicity : ℂ → ℕ)
    (windows : ∀ T : ℝ, 0 < T → FiniteZeroWindow xi T)
    (hMultiplicityPositive :
      ∀ rho, xi rho = 0 → 0 < rho.im → 0 < multiplicity rho)
    (positiveRepresentative :
      ∀ rho, xi rho = 0 →
        ∃ sigma, xi sigma = 0 ∧ 0 < sigma.im ∧ sigma.re = rho.re) :
    CriticalLineHypothesis xi ↔
      ∀ (T : ℝ) (hT : 0 < T),
        completionVariance (windows T hT) multiplicity = 0 := by
  have hPositiveCriterion :=
    positive_ordinate_orbit_variance_criterion xi multiplicity windows
      hMultiplicityPositive
  constructor
  · intro hCritical
    apply hPositiveCriterion.mp
    intro rho hZero _hIm
    exact hCritical rho hZero
  · intro hVariance rho hZero
    have hPositive := hPositiveCriterion.mpr hVariance
    obtain ⟨sigma, hSigmaZero, hSigmaIm, hSigmaRe⟩ :=
      positiveRepresentative rho hZero
    exact hSigmaRe.symm.trans (hPositive sigma hSigmaZero hSigmaIm)

/-- The imported off-line witness has its zero below height two and variance
`1/4`, hence strictly positive. -/
def witnessWindowTwo : FiniteZeroWindow witnessXi 2 where
  height_pos := by norm_num
  points := {Complex.I}
  mem_iff := by
    intro rho
    constructor
    · intro hRho
      have hEq : rho = Complex.I := by simpa using hRho
      subst rho
      norm_num [witnessXi]
    · intro hRho
      have hEq : rho = Complex.I := by
        apply sub_eq_zero.mp
        simpa [witnessXi] using hRho.1
      simp [hEq]

theorem witnessXi_offline_positive_variance :
    witnessXi Complex.I = 0 ∧
      Complex.I.re ≠ criticalAbscissa ∧
      Complex.I.im < (2 : ℝ) ∧
      completionVariance witnessWindowTwo witnessMultiplicity = 1 / 4 ∧
      0 < completionVariance witnessWindowTwo witnessMultiplicity := by
  norm_num [completionVariance, witnessWindowTwo, witnessMultiplicity,
    witnessXi, criticalDisplacement, criticalAbscissa]

/-- A completion function whose only zero is on the critical line. -/
def criticalLineWitnessXi (rho : ℂ) : ℂ :=
  rho - ((criticalAbscissa : ℂ) + Complex.I)

/-- The positive unit-height window for `criticalLineWitnessXi`. -/
def criticalLineWitnessWindow : FiniteZeroWindow criticalLineWitnessXi 1 where
  height_pos := by norm_num
  points := {((criticalAbscissa : ℂ) + Complex.I)}
  mem_iff := by
    intro rho
    constructor
    · intro hRho
      have hEq : rho = (criticalAbscissa : ℂ) + Complex.I := by
        simpa using hRho
      subst rho
      norm_num [criticalLineWitnessXi, criticalAbscissa]
    · intro hRho
      have hEq : rho = (criticalAbscissa : ℂ) + Complex.I := by
        apply sub_eq_zero.mp
        simpa [criticalLineWitnessXi] using hRho.1
      simp [hEq]

/-- The zero-variance side is nonempty: the singleton zero lies on the
critical line and contributes zero variance. -/
theorem critical_line_zero_variance_example :
    CriticalLineHypothesis criticalLineWitnessXi ∧
      criticalLineWitnessWindow.points.Nonempty ∧
      completionVariance criticalLineWitnessWindow witnessMultiplicity = 0 := by
  constructor
  · intro rho hZero
    have hEq : rho = (criticalAbscissa : ℂ) + Complex.I := by
      apply sub_eq_zero.mp
      simpa [criticalLineWitnessXi] using hZero
    simp [hEq]
  · constructor
    · simp [criticalLineWitnessWindow]
    · norm_num [completionVariance, criticalLineWitnessWindow,
        witnessMultiplicity, criticalDisplacement]

#print axioms completion_variance_eq_zero_iff_terms_zero
#print axioms exists_positive_completion_variance_of_offline_zero
#print axioms orbit_variance_rh_criterion
#print axioms witnessXi_offline_positive_variance
#print axioms critical_line_zero_variance_example

end D5.S3.Weil.ZetaLinear.OrbitVarianceRiemannCriterion
