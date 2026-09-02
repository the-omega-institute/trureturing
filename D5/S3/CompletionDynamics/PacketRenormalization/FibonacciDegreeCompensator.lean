/- GID: D5/S3/CompletionDynamics/PacketRenormalization/FibonacciDegreeCompensator
   generality: I
   mirror-B: D5/B/S3/CompletionDynamics/PacketRenormalization/FibonacciDegreeCompensator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Even Fibonacci degrees compensate inverse-square golden contraction. -/

import Mathlib.Analysis.SpecificLimits.Fibonacci

/- Library-search audit trail (2026-09-02):
   * Repository searches found no declaration covering the even-index Fibonacci
     compensation limit, its defect-product consequence, or the compensator role.
   * Pinned Mathlib supplies the exact Binet identity `Real.coe_fib_eq`, the
     golden-ratio bounds, and `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`.
   * Loogle and GitHub Lean-code searches found those Mathlib ingredients and
     mirrors, but no exact theorem for this normalized even-index limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.PacketRenormalization.FibonacciDegreeCompensator

open Filter Function Topology
open scoped goldenRatio

/-- One continuous golden renormalization step on a transverse defect. -/
def goldenRenormalization (defect : ℝ) : ℝ :=
  (Real.goldenRatio ^ 2)⁻¹ * defect

/-- The integral observation degree selected by an even Fibonacci scale. -/
def fibonacciDegree (offset step : ℕ) : ℕ :=
  Nat.fib (2 * step + offset)

/-- An integer degree sequence compensates a renormalization when its product
with every renormalization orbit has the stated normalized limiting gain. -/
def IsIntegerCompensator
    (renormalization : ℝ → ℝ) (degree : ℕ → ℕ) (gain : ℝ) : Prop :=
  ∀ initial : ℝ,
    Tendsto
      (fun step : ℕ => (degree step : ℝ) * (renormalization^[step]) initial)
      atTop (𝓝 (initial * gain))

private theorem goldenRenormalization_iterate (initial : ℝ) (step : ℕ) :
    (goldenRenormalization^[step]) initial =
      ((Real.goldenRatio ^ 2)⁻¹) ^ step * initial := by
  induction step generalizing initial with
  | zero => simp
  | succ step ih =>
      rw [iterate_succ_apply, ih]
      simp only [goldenRenormalization]
      ring

private theorem fibonacci_degree_limit (offset : ℕ) :
    Tendsto
      (fun step : ℕ =>
        (fibonacciDegree offset step : ℝ) *
          (Real.goldenRatio ^ (2 * step))⁻¹)
      atTop
      (𝓝 (Real.goldenRatio ^ offset / Real.sqrt 5)) := by
  have hPhi : Real.goldenRatio ≠ 0 := Real.goldenRatio_pos.ne'
  have hSqrtFive : Real.sqrt 5 ≠ 0 := by positivity
  have hRatio : |Real.goldenConj / Real.goldenRatio| < 1 := by
    rw [abs_div, div_lt_one (by positivity), abs_of_pos Real.goldenRatio_pos, abs_lt]
    ring_nf
    bound
  have hSquare : |(Real.goldenConj / Real.goldenRatio) ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg (Real.goldenConj / Real.goldenRatio)]
  have hPower :
      Tendsto
        (fun step : ℕ => ((Real.goldenConj / Real.goldenRatio) ^ 2) ^ step)
        atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hSquare
  have hVanish :
      Tendsto
        (fun step : ℕ =>
          (Real.goldenConj ^ offset / Real.sqrt 5) *
            ((Real.goldenConj / Real.goldenRatio) ^ 2) ^ step)
        atTop (𝓝 0) := by
    simpa using hPower.const_mul (Real.goldenConj ^ offset / Real.sqrt 5)
  have hIdentity (step : ℕ) :
      (fibonacciDegree offset step : ℝ) *
          (Real.goldenRatio ^ (2 * step))⁻¹ =
        Real.goldenRatio ^ offset / Real.sqrt 5 -
          (Real.goldenConj ^ offset / Real.sqrt 5) *
            ((Real.goldenConj / Real.goldenRatio) ^ 2) ^ step := by
    unfold fibonacciDegree
    rw [Real.coe_fib_eq]
    simp only [pow_add, pow_mul, div_pow]
    field_simp [hPhi, hSqrtFive]
  rw [show (fun step : ℕ =>
      (fibonacciDegree offset step : ℝ) *
        (Real.goldenRatio ^ (2 * step))⁻¹) =
      (fun step : ℕ =>
        Real.goldenRatio ^ offset / Real.sqrt 5 -
          (Real.goldenConj ^ offset / Real.sqrt 5) *
            ((Real.goldenConj / Real.goldenRatio) ^ 2) ^ step) by
    funext step
    exact hIdentity step]
  simpa using
    (tendsto_const_nhds.sub hVanish :
      Tendsto
        (fun step : ℕ =>
          Real.goldenRatio ^ offset / Real.sqrt 5 -
            (Real.goldenConj ^ offset / Real.sqrt 5) *
              ((Real.goldenConj / Real.goldenRatio) ^ 2) ^ step)
        atTop
        (𝓝 (Real.goldenRatio ^ offset / Real.sqrt 5 - 0)))

/-- For a fixed natural offset, even Fibonacci degrees have the exact Binet
limit, preserve the limiting product of every source-specified defect orbit,
and form an integer compensator for inverse-square golden renormalization. -/
theorem fibonacci_degree_compensator
    (offset : ℕ) (initial : ℝ) (degree : ℕ → ℕ) (defect : ℕ → ℝ)
    (hDegree : ∀ step, degree step = fibonacciDegree offset step)
    (hDefect : ∀ step,
      defect step = initial * (Real.goldenRatio ^ (2 * step))⁻¹) :
    Tendsto
        (fun step : ℕ =>
          (fibonacciDegree offset step : ℝ) *
            (Real.goldenRatio ^ (2 * step))⁻¹)
        atTop
        (𝓝 (Real.goldenRatio ^ offset / Real.sqrt 5)) ∧
      Tendsto
        (fun step : ℕ => (degree step : ℝ) * defect step)
        atTop
        (𝓝 (initial * Real.goldenRatio ^ offset / Real.sqrt 5)) ∧
      IsIntegerCompensator
        goldenRenormalization
        (fibonacciDegree offset)
        (Real.goldenRatio ^ offset / Real.sqrt 5) := by
  have hLimit := fibonacci_degree_limit offset
  refine ⟨hLimit, ?_, ?_⟩
  · have hFunctions :
        (fun step : ℕ => (degree step : ℝ) * defect step) =
          (fun step : ℕ =>
            initial * ((fibonacciDegree offset step : ℝ) *
              (Real.goldenRatio ^ (2 * step))⁻¹)) := by
      funext step
      rw [hDegree step, hDefect step]
      ring
    rw [hFunctions]
    convert hLimit.const_mul initial using 1
    ring
  · intro orbitInitial
    have hScaled := hLimit.const_mul orbitInitial
    convert hScaled using 1
    · funext step
      rw [goldenRenormalization_iterate, inv_pow, ← pow_mul]
      ring

/-- Reverse probe: the public theorem exposes the nontrivial normalized Binet
limit directly, rather than leaving it only in the proof body. -/
example (offset : ℕ) (initial : ℝ) (degree : ℕ → ℕ) (defect : ℕ → ℝ)
    (hDegree : ∀ step, degree step = fibonacciDegree offset step)
    (hDefect : ∀ step,
      defect step = initial * (Real.goldenRatio ^ (2 * step))⁻¹) :
    Tendsto
      (fun step : ℕ =>
        (fibonacciDegree offset step : ℝ) *
          (Real.goldenRatio ^ (2 * step))⁻¹)
      atTop
      (𝓝 (Real.goldenRatio ^ offset / Real.sqrt 5)) :=
  (fibonacci_degree_compensator offset initial degree defect hDegree hDefect).1

/-- Product probe: the source-specified degree and defect sequences retain the
second boxed limit as an independent public leaf. -/
example (offset : ℕ) (initial : ℝ) (degree : ℕ → ℕ) (defect : ℕ → ℝ)
    (hDegree : ∀ step, degree step = fibonacciDegree offset step)
    (hDefect : ∀ step,
      defect step = initial * (Real.goldenRatio ^ (2 * step))⁻¹) :
    Tendsto
      (fun step : ℕ => (degree step : ℝ) * defect step)
      atTop
      (𝓝 (initial * Real.goldenRatio ^ offset / Real.sqrt 5)) :=
  (fibonacci_degree_compensator offset initial degree defect hDegree hDefect).2.1

/-- Role probe: the third public leaf specializes to the orbit beginning at
one, so the compensator claim cannot be discharged only at the zero defect. -/
example (offset : ℕ) (initial : ℝ) (degree : ℕ → ℕ) (defect : ℕ → ℝ)
    (hDegree : ∀ step, degree step = fibonacciDegree offset step)
    (hDefect : ∀ step,
      defect step = initial * (Real.goldenRatio ^ (2 * step))⁻¹) :
    Tendsto
      (fun step : ℕ =>
        (fibonacciDegree offset step : ℝ) *
          (goldenRenormalization^[step]) 1)
      atTop
      (𝓝 (Real.goldenRatio ^ offset / Real.sqrt 5)) := by
  simpa [IsIntegerCompensator] using
    (fibonacci_degree_compensator offset initial degree defect hDegree hDefect).2.2 1

/-- Trivialization probe: even at offset zero, the source degree sequence is
not the constant-zero natural sequence. -/
example : ¬ ∀ step : ℕ, (0 : ℕ) = fibonacciDegree 0 step := by
  intro hZero
  have hOne := hZero 1
  norm_num [fibonacciDegree, Nat.fib] at hOne

#print axioms fibonacci_degree_compensator

end D5.S3.CompletionDynamics.PacketRenormalization.FibonacciDegreeCompensator
