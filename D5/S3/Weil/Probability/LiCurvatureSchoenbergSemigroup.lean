/- GID: D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized positive Li curvature constructs an actual weakly continuous infinitely divisible circle probability evolution without a separate exponential-positivity premise. -/

import D5.S3.Weil.Probability.GeometricLiNegativeType

/-!
The original circleMoment convention and actual measure convolution are reused.
This closes the specific forward Schoenberg obligation for the reconstructed Li
energy, including its Gaussian identity atom. The canonical arithmetic Li
criterion and the actual zero-measure identification are not premises disguised
as constructions, and are not claimed proved here. A new candidate owner for
the derivative-defined canonical Li sequence exists in PR #6172; it is not copied
into this branch or silently imported from an unmerged dependency.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.LiCurvatureSchoenbergSemigroup

open MeasureTheory
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open D5.S3.Weil.Probability.CircleProbabilitySemigroup
open D5.S3.Weil.Probability.LiCurvatureProbabilityCompletion
open D5.S3.Weil.Probability.GeometricLiNegativeType
open scoped BigOperators NNReal MeasureTheory ComplexOrder

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- Every original reconstructed Li energy produces the actual unique weakly
continuous probability semigroup. Exponential matrix positivity is derived. -/
theorem reconstructed_li_probability_semigroup
    (σ : Measure Circle) [IsFiniteMeasure σ] (a : ℝ) (ha : 0 ≤ a) :
    ∃ ρ : ℝ≥0 → ProbabilityMeasure Circle,
      (∀ t n, circleMoment (ρ t : Measure Circle) n =
        (Real.exp (-(t : ℝ) * reconstructedLi σ a n.natAbs) : ℂ)) ∧
      Continuous ρ ∧
      (ρ 0 : Measure Circle) = Measure.dirac 1 ∧
      (∀ s t, (ρ (s + t) : Measure Circle) = (ρ s : Measure Circle) ∗ₘ (ρ t : Measure Circle)) ∧
      (∀ η : ℝ≥0 → ProbabilityMeasure Circle,
        (∀ t n, circleMoment (η t : Measure Circle) n =
          (Real.exp (-(t : ℝ) * reconstructedLi σ a n.natAbs) : ℂ)) → η = ρ) := by
  apply (exponential_toeplitz_iff_probability_semigroup
    (fun n : ℤ => reconstructedLi σ a n.natAbs) (by simp [reconstructedLi_zero])).mp
  intro t N
  exact reconstructed_li_exponential_posSemidef σ a ha
    (fun i : Fin (N + 1) => ((i : ℕ) : ℤ)) (t : ℝ) t.property

/-- A convolution semigroup realizes each natural-time multiple as an actual
iterated convolution starting at the identity measure. -/
theorem semigroup_nsmul_convolution
    (ρ : ℝ≥0 → ProbabilityMeasure Circle)
    (initial : (ρ 0 : Measure Circle) = Measure.dirac 1)
    (semigroup : ∀ s t, (ρ (s + t) : Measure Circle) =
      (ρ s : Measure Circle) ∗ₘ (ρ t : Measure Circle))
    (s : ℝ≥0) (n : ℕ) :
    (ρ (n • s) : Measure Circle) =
      ((fun μ : Measure Circle => μ ∗ₘ (ρ s : Measure Circle))^[n]) (Measure.dirac 1) := by
  induction n with
  | zero => simpa using initial
  | succ n ih =>
      rw [succ_nsmul, semigroup, ih, Function.iterate_succ_apply']

/-- Each time marginal has a probability convolution root of every positive
integer order. The root is the same constructed family at divided time. -/
theorem semigroup_probability_roots
    (ρ : ℝ≥0 → ProbabilityMeasure Circle)
    (initial : (ρ 0 : Measure Circle) = Measure.dirac 1)
    (semigroup : ∀ s t, (ρ (s + t) : Measure Circle) =
      (ρ s : Measure Circle) ∗ₘ (ρ t : Measure Circle))
    (t : ℝ≥0) (n : ℕ) (hn : n ≠ 0) :
    ∃ ν : ProbabilityMeasure Circle,
      ((fun μ : Measure Circle => μ ∗ₘ (ν : Measure Circle))^[n]) (Measure.dirac 1) =
        (ρ t : Measure Circle) := by
  let s : ℝ≥0 := t / (n : ℝ≥0)
  have hn' : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have htime : n • s = t := by
    dsimp [s]
    rw [nsmul_eq_mul]
    field_simp [hn'] <;> ring
  refine ⟨ρ s, ?_⟩
  rw [← semigroup_nsmul_convolution ρ initial semigroup s n, htime]

/-- The original normalized curvature and recurrence give conditional negative
energy on all finite integer samples. The representing measure is constructed. -/
theorem normalized_curvature_conditionally_negative
    (c : ℤ → ℂ) (L : ℕ → ℝ) (normalized : c 0 = 1)
    (positive : ∀ N : ℕ, (toeplitzMatrix c N).PosSemidef)
    (zeroValue : L 0 = 0) (firstNonnegative : 0 ≤ L 1)
    (recurrence : ∀ n, 1 ≤ n →
      L (n + 1) - 2 * L n + L (n - 1) = 2 * L 1 * (c n).re)
    {I : Type*} [Fintype I] [DecidableEq I]
    (index : I → ℤ) (x : I → ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, ∑ j, x i * x j * L (index i - index j).natAbs) ≤ 0 := by
  obtain ⟨σ, hσ, _⟩ := normalized_curvature_reconstruction c L normalized positive zeroValue recurrence
  have reconstruction : reconstructedLi (σ : Measure Circle) (L 1) = L :=
    funext fun n => (hσ.2 n).symm
  have h := reconstructed_li_conditionally_negative
    (σ : Measure Circle) (L 1) firstNonnegative index x hx
  rwa [reconstruction] at h

/-- End-to-end evolution of the same original Li-type sequence. Only normalized
curvature positivity, the original recurrence and nonnegative first coefficient
are supplied. The curvature measure, all exponential matrices, the evolving
probabilities, their weak continuity and all convolution roots are constructed. -/
theorem normalized_curvature_probability_evolution
    (c : ℤ → ℂ) (L : ℕ → ℝ) (normalized : c 0 = 1)
    (positive : ∀ N : ℕ, (toeplitzMatrix c N).PosSemidef)
    (zeroValue : L 0 = 0) (firstNonnegative : 0 ≤ L 1)
    (recurrence : ∀ n, 1 ≤ n →
      L (n + 1) - 2 * L n + L (n - 1) = 2 * L 1 * (c n).re) :
    ∃ σ : ProbabilityMeasure Circle,
      (∀ n : ℤ, circleMoment (σ : Measure Circle) n = c n) ∧
      (∀ n : ℕ, L n = reconstructedLi (σ : Measure Circle) (L 1) n) ∧
      ∃ ρ : ℝ≥0 → ProbabilityMeasure Circle,
        (∀ t n, circleMoment (ρ t : Measure Circle) n = (Real.exp (-(t : ℝ) * L n.natAbs) : ℂ)) ∧
        Continuous ρ ∧
        (ρ 0 : Measure Circle) = Measure.dirac 1 ∧
        (∀ s t, (ρ (s + t) : Measure Circle) = (ρ s : Measure Circle) ∗ₘ (ρ t : Measure Circle)) ∧
        (∀ η : ℝ≥0 → ProbabilityMeasure Circle,
          (∀ t n, circleMoment (η t : Measure Circle) n = (Real.exp (-(t : ℝ) * L n.natAbs) : ℂ)) → η = ρ) ∧
        (∀ t : ℝ≥0, ∀ k : ℕ, k ≠ 0 → ∃ ν : ProbabilityMeasure Circle,
          ((fun μ : Measure Circle => μ ∗ₘ (ν : Measure Circle))^[k]) (Measure.dirac 1) =
            (ρ t : Measure Circle)) := by
  obtain ⟨σ, hσ, _⟩ := normalized_curvature_reconstruction c L normalized positive zeroValue recurrence
  have reconstruction : reconstructedLi (σ : Measure Circle) (L 1) = L :=
    funext fun n => (hσ.2 n).symm
  have evolution := reconstructed_li_probability_semigroup (σ : Measure Circle) (L 1) firstNonnegative
  rw [reconstruction] at evolution
  obtain ⟨ρ, moments, continuous, initial, convolution, unique⟩ := evolution
  exact ⟨σ, hσ.1, hσ.2, ρ, moments, continuous, initial, convolution, unique,
    fun t k hk => semigroup_probability_roots ρ initial convolution t k hk⟩

/-- The constructed probability representation also bounds every original
coefficient quadratically. This controls the radius of the Li generating series;
it does not assume an arithmetic growth asymptotic. -/
theorem normalized_curvature_quadratic_bound
    (c : ℤ → ℂ) (L : ℕ → ℝ) (normalized : c 0 = 1)
    (positive : ∀ N : ℕ, (toeplitzMatrix c N).PosSemidef)
    (zeroValue : L 0 = 0) (firstNonnegative : 0 ≤ L 1)
    (recurrence : ∀ n, 1 ≤ n →
      L (n + 1) - 2 * L n + L (n - 1) = 2 * L 1 * (c n).re) :
    ∀ n : ℕ, 0 ≤ L n ∧ L n ≤ L 1 * (n : ℝ) ^ 2 := by
  obtain ⟨σ, hσ, _⟩ := normalized_curvature_reconstruction c L normalized positive zeroValue recurrence
  intro n
  rw [hσ.2 n]
  refine ⟨reconstructedLi_nonneg _ _ firstNonnegative n, ?_⟩
  have point (z : Circle) : Complex.normSq (geometricPolynomial n z) ≤ (n : ℝ) ^ 2 := by
    have hnorm : ‖geometricPolynomial n z‖ ≤ (n : ℝ) := by
      calc
        _ ≤ ∑ j ∈ Finset.range n, ‖(z : ℂ) ^ j‖ := norm_sum_le _ _
        _ = _ := by simp [norm_pow, Circle.norm_coe]
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (geometricPolynomial n z), Nat.cast_nonneg (α := ℝ) n]
  have hc : Continuous (fun z : Circle => Complex.normSq (geometricPolynomial n z)) := by
    unfold geometricPolynomial
    fun_prop
  have hint : Integrable (fun z : Circle => Complex.normSq (geometricPolynomial n z))
      (σ : Measure Circle) := by
    simpa using hc.continuousOn.integrableOn_compact (μ := (σ : Measure Circle)) isCompact_univ
  have integralBound : (∫ z : Circle, Complex.normSq (geometricPolynomial n z) ∂(σ : Measure Circle)) ≤
      (n : ℝ) ^ 2 := by
    calc
      _ ≤ ∫ _ : Circle, (n : ℝ) ^ 2 ∂(σ : Measure Circle) :=
        integral_mono hint (integrable_const _) point
      _ = _ := by simp
  exact mul_le_mul_of_nonneg_left integralBound firstNonnegative

#print axioms reconstructed_li_probability_semigroup
#print axioms semigroup_probability_roots
#print axioms normalized_curvature_conditionally_negative
#print axioms normalized_curvature_probability_evolution
#print axioms normalized_curvature_quadratic_bound

end D5.S3.Weil.Probability.LiCurvatureSchoenbergSemigroup
