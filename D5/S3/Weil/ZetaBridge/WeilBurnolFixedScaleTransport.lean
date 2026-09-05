/- GID: D5/S3/Weil/ZetaBridge/WeilBurnolFixedScaleTransport
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilBurnolFixedScaleTransport
   mirror-E: none(waiver:support-controlled-fixed-scale-transport)
   anchors: []
   digest: Realize the full negative family in one common support window and transport its quantitative margin to the existing prime-Archimedean multiplier with the pole energy retained exactly. -/

import D5.S3.Weil.ZetaBridge.WeilBurnolSupportBudget
import D5.S3.Weil.ZetaBridge.WeilFullGramUniformRemainder
import D5.S3.Weil.ZetaBridge.FixedScaleWeilQuadraticForm

/-!
# Support-controlled full negativity and arithmetic transport

The support window is common to all coefficient vectors of the chosen family.
The completed multiplier is the repository's existing fixedScaleMultiplier.
The nonnegative rank-one pole energy is subtracted exactly, so it strengthens
the negative multiplier bound. No prime-side positivity is assumed.

The arithmetic equalities explicitly retain the ArchimedeanConvergent witness
required by the existing fixed-scale interface in this branch. The zero-side
family and its common support window need no such additional hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilBurnolFixedScaleTransport

open Set MeasureTheory Matrix
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaBridge.WeilFullGramInertia
open D5.S3.Weil.ZetaBridge.WeilFullGramUniformRemainder
open D5.S3.Weil.ZetaBridge.WeilBurnolSupportBudget
open D5.S3.Weil.ZetaBridge.FixedScaleWeilQuadraticForm
open RHLinalg
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

/-- The existing fixed-scale identity isolates the completed multiplier by
subtracting the exact rank-one pole energy. -/
theorem fixedScale_multiplier_re_eq_full_minus_pole
    (Z : ZeroData) (f : WeilTestFunction) (L : ℝ)
    (hsupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-L) L)
    (hArch : ArchimedeanConvergent (convolutionSquare f)) :
    ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ xi : ℝ, (fixedScaleMultiplier L xi : ℂ) *
        (Complex.normSq (fourierLaplace f xi) : ℂ))).re =
      (zeroSum Z (convolutionSquare f)
        (symmetricConvergent_of_zeroData Z (convolutionSquare f))).re -
      2 * Complex.normSq
        (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * f x) := by
  have hformula := (fixed_scale_weil_quadratic_form Z f L hsupport
    (symmetricConvergent_of_zeroData Z (convolutionSquare f)) hArch).1
  have hre := congrArg Complex.re hformula
  rw [Complex.add_re] at hre
  have hpole : (2 * (Complex.normSq
      (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * f x) : ℂ)).re =
      2 * Complex.normSq
        (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * f x) := by
    simp
  rw [hpole] at hre
  linarith

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : FiniteEvenWeilOrbitFrame Z ι)

/-- A single positive support radius contains every member of a genuinely
finite-dimensional family with a uniform full negative margin and exact inertia.
The basis, radius and localization depth are constructed from the given frame. -/
theorem exists_support_controlled_full_negative_family
    (F : FiniteEvenWeilOrbitFrame Z ι)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta4 : delta < 4) :
    ∃ L : ℝ, 0 < L ∧ ∃ basis : ι → WeilTestFunction,
      Function.Injective (fun a : ι → ℂ => finiteWeilLinearCombination a basis) ∧
      (-fullWeilGram Z basis).PosDef ∧
      negIndex (fullWeilGram_isHermitian Z basis) = Fintype.card ι ∧
      ∀ a : ι → ℂ,
        tsupport (finiteWeilLinearCombination a basis : ℝ → ℂ) ⊆ Icc (-L) L ∧
        (star a ⬝ᵥ ((fullWeilGram Z basis) *ᵥ a)).re ≤
          -(4 - delta) * finiteComplexEnergy a := by
  let P := chosenOrbitBurnolPacket F
  obtain ⟨B, K, hB, hK, _, _, hsupport⟩ := exists_burnol_linear_support_budget F P
  obtain ⟨hmargin, N, hN⟩ :=
    eventually_burnolGram_uniform_negative_margin F P delta hdelta hdelta4
  let L : ℝ := ((N : ℝ) + 1) * B + K
  have hL : 0 < L := by dsimp [L]; positivity
  have hnegative : ∀ a : ι → ℂ, a ≠ 0 →
      (zeroSum Z (convolutionSquare
        (finiteWeilLinearCombination a (burnolBasis F P N)))
        (symmetricConvergent_of_zeroData Z (convolutionSquare
          (finiteWeilLinearCombination a (burnolBasis F P N))))).re < 0 := by
    intro a ha
    have hbound := hN N le_rfl a
    rw [fullWeilGram_quadratic] at hbound
    exact lt_of_le_of_lt hbound
      (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hmargin) (finiteComplexEnergy_pos ha))
  refine ⟨L, hL, burnolBasis F P N, burnolSynthesis_injective F P N,
    neg_fullWeilGram_posDef_of_strictNegative Z (burnolBasis F P N) hnegative,
    fullWeilGram_negIndex_of_strictNegative Z (burnolBasis F P N) hnegative, ?_⟩
  intro a
  exact ⟨hsupport N a, hN N le_rfl a⟩

/-- The derived full margin transports to the completed multiplier at every
sufficiently large depth, using a linear support budget uniform in coefficients.
The pole contribution remains explicit and is subtracted with its exact sign. -/
theorem eventually_burnol_fixedScale_multiplier_margin
    (P : OrbitBurnolPacket F) (delta : ℝ)
    (hdelta : 0 < delta) (hdelta4 : delta < 4) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → ∀ a : ι → ℂ,
        tsupport (burnolSynthesis F P N a : ℝ → ℂ) ⊆
          Icc (-(((N : ℝ) + 1) * B + K)) (((N : ℝ) + 1) * B + K) ∧
        ∀ hArch : ArchimedeanConvergent (convolutionSquare (burnolSynthesis F P N a)),
          ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ xi : ℝ, (fixedScaleMultiplier (((N : ℝ) + 1) * B + K) xi : ℂ) *
              (Complex.normSq (fourierLaplace (burnolSynthesis F P N a) xi) : ℂ))).re ≤
            -(4 - delta) * finiteComplexEnergy a -
            2 * Complex.normSq
              (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * burnolSynthesis F P N a x) := by
  obtain ⟨B, K, hB, hK, _, _, hsupport⟩ := exists_burnol_linear_support_budget F P
  obtain ⟨_, N₀, hN₀⟩ :=
    eventually_burnolGram_uniform_negative_margin F P delta hdelta hdelta4
  refine ⟨B, K, hB, hK, N₀, ?_⟩
  intro N hN a
  refine ⟨hsupport N a, ?_⟩
  intro hArch
  rw [fixedScale_multiplier_re_eq_full_minus_pole Z (burnolSynthesis F P N a)
    (((N : ℝ) + 1) * B + K) (hsupport N a) hArch]
  have hbound := hN₀ N hN a
  rw [fullWeilGram_quadratic] at hbound
  exact sub_le_sub_right hbound _

#print axioms fixedScale_multiplier_re_eq_full_minus_pole
#print axioms exists_support_controlled_full_negative_family
#print axioms eventually_burnol_fixedScale_multiplier_margin

end D5.S3.Weil.ZetaBridge.WeilBurnolFixedScaleTransport
