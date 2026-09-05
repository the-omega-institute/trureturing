/- GID: D5/S3/Weil/ZetaBridge/WeilFullGramInertia
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilFullGramInertia
   mirror-E: none(waiver:actual-full-weil-gram-interface)
   anchors: []
   digest: Construct the actual mixed full Weil Gram, prove Hermitian symmetry and exact quadratic representation, and derive its RHLinalg negative index from the realized Burnol family. -/

import D5.S3.Weil.ZetaBridge.WeilEvaluationExactObservableRange
import D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
import D5.S3.SpectralTopology.FiniteSpectralLocalizer
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Actual full Weil Gram and observable negative inertia

The entries below are full absolutely convergent mixed zero sums of actual
Weil tests. The matrix convention is conjugate-linear in the row coefficient:
`G i j = W(basis j, basis i)`. Consequently `star a dot (G mulVec a)` is the
actual full convolution-square sum of the synthesized test.

Mirror reindexing proves Hermitian symmetry. The existing constructed common
Burnol packet then yields a genuine matrix whose negative is positive definite.
Its negative index uses the repository's spectral `RHLinalg.negIndex`, with
value the number of independent observable orbit channels. No prescribed
scalar matrix is substituted for the actual full Gram.

The final theorem assumes a valid finite separated off-line orbit frame. It
asserts neither existence of an off-line zero nor RH, and does not identify
this observable dimension with the multiplicity-expanded ambient index.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilFullGramInertia

open Matrix
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv
open D5.S3.Weil.ZetaBridge.FiniteMixedWeilMajorant
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open D5.S3.SpectralTopology.FiniteSpectralLocalizer
open RHLinalg
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

variable {ι : Type*} [Fintype ι]

/-- The actual full mixed Weil form, with multiplicity already in its summand. -/
def fullMixedWeilForm (Z : ZeroData) (g h : WeilTestFunction) : ℂ :=
  ∑' n : ℕ, mixedWeilSummand Z g h n

/-- Its ordinary absolutely convergent sum agrees with the canonical full
symmetric zero sum. -/
theorem fullMixedWeilForm_eq_zeroSum (Z : ZeroData) (g h : WeilTestFunction) :
    fullMixedWeilForm Z g h =
      zeroSum Z (convolve g (involution h))
        (symmetricConvergent_of_zeroData Z (convolve g (involution h))) := by
  rw [zeroSum_eq_tsum_of_zeroData]
  rfl

/-- Complex conjugation swaps the two actual tests after mirror reindexing. -/
theorem mixedWeilSummand_conj_mirror (Z : ZeroData)
    (g h : WeilTestFunction) (n : ℕ) :
    conj (mixedWeilSummand Z g h n) =
      mixedWeilSummand Z h g (mirrorIndex Z n) := by
  rw [mixedWeilSummand_factorization, mixedWeilSummand_factorization,
    mirrorIndex_multiplicity, mirrorIndex_gamma]
  simp only [map_mul, map_natCast, Complex.conj_conj]
  ring

/-- Hermitian symmetry of the full mixed form follows from an actual
permutation of the complete zero set, not a finite truncation assumption. -/
theorem fullMixedWeilForm_conj (Z : ZeroData) (g h : WeilTestFunction) :
    conj (fullMixedWeilForm Z g h) = fullMixedWeilForm Z h g := by
  unfold fullMixedWeilForm
  rw [Complex.conj_tsum]
  calc
    (∑' n : ℕ, conj (mixedWeilSummand Z g h n)) =
        ∑' n : ℕ, mixedWeilSummand Z h g (mirrorIndex Z n) :=
      tsum_congr (mixedWeilSummand_conj_mirror Z g h)
    _ = ∑' n : ℕ, mixedWeilSummand Z h g n :=
      (mirrorIndex Z).tsum_eq (mixedWeilSummand Z h g)

/-- The actual full Gram in the standard conjugate-linear row convention. -/
def fullWeilGram (Z : ZeroData) (basis : ι → WeilTestFunction) :
    Matrix ι ι ℂ :=
  fun i j => fullMixedWeilForm Z (basis j) (basis i)

/-- Every finite full mixed Weil Gram is Hermitian, with no sign assumption. -/
theorem fullWeilGram_isHermitian (Z : ZeroData) (basis : ι → WeilTestFunction) :
    (fullWeilGram Z basis).IsHermitian := by
  change (fullWeilGram Z basis)ᴴ = fullWeilGram Z basis
  ext i j
  change conj (fullMixedWeilForm Z (basis i) (basis j)) =
    fullMixedWeilForm Z (basis j) (basis i)
  exact fullMixedWeilForm_conj Z (basis i) (basis j)

/-- Absolute mixed summability justifies commuting the finite coefficient sums
with the complete zero sum. Every cross term is retained. -/
theorem fullZeroSum_finite_synthesis_expansion
    (Z : ZeroData) (basis : ι → WeilTestFunction) (a : ι → ℂ) :
    zeroSum Z (convolutionSquare (finiteWeilLinearCombination a basis))
      (symmetricConvergent_of_zeroData Z
        (convolutionSquare (finiteWeilLinearCombination a basis))) =
      ∑ i, ∑ j, (a i * conj (a j)) * fullMixedWeilForm Z (basis i) (basis j) := by
  have hs (i j : ι) : Summable (fun n : ℕ =>
      (a i * conj (a j)) * mixedWeilSummand Z (basis i) (basis j) n) :=
    (mixedWeilSummand_summable Z (basis i) (basis j)).mul_left _
  rw [zeroSum_eq_tsum_of_zeroData]
  simp_rw [zeroSummand_finite_synthesis_expansion]
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [tsum_mul_left]
  rfl

/-- Matrix evaluation equals the actual full Weil convolution-square sum. -/
theorem fullWeilGram_quadratic (Z : ZeroData)
    (basis : ι → WeilTestFunction) (a : ι → ℂ) :
    star a ⬝ᵥ ((fullWeilGram Z basis) *ᵥ a) =
      zeroSum Z (convolutionSquare (finiteWeilLinearCombination a basis))
        (symmetricConvergent_of_zeroData Z
          (convolutionSquare (finiteWeilLinearCombination a basis))) := by
  rw [fullZeroSum_finite_synthesis_expansion]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.star_apply,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [fullWeilGram]
  ring

/-- Strict negativity of the realized full form gives positive definiteness of
the negative of its actual Hermitian Gram. -/
theorem neg_fullWeilGram_posDef_of_strictNegative
    (Z : ZeroData) (basis : ι → WeilTestFunction)
    (hneg : ∀ a : ι → ℂ, a ≠ 0 →
      (zeroSum Z (convolutionSquare (finiteWeilLinearCombination a basis))
        (symmetricConvergent_of_zeroData Z
          (convolutionSquare (finiteWeilLinearCombination a basis)))).re < 0) :
    (-fullWeilGram Z basis).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (fullWeilGram_isHermitian Z basis).neg
  intro a ha
  apply Complex.pos_iff.mpr
  constructor
  · rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re, fullWeilGram_quadratic]
    exact neg_pos.mpr (hneg a ha)
  · exact ((fullWeilGram_isHermitian Z basis).neg.im_star_dotProduct_mulVec_self a).symm

/-- The repository spectral inertia equals the number of independent actual
test coordinates whenever the complete form is strictly negative on them. -/
theorem fullWeilGram_negIndex_of_strictNegative
    (Z : ZeroData) (basis : ι → WeilTestFunction)
    (hneg : ∀ a : ι → ℂ, a ≠ 0 →
      (zeroSum Z (convolutionSquare (finiteWeilLinearCombination a basis))
        (symmetricConvergent_of_zeroData Z
          (convolutionSquare (finiteWeilLinearCombination a basis)))).re < 0) :
    negIndex (fullWeilGram_isHermitian Z basis) = Fintype.card ι := by
  classical
  let hG := fullWeilGram_isHermitian Z basis
  have hpositive := neg_fullWeilGram_posDef_of_strictNegative Z basis hneg
  calc
    negIndex hG = posIndex hG.neg := (posIndex_neg_eq_negIndex hG).symm
    _ = Fintype.card ι := by
      unfold posIndex
      rw [Finset.filter_eq_self.2]
      · exact Finset.card_univ
      · intro i _
        exact hpositive.eigenvalues_pos i

/-- A valid finite observable off-line frame has an actual full Weil Gram with
exactly as many negative eigenvalues as independent orbit channels. The basis
and common localization depth are constructed by the existing Burnol theorem;
no remainder hypothesis is supplied here. -/
theorem exists_actual_full_weil_gram_with_exact_negative_index
    {Z : ZeroData} [DecidableEq ι] (F : FiniteEvenWeilOrbitFrame Z ι) :
    ∃ basis : ι → WeilTestFunction,
      Function.Injective (fun a : ι → ℂ => finiteWeilLinearCombination a basis) ∧
      (-fullWeilGram Z basis).PosDef ∧
      negIndex (fullWeilGram_isHermitian Z basis) = Fintype.card ι := by
  obtain ⟨basis, hinj, hneg⟩ := finite_multiOrbit_full_weil_negative_family F
  exact ⟨basis, hinj, neg_fullWeilGram_posDef_of_strictNegative Z basis hneg,
    fullWeilGram_negIndex_of_strictNegative Z basis hneg⟩

#print axioms fullMixedWeilForm_conj
#print axioms fullWeilGram_isHermitian
#print axioms fullWeilGram_quadratic
#print axioms neg_fullWeilGram_posDef_of_strictNegative
#print axioms fullWeilGram_negIndex_of_strictNegative
#print axioms exists_actual_full_weil_gram_with_exact_negative_index

end D5.S3.Weil.ZetaBridge.WeilFullGramInertia
