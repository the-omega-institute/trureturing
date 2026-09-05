/- GID: D5/S3/Weil/ZetaBridge/QuantitativeMultiOrbitWeilNegativeCertificate
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/QuantitativeMultiOrbitWeilNegativeCertificate
   mirror-E: none(waiver:canonical-zeta-observer-interface)
   anchors: []
   digest: Prove that a uniform quadratic remainder below the finite odd margin preserves an entire multi-orbit negative test family. -/

import D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
import D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
import Mathlib.Tactic

/-!
# Quantitative multi-orbit Weil negative certificates

The finite odd interpolation node gives an exact negative target form

`-4 * sum_i multiplicity_i * |a_i|^2`

on a coefficient space of independently observable orbit channels.  The full
Weil zero sum also contains every other zero.  This node isolates the exact
remaining analytic obligation as a uniform quadratic remainder estimate.

A reusable perturbation theorem proves that if the remainder norm is strictly
smaller than the least target weight, then every nonzero coefficient vector
still yields a strictly negative full Weil square.  Because the explicit
interpolation synthesis is injective, this is a genuine finite-dimensional
family of distinct admissible tests, rather than a collection of unrelated
single-orbit witnesses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate

open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open scoped BigOperators

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared Euclidean energy of a finite complex coefficient vector. -/
def finiteComplexEnergy (a : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (a i)

/-- Finite coefficient energy is nonnegative. -/
theorem finiteComplexEnergy_nonneg (a : ι → ℂ) :
    0 ≤ finiteComplexEnergy a := by
  unfold finiteComplexEnergy
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (a i)

/-- Finite coefficient energy is strictly positive away from zero. -/
theorem finiteComplexEnergy_pos {a : ι → ℂ} (ha : a ≠ 0) :
    0 < finiteComplexEnergy a := by
  have hexists : ∃ i, a i ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply ha
    funext i
    exact hnone i
  obtain ⟨i, hi⟩ := hexists
  unfold finiteComplexEnergy
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (a j))
    ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

/-- A weighted negative diagonal quadratic form. -/
def negativeWeightedDiagonalQuadratic
    (weight : ι → ℝ) (a : ι → ℂ) : ℝ :=
  -∑ i, weight i * Complex.normSq (a i)

/-- A positive lower bound on all diagonal weights gives a uniform negative
margin. -/
theorem negativeWeightedDiagonalQuadratic_le_margin
    (weight : ι → ℝ) (margin : ℝ)
    (hweight : ∀ i, margin ≤ weight i)
    (a : ι → ℂ) :
    negativeWeightedDiagonalQuadratic weight a ≤
      -margin * finiteComplexEnergy a := by
  have hsum :
      margin * finiteComplexEnergy a ≤
        ∑ i, weight i * Complex.normSq (a i) := by
    rw [finiteComplexEnergy, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hweight i)
        (Complex.normSq_nonneg (a i))
  unfold negativeWeightedDiagonalQuadratic
  linarith

/-- General finite-dimensional perturbation theorem missing from the local
matrix API: a quadratic remainder with norm below a strict diagonal margin
preserves negative definiteness on the whole coefficient space. -/
theorem strictNegative_of_uniformQuadraticRemainder
    (weight : ι → ℝ) (margin epsilon : ℝ)
    (hmargin : 0 < margin)
    (hweight : ∀ i, margin ≤ weight i)
    (hepsilon : epsilon < margin)
    (full remainder : (ι → ℂ) → ℝ)
    (hdecomposition : ∀ a,
      full a = negativeWeightedDiagonalQuadratic weight a + remainder a)
    (hremainder : ∀ a,
      |remainder a| ≤ epsilon * finiteComplexEnergy a) :
    ∀ a, a ≠ 0 → full a < 0 := by
  intro a ha
  have henergy : 0 < finiteComplexEnergy a := finiteComplexEnergy_pos ha
  have htarget :=
    negativeWeightedDiagonalQuadratic_le_margin weight margin hweight a
  have hrem : remainder a ≤ epsilon * finiteComplexEnergy a :=
    (le_abs_self (remainder a)).trans (hremainder a)
  calc
    full a = negativeWeightedDiagonalQuadratic weight a + remainder a :=
      hdecomposition a
    _ ≤ -margin * finiteComplexEnergy a +
        epsilon * finiteComplexEnergy a := add_le_add htarget hrem
    _ = (epsilon - margin) * finiteComplexEnergy a := by ring
    _ < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hepsilon) henergy

/-- The exact negative target quadratic supplied by the selected observable
orbit channels. -/
def frameOddTargetQuadratic
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ) : ℝ :=
  -4 * ∑ i,
    (Z.multiplicity (F.index i) : ℝ) * Complex.normSq (a i)

/-- The actual full symmetric zero-sum quadratic of the synthesized admissible
Weil test. -/
noncomputable def synthesizedFullWeilQuadratic
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ) : ℝ :=
  (zeroSum Z (convolutionSquare (frameOddSynthesis F a))
    (symmetricConvergent_of_zeroData Z
      (convolutionSquare (frameOddSynthesis F a)))).re

/-- Everything in the actual zero sum beyond the exact selected-orbit odd
target. -/
noncomputable def synthesizedWeilRemainder
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ) : ℝ :=
  synthesizedFullWeilQuadratic F a - frameOddTargetQuadratic F a

/-- A uniform operator-norm-style bound for the full Weil remainder on the
finite synthesized coefficient space. -/
def HasUniformMultiOrbitRemainderBound
    (F : FiniteEvenWeilOrbitFrame Z ι) (epsilon : ℝ) : Prop :=
  ∀ a : ι → ℂ,
    |synthesizedWeilRemainder F a| ≤ epsilon * finiteComplexEnergy a

/-- The explicit finite synthesis is injective because reduced odd evaluation
is its right inverse. -/
theorem frameOddSynthesis_injective
    (F : FiniteEvenWeilOrbitFrame Z ι) :
    Function.Injective (frameOddSynthesis F) := by
  intro a b hab
  funext i
  have hread := congrArg (fun g : WeilTestFunction => frameOddReadout F g i) hab
  simpa only [frameOddSynthesis_readout] using hread

/-- The target quadratic is the generic negative weighted diagonal with weight
`4 * multiplicity`. -/
theorem frameOddTargetQuadratic_eq_weighted
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ) :
    frameOddTargetQuadratic F a =
      negativeWeightedDiagonalQuadratic
        (fun i => 4 * (Z.multiplicity (F.index i) : ℝ)) a := by
  unfold frameOddTargetQuadratic negativeWeightedDiagonalQuadratic
  rw [Finset.mul_sum]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A positive multiplicity floor gives the exact target margin. -/
theorem frameOddTargetQuadratic_le_massFloor
    (F : FiniteEvenWeilOrbitFrame Z ι)
    (massFloor : ℝ)
    (hmass : ∀ i, massFloor ≤ (Z.multiplicity (F.index i) : ℝ))
    (a : ι → ℂ) :
    frameOddTargetQuadratic F a ≤
      -(4 * massFloor) * finiteComplexEnergy a := by
  rw [frameOddTargetQuadratic_eq_weighted]
  apply negativeWeightedDiagonalQuadratic_le_margin
  intro i
  nlinarith [hmass i]

/-- Complete quantitative certificate data.  The only analytic input is the
uniform remainder estimate; all finite interpolation, multiplicity margins,
and nonvacuity are already internal. -/
structure QuantitativeMultiOrbitCertificate
    (F : FiniteEvenWeilOrbitFrame Z ι) where
  epsilon : ℝ
  massFloor : ℝ
  massFloor_pos : 0 < massFloor
  massFloor_le : ∀ i,
    massFloor ≤ (Z.multiplicity (F.index i) : ℝ)
  remainderBound : HasUniformMultiOrbitRemainderBound F epsilon
  strictMargin : epsilon < 4 * massFloor

/-- A quantitative certificate preserves strict negativity for every nonzero
coefficient vector. -/
theorem quantitativeMultiOrbit_strictly_negative
    (F : FiniteEvenWeilOrbitFrame Z ι)
    (C : QuantitativeMultiOrbitCertificate F) :
    ∀ a : ι → ℂ, a ≠ 0 → synthesizedFullWeilQuadratic F a < 0 := by
  apply strictNegative_of_uniformQuadraticRemainder
    (weight := fun i => 4 * (Z.multiplicity (F.index i) : ℝ))
    (margin := 4 * C.massFloor)
    (epsilon := C.epsilon)
    (full := synthesizedFullWeilQuadratic F)
    (remainder := synthesizedWeilRemainder F)
  · positivity
  · intro i
    nlinarith [C.massFloor_le i]
  · exact C.strictMargin
  · intro a
    unfold synthesizedWeilRemainder
    rw [frameOddTargetQuadratic_eq_weighted]
    ring
  · exact C.remainderBound

/-- The resulting family is genuinely multi-dimensional: distinct coefficient
vectors synthesize distinct admissible tests, and every nonzero synthesized
test has negative full Weil zero sum. -/
theorem quantitative_multiOrbit_weil_negative_certificate
    (F : FiniteEvenWeilOrbitFrame Z ι)
    (C : QuantitativeMultiOrbitCertificate F) :
    Function.Injective (frameOddSynthesis F) ∧
      ∀ a : ι → ℂ, a ≠ 0 →
        (zeroSum Z (convolutionSquare (frameOddSynthesis F a))
          (symmetricConvergent_of_zeroData Z
            (convolutionSquare (frameOddSynthesis F a)))).re < 0 := by
  refine ⟨frameOddSynthesis_injective F, ?_⟩
  intro a ha
  exact quantitativeMultiOrbit_strictly_negative F C a ha

/-- In particular, every interpolation basis direction remains a strict full
Weil negative witness under the same uniform certificate. -/
theorem quantitative_basis_tests_negative
    (F : FiniteEvenWeilOrbitFrame Z ι)
    (C : QuantitativeMultiOrbitCertificate F) (i : ι) :
    synthesizedFullWeilQuadratic F (frameDelta i) < 0 := by
  apply quantitativeMultiOrbit_strictly_negative F C
  intro hzero
  have h := congrFun hzero i
  simp [frameDelta] at h

#print axioms strictNegative_of_uniformQuadraticRemainder
#print axioms frameOddSynthesis_injective
#print axioms quantitativeMultiOrbit_strictly_negative
#print axioms quantitative_multiOrbit_weil_negative_certificate

end D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
