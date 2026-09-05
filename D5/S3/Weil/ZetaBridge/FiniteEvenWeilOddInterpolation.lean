/- GID: D5/S3/Weil/ZetaBridge/FiniteEvenWeilOddInterpolation
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/FiniteEvenWeilOddInterpolation
   mirror-E: none(waiver:canonical-zeta-observer-interface)
   anchors: []
   digest: Construct a finite linear right inverse for reduced odd Weil evaluations and compute its exact negative Gram inertia. -/

import D5.S3.Weil.ZetaBridge.FiniteMirrorReducedWeilFactorization
import D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation
import D5.S3.SpectralTopology.FiniteSpectralLocalizer
import Mathlib.Tactic

/-!
# Finite simultaneous interpolation of observable odd zero channels

An admissible scalar even Weil test cannot span the full
multiplicity-expanded mirror-odd Hilbert sector.  It can, however, prescribe
independent differences between finitely many sign-separated conjugate
spectral pairs.  This node packages the exact finite separation data, invokes
the existing even Paley--Wiener interpolation theorem, and upgrades its
existential conclusion to an explicit finite linear synthesis map.

The basis tests have a concrete reduced odd Gram matrix
`-4 * diagonal(multiplicity)`.  Its spectral negative index is exactly the
number of independently observable orbit channels.  Analytic multiplicity
sets the negative weight and margin; it does not create additional scalar
observer directions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation

open Matrix Finset
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.FiniteMirrorReducedWeilFactorization
open D5.S3.SpectralTopology.FiniteSpectralLocalizer
open RHLinalg
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

/-- A finite family of nonreal off-line orbit channels together with the exact
node certificate needed by even finite interpolation.  `inl i` represents
`gamma_i`; `inr i` represents `conj gamma_i`. -/
structure FiniteEvenWeilOrbitFrame
    (Z : ZeroData) (ι : Type*) [Fintype ι] where
  index : ι → ℕ
  offLine : ∀ i, (Z.zero (index i)).re ≠ criticalAbscissa
  conjugateMove : ∀ i, Z.conjugation (index i) ≠ index i
  nodes : Finset ℂ
  nodeEquiv : Sum ι ι ≃ {z : ℂ // z ∈ nodes}
  plusNode : ∀ i,
    (nodeEquiv (Sum.inl i)).1 = Z.gamma (index i)
  minusNode : ∀ i,
    (nodeEquiv (Sum.inr i)).1 = conj (Z.gamma (index i))
  signSeparated : ∀ ⦃z w : ℂ⦄,
    z ∈ nodes → w ∈ nodes → z ≠ w → z ≠ -w

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Values prescribed on the two nodes of every reduced odd channel. -/
noncomputable def frameSignedAssignment
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ)
    (z : {w : ℂ // w ∈ F.nodes}) : ℂ :=
  match F.nodeEquiv.symm z with
  | Sum.inl i => a i
  | Sum.inr i => -a i

/-- One even Weil test simultaneously realizes arbitrary signed data on all
frame channels. -/
theorem exists_even_weil_frame_interpolant
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ) :
    ∃ g : WeilTestFunction,
      ∀ i,
        fourierLaplace g (Z.gamma (F.index i)) = a i ∧
        fourierLaplace g (conj (Z.gamma (F.index i))) = -a i := by
  obtain ⟨g, hg⟩ := even_weilTestFunction_finite_interpolation
    F.nodes F.signSeparated (frameSignedAssignment F a)
  refine ⟨g, ?_⟩
  intro i
  constructor
  · have h := hg (F.nodeEquiv (Sum.inl i))
    simpa [frameSignedAssignment, F.plusNode i] using h
  · have h := hg (F.nodeEquiv (Sum.inr i))
    simpa [frameSignedAssignment, F.minusNode i] using h

/-- The independently observable odd value of one four-point orbit channel. -/
noncomputable def frameOddReadout
    (F : FiniteEvenWeilOrbitFrame Z ι)
    (g : WeilTestFunction) (i : ι) : ℂ :=
  oddSpectralChannel
    (fourierLaplace g (Z.gamma (F.index i)))
    (fourierLaplace g (conj (Z.gamma (F.index i))))

/-- Arbitrary reduced odd vectors are reachable by scalar even Weil tests. -/
theorem exists_even_weil_odd_interpolant
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ) :
    ∃ g : WeilTestFunction, ∀ i, frameOddReadout F g i = a i := by
  obtain ⟨g, hg⟩ := exists_even_weil_frame_interpolant F a
  refine ⟨g, ?_⟩
  intro i
  rw [frameOddReadout, oddSpectralChannel, (hg i).1, (hg i).2]
  ring

/-- Kronecker data for the interpolation basis. -/
def frameDelta (i j : ι) : ℂ := if j = i then 1 else 0

/-- A chosen even Weil test whose reduced odd readout is the `i`th coordinate
vector. -/
noncomputable def frameOddBasisTest
    (F : FiniteEvenWeilOrbitFrame Z ι) (i : ι) : WeilTestFunction :=
  Classical.choose (exists_even_weil_odd_interpolant F (frameDelta i))

@[simp]
theorem frameOddBasisTest_readout
    (F : FiniteEvenWeilOrbitFrame Z ι) (i j : ι) :
    frameOddReadout F (frameOddBasisTest F i) j = frameDelta i j :=
  Classical.choose_spec
    (exists_even_weil_odd_interpolant F (frameDelta i)) j

/-- Odd readout commutes with explicit finite Weil linear combinations. -/
theorem frameOddReadout_finiteWeilLinearCombination
    (F : FiniteEvenWeilOrbitFrame Z ι)
    {κ : Type*} [Fintype κ]
    (a : κ → ℂ) (g : κ → WeilTestFunction) (i : ι) :
    frameOddReadout F (finiteWeilLinearCombination a g) i =
      ∑ k, a k * frameOddReadout F (g k) i := by
  rw [frameOddReadout, oddSpectralChannel,
    fourierLaplace_finiteWeilLinearCombination,
    fourierLaplace_finiteWeilLinearCombination]
  calc
    ((∑ k, a k * fourierLaplace (g k) (Z.gamma (F.index i))) -
        ∑ k, a k * fourierLaplace (g k)
          (conj (Z.gamma (F.index i))))) / 2 =
      ∑ k,
        (a k * fourierLaplace (g k) (Z.gamma (F.index i)) -
          a k * fourierLaplace (g k)
            (conj (Z.gamma (F.index i)))) / 2 := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_div]
    _ = ∑ k, a k *
        ((fourierLaplace (g k) (Z.gamma (F.index i)) -
          fourierLaplace (g k) (conj (Z.gamma (F.index i)))) / 2) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = _ := by
      rfl

/-- Explicit linear synthesis from reduced odd coordinates to even Weil tests. -/
noncomputable def frameOddSynthesis
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ) : WeilTestFunction :=
  finiteWeilLinearCombination a (frameOddBasisTest F)

/-- The finite synthesis is a right inverse to reduced odd evaluation. -/
theorem frameOddSynthesis_readout
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ) (j : ι) :
    frameOddReadout F (frameOddSynthesis F a) j = a j := by
  rw [frameOddSynthesis,
    frameOddReadout_finiteWeilLinearCombination]
  simp only [frameOddBasisTest_readout, frameDelta]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

/-- The reduced negative sesquilinear form carried by the observable odd
channels. -/
noncomputable def frameOddSesquilinear
    (F : FiniteEvenWeilOrbitFrame Z ι)
    (g h : WeilTestFunction) : ℂ :=
  -4 * ∑ k,
    (Z.multiplicity (F.index k) : ℂ) *
      conj (frameOddReadout F g k) * frameOddReadout F h k

/-- The concrete Gram matrix of the interpolation basis. -/
noncomputable def frameOddGram
    (F : FiniteEvenWeilOrbitFrame Z ι) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => -(4 * (Z.multiplicity (F.index i) : ℂ))

/-- The chosen Weil interpolation basis realizes the exact diagonal reduced
odd Gram matrix. -/
theorem frameOddBasisTest_gram
    (F : FiniteEvenWeilOrbitFrame Z ι) (i j : ι) :
    frameOddSesquilinear F (frameOddBasisTest F i)
      (frameOddBasisTest F j) = frameOddGram F i j := by
  classical
  rw [frameOddSesquilinear, frameOddGram, Matrix.diagonal_apply]
  simp only [frameOddBasisTest_readout, frameDelta]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single i]
    · simp
      ring
    · intro k _ hki
      simp [hki]
    · simp
  · have hsum :
      (∑ k,
        (Z.multiplicity (F.index k) : ℂ) *
          conj (if k = i then 1 else 0) *
          (if k = j then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hki : k = i
      · subst k
        simp [hij]
      · simp [hki]
    rw [hsum]
    simp [hij]

/-- The reduced odd Gram is Hermitian. -/
theorem frameOddGram_isHermitian
    (F : FiniteEvenWeilOrbitFrame Z ι) :
    (frameOddGram F).IsHermitian := by
  rw [frameOddGram, Matrix.isHermitian_diagonal_iff]
  intro i
  simp

/-- The negative of the reduced odd Gram is positive definite. -/
theorem neg_frameOddGram_posDef
    (F : FiniteEvenWeilOrbitFrame Z ι) :
    (-frameOddGram F).PosDef := by
  rw [show -frameOddGram F =
      Matrix.diagonal (fun i => (4 * Z.multiplicity (F.index i) : ℂ)) by
    ext i j
    simp [frameOddGram]]
  apply Matrix.PosDef.diagonal
  intro i
  simp only [Complex.ofReal_re, Nat.cast_ofNat]
  exact mul_pos (by norm_num)
    (Nat.cast_pos.mpr (Z.multiplicity_pos (F.index i)))

/-- The spectral negative index of the observable odd Gram is exactly the
number of independently interpolated orbit channels. -/
theorem frameOddGram_negIndex
    (F : FiniteEvenWeilOrbitFrame Z ι) :
    negIndex (frameOddGram_isHermitian F) = Fintype.card ι := by
  let hG := frameOddGram_isHermitian F
  have hNegative := neg_frameOddGram_posDef F
  calc
    negIndex hG = posIndex hG.neg :=
      (posIndex_neg_eq_negIndex hG).symm
    _ = Fintype.card ι := by
      unfold posIndex
      rw [Finset.filter_eq_self.2]
      · exact Finset.card_univ
      · intro i _
        exact hNegative.eigenvalues_pos i

/-- The explicit synthesis realizes the expected multiplicity-weighted odd
energy on the selected orbit family. -/
theorem frameOddSynthesis_orbitOddEnergy
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ) :
    finiteOrbitOddEnergy Z (frameOddSynthesis F a) F.index =
      4 * ∑ i,
        (Z.multiplicity (F.index i) : ℝ) * Complex.normSq (a i) := by
  unfold finiteOrbitOddEnergy orbitOddEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show oddSpectralChannel
      (fourierLaplace (frameOddSynthesis F a) (Z.gamma (F.index i)))
      (fourierLaplace (frameOddSynthesis F a)
        (conj (Z.gamma (F.index i)))) = a i by
    exact frameOddSynthesis_readout F a i]
  ring

/-- Complete finite observable-odd interpolation package. -/
theorem finite_even_weil_odd_interpolation_spec
    (F : FiniteEvenWeilOrbitFrame Z ι) :
    (∀ a : ι → ℂ, ∀ i,
      frameOddReadout F (frameOddSynthesis F a) i = a i) ∧
    (∀ i j,
      frameOddSesquilinear F (frameOddBasisTest F i)
        (frameOddBasisTest F j) = frameOddGram F i j) ∧
    negIndex (frameOddGram_isHermitian F) = Fintype.card ι :=
  ⟨frameOddSynthesis_readout F,
    frameOddBasisTest_gram F,
    frameOddGram_negIndex F⟩

#print axioms exists_even_weil_frame_interpolant
#print axioms frameOddSynthesis_readout
#print axioms frameOddBasisTest_gram
#print axioms frameOddGram_negIndex
#print axioms frameOddSynthesis_orbitOddEnergy

end D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
