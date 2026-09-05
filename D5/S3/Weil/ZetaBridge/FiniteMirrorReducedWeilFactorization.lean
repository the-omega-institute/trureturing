/- GID: D5/S3/Weil/ZetaBridge/FiniteMirrorReducedWeilFactorization
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/FiniteMirrorReducedWeilFactorization
   mirror-E: none(waiver:canonical-zeta-observer-interface)
   anchors: []
   digest: Factor finite convolution-square zero sums through the reflection-reduced mirror form and aggregate exact even-minus-odd orbit energies. -/

import D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
import D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition
import Mathlib.Tactic

/-!
# Finite mirror-reduced Weil factorization

Scalar even Weil tests live on the functional-equation-reflection quotient of
the zero set.  This node keeps one scalar value per distinct zero index, records
reflection-evenness as a subtype condition, and retains analytic multiplicity
as a positive weight in the form rather than as independent coordinates.

The finite convolution-square zero sum is identified exactly with a weighted
same-height-mirror form on this reduced observable space.  A second theorem
sums the existing four-point orbit decomposition over any finite family and
produces a finite positive-even minus positive-odd energy identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.FiniteMirrorReducedWeilFactorization

open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition
open D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv
open scoped BigOperators ComplexConjugate

/-- Same-height reflection restricted to a finite symmetric window. -/
noncomputable def windowMirrorIndex (Z : ZeroData) (T : ℝ) :
    Equiv.Perm (WindowZeroIndex Z T) where
  toFun n := by
    refine ⟨mirrorIndex Z n.1, ?_⟩
    have hR : Z.reflection n.1 ∈ Z.symmetricIndices T :=
      (Z.reflection_mem_symmetricIndices (T := T) (n := n.1)).2 n.2
    exact (Z.conjugation_mem_symmetricIndices
      (T := T) (n := Z.reflection n.1)).2 hR
  invFun n := by
    refine ⟨mirrorIndex Z n.1, ?_⟩
    have hR : Z.reflection n.1 ∈ Z.symmetricIndices T :=
      (Z.reflection_mem_symmetricIndices (T := T) (n := n.1)).2 n.2
    exact (Z.conjugation_mem_symmetricIndices
      (T := T) (n := Z.reflection n.1)).2 hR
  left_inv n := Subtype.ext (mirrorIndex_involutive Z n.1)
  right_inv n := Subtype.ext (mirrorIndex_involutive Z n.1)

@[simp]
theorem windowMirrorIndex_val (Z : ZeroData) (T : ℝ)
    (n : WindowZeroIndex Z T) :
    (windowMirrorIndex Z T n).1 = mirrorIndex Z n.1 := rfl

/-- Finite distinct-zero vectors satisfying the exact reflection-even
constraint imposed by scalar even Weil tests. -/
def FiniteReflectionEvenVector (Z : ZeroData) (T : ℝ) :=
  {v : WindowZeroIndex Z T → ℂ // ReflectionEvenOnWindow Z T v}

/-- The canonical reduced vector produced by one Weil test. -/
noncomputable def finiteWeilReducedEvaluation
    (Z : ZeroData) (T : ℝ) (g : WeilTestFunction) :
    FiniteReflectionEvenVector Z T :=
  ⟨finiteWeilIndexEvaluation Z T g,
    finiteWeilIndexEvaluation_mem_observable Z T g⟩

/-- The multiplicity-weighted mirror sesquilinear form on the finite reduced
observable space. -/
noncomputable def finiteMirrorReducedForm
    (Z : ZeroData) (T : ℝ)
    (v w : FiniteReflectionEvenVector Z T) : ℂ :=
  ∑ n : WindowZeroIndex Z T,
    (Z.multiplicity n.1 : ℂ) * v.1 n *
      conj (w.1 (windowMirrorIndex Z T n))

/-- One finite convolution-square zero summand is exactly one diagonal entry of
the reduced mirror form. -/
theorem zeroSummand_convolutionSquare_eq_reducedMirrorTerm
    (Z : ZeroData) (T : ℝ) (g : WeilTestFunction)
    (n : WindowZeroIndex Z T) :
    zeroSummand Z (convolutionSquare g) n.1 =
      (Z.multiplicity n.1 : ℂ) *
        (finiteWeilReducedEvaluation Z T g).1 n *
        conj ((finiteWeilReducedEvaluation Z T g).1
          (windowMirrorIndex Z T n)) := by
  rw [zeroSummand, fourierLaplace_convolutionSquare_complex]
  change
    (Z.multiplicity n.1 : ℂ) *
        (fourierLaplace g (Z.gamma n.1) *
          conj (fourierLaplace g (conj (Z.gamma n.1)))) =
      (Z.multiplicity n.1 : ℂ) * fourierLaplace g (Z.gamma n.1) *
        conj (fourierLaplace g
          (Z.gamma (mirrorIndex Z n.1)))
  rw [mirrorIndex_gamma]
  ring

/-- The actual finite convolution-square zero sum factors exactly through the
reflection-reduced, multiplicity-weighted mirror form. -/
theorem truncatedZeroSum_convolutionSquare_eq_reducedMirrorForm
    (Z : ZeroData) (T : ℝ) (g : WeilTestFunction) :
    truncatedZeroSum Z (convolutionSquare g) T =
      finiteMirrorReducedForm Z T
        (finiteWeilReducedEvaluation Z T g)
        (finiteWeilReducedEvaluation Z T g) := by
  classical
  symm
  change
    (∑ n : WindowZeroIndex Z T,
      (Z.multiplicity n.1 : ℂ) *
        (finiteWeilReducedEvaluation Z T g).1 n *
        conj ((finiteWeilReducedEvaluation Z T g).1
          (windowMirrorIndex Z T n))) =
      ∑ n ∈ Z.symmetricIndices T,
        zeroSummand Z (convolutionSquare g) n
  rw [← Finset.sum_subtype
    (p := fun n : ℕ => n ∈ Z.symmetricIndices T)
    (Z.symmetricIndices T) (by simp)]
  apply Fintype.sum_congr
  intro n
  exact (zeroSummand_convolutionSquare_eq_reducedMirrorTerm Z T g n).symm

/-- The finite real Weil quadratic form on the reduced observable space. -/
noncomputable def finiteMirrorReducedQuadratic
    (Z : ZeroData) (T : ℝ)
    (v : FiniteReflectionEvenVector Z T) : ℝ :=
  (finiteMirrorReducedForm Z T v v).re

/-- Real-part version of the full finite factorization. -/
theorem truncatedZeroSum_convolutionSquare_re_eq_reducedQuadratic
    (Z : ZeroData) (T : ℝ) (g : WeilTestFunction) :
    (truncatedZeroSum Z (convolutionSquare g) T).re =
      finiteMirrorReducedQuadratic Z T
        (finiteWeilReducedEvaluation Z T g) := by
  rw [finiteMirrorReducedQuadratic,
    truncatedZeroSum_convolutionSquare_eq_reducedMirrorForm]

/-- The real convolution-square contribution of one four-point orbit. -/
noncomputable def fourPointOrbitRealValue
    (Z : ZeroData) (g : WeilTestFunction) (n : ℕ) : ℝ :=
  (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
    Z.conjugation (Z.reflection n)} : Finset ℕ),
    zeroSummand Z (convolutionSquare g) k).re

/-- Sum of selected four-point orbit blocks. -/
noncomputable def finiteOrbitBlockRealValue
    {ι : Type*} [Fintype ι]
    (Z : ZeroData) (g : WeilTestFunction) (index : ι → ℕ) : ℝ :=
  ∑ i, fourPointOrbitRealValue Z g (index i)

/-- Sum of the nonnegative even energies of selected orbit blocks. -/
noncomputable def finiteOrbitEvenEnergy
    {ι : Type*} [Fintype ι]
    (Z : ZeroData) (g : WeilTestFunction) (index : ι → ℕ) : ℝ :=
  ∑ i, orbitEvenEnergy (Z.multiplicity (index i))
    (fourierLaplace g (Z.gamma (index i)))
    (fourierLaplace g (conj (Z.gamma (index i))))

/-- Sum of the nonnegative odd energies of selected orbit blocks. -/
noncomputable def finiteOrbitOddEnergy
    {ι : Type*} [Fintype ι]
    (Z : ZeroData) (g : WeilTestFunction) (index : ι → ℕ) : ℝ :=
  ∑ i, orbitOddEnergy (Z.multiplicity (index i))
    (fourierLaplace g (Z.gamma (index i)))
    (fourierLaplace g (conj (Z.gamma (index i))))

/-- Any finite family of nonreal off-line four-point orbit blocks has the exact
positive-even minus positive-odd decomposition.  Disjointness of the chosen
orbits is only needed when interpreting this block sum as a sum over their
union; it is not needed for the algebraic identity itself. -/
theorem finite_offLine_orbit_block_factorization
    {ι : Type*} [Fintype ι]
    (Z : ZeroData) (g : WeilTestFunction) (index : ι → ℕ)
    (hConjugate : ∀ i, Z.conjugation (index i) ≠ index i)
    (hOffLine : ∀ i, (Z.zero (index i)).re ≠ criticalAbscissa) :
    finiteOrbitBlockRealValue Z g index =
        finiteOrbitEvenEnergy Z g index - finiteOrbitOddEnergy Z g index ∧
      0 ≤ finiteOrbitEvenEnergy Z g index ∧
      0 ≤ finiteOrbitOddEnergy Z g index := by
  have hdecomposition (i : ι) :
      fourPointOrbitRealValue Z g (index i) =
        orbitEvenEnergy (Z.multiplicity (index i))
            (fourierLaplace g (Z.gamma (index i)))
            (fourierLaplace g (conj (Z.gamma (index i)))) -
          orbitOddEnergy (Z.multiplicity (index i))
            (fourierLaplace g (Z.gamma (index i)))
            (fourierLaplace g (conj (Z.gamma (index i)))) := by
    simpa [fourPointOrbitRealValue] using
      (off_line_orbit_parity_decomposition Z g (index i)
        (hConjugate i) (hOffLine i)).1
  have hEven (i : ι) :
      0 ≤ orbitEvenEnergy (Z.multiplicity (index i))
        (fourierLaplace g (Z.gamma (index i)))
        (fourierLaplace g (conj (Z.gamma (index i)))) := by
    simpa using
      (off_line_orbit_parity_decomposition Z g (index i)
        (hConjugate i) (hOffLine i)).2.2.2
  have hOdd (i : ι) :
      0 ≤ orbitOddEnergy (Z.multiplicity (index i))
        (fourierLaplace g (Z.gamma (index i)))
        (fourierLaplace g (conj (Z.gamma (index i)))) := by
    simpa using
      (off_line_orbit_parity_decomposition Z g (index i)
        (hConjugate i) (hOffLine i)).2.1
  refine ⟨?_, ?_, ?_⟩
  · unfold finiteOrbitBlockRealValue finiteOrbitEvenEnergy finiteOrbitOddEnergy
    calc
      (∑ i, fourPointOrbitRealValue Z g (index i)) =
          ∑ i,
            (orbitEvenEnergy (Z.multiplicity (index i))
                (fourierLaplace g (Z.gamma (index i)))
                (fourierLaplace g (conj (Z.gamma (index i)))) -
              orbitOddEnergy (Z.multiplicity (index i))
                (fourierLaplace g (Z.gamma (index i)))
                (fourierLaplace g (conj (Z.gamma (index i))))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hdecomposition i
      _ = _ := Finset.sum_sub_distrib
  · unfold finiteOrbitEvenEnergy
    exact Finset.sum_nonneg fun i _ => hEven i
  · unfold finiteOrbitOddEnergy
    exact Finset.sum_nonneg fun i _ => hOdd i

#print axioms truncatedZeroSum_convolutionSquare_eq_reducedMirrorForm
#print axioms finite_offLine_orbit_block_factorization

end D5.S3.Weil.ZetaBridge.FiniteMirrorReducedWeilFactorization
