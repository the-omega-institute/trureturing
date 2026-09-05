/- GID: D5/S3/Weil/ZetaBridge/WeilEvaluationExactObservableRange
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilEvaluationExactObservableRange
   mirror-E: none(waiver:canonical-zeta-observer-interface)
   anchors: []
   digest: Identify the exact finite range of scalar even Weil evaluation, transport mixed forms, and prove that multiplicity replication creates no readout-kernel escape. -/

import D5.S3.Weil.ZetaBridge.FiniteReflectionCompatibleWeilInterpolation
import D5.S3.Weil.ZetaBridge.FiniteMirrorReducedWeilFactorization

/-!
# Exact observable range and lossless multiplicity reduction

The earlier observable owner supplies necessary range constraints. Finite
reflection-compatible interpolation supplies their converse. Thus the reduced
codomain is the actual image of the original Weil-test observer.

The state space in every readout-kernel theorem below is the original
`WeilTestFunction`, without a truth-dependent subtype. Replicating an index
value along its analytic-multiplicity fiber leaves this kernel unchanged.
These are semantic kernel statements on an infinite state space. No finite
collision score, normalized pair mass, primitive-law admission, or positive
intrinsic-information gain is asserted.

The mixed factorization extends the existing diagonal identity without
introducing another zero model or counting analytic multiplicity twice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilEvaluationExactObservableRange

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.FiniteMirrorReducedWeilFactorization
open D5.S3.Weil.ZetaBridge.FiniteReflectionCompatibleWeilInterpolation
open D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv
open scoped BigOperators ComplexConjugate

/-- Extend window data by zero on the actual complementary zero indices. -/
def extendWindowValues (Z : ZeroData) (T : ℝ)
    (v : WindowZeroIndex Z T → ℂ) (n : ℕ) : ℂ :=
  if hn : n ∈ Z.symmetricIndices T then v ⟨n, hn⟩ else 0

/-- Reflection closure of the symmetric window makes zero extension lawful. -/
theorem extendWindowValues_reflection (Z : ZeroData) (T : ℝ)
    (v : WindowZeroIndex Z T → ℂ) (hv : ReflectionEvenOnWindow Z T v) :
    ∀ n, extendWindowValues Z T v (Z.reflection n) =
      extendWindowValues Z T v n := by
  classical
  intro n
  by_cases hn : n ∈ Z.symmetricIndices T
  · have hr : Z.reflection n ∈ Z.symmetricIndices T :=
      (Z.reflection_mem_symmetricIndices (T := T) (n := n)).2 hn
    simp only [extendWindowValues, dif_pos hn, dif_pos hr]
    exact hv ⟨n, hn⟩
  · have hr : Z.reflection n ∉ Z.symmetricIndices T := by
      intro h
      exact hn ((Z.reflection_mem_symmetricIndices (T := T) (n := n)).1 h)
    simp only [extendWindowValues, dif_neg hn, dif_neg hr]

/-- The exact finite scalar evaluation image consists of all reflection-even
index vectors. Both directions concern actual bundled Weil tests. -/
theorem finiteWeilIndexEvaluation_range_iff
    (Z : ZeroData) (T : ℝ) (v : WindowZeroIndex Z T → ℂ) :
    (∃ g : WeilTestFunction, finiteWeilIndexEvaluation Z T g = v) ↔
      ReflectionEvenOnWindow Z T v := by
  constructor
  · rintro ⟨g, rfl⟩
    exact finiteWeilIndexEvaluation_mem_observable Z T g
  · intro hv
    obtain ⟨g, hg⟩ := even_weil_interpolation_on_finite_indices Z
      (Z.symmetricIndices T) (extendWindowValues Z T v)
      (extendWindowValues_reflection Z T v hv)
    refine ⟨g, ?_⟩
    funext n
    change fourierLaplace g (Z.gamma n.1) = v n
    simpa only [extendWindowValues, dif_pos n.2] using hg n.1 n.2

/-- The previously defined reduced observable codomain is genuinely reached. -/
theorem finiteWeilReducedEvaluation_surjective (Z : ZeroData) (T : ℝ) :
    Function.Surjective (finiteWeilReducedEvaluation Z T) := by
  intro v
  obtain ⟨g, hg⟩ := (finiteWeilIndexEvaluation_range_iff Z T v.1).2 v.2
  exact ⟨g, Subtype.ext hg⟩

/-- Replicate one distinct-zero value into its existing multiplicity fiber. -/
def expandMultiplicityCopies (Z : ZeroData) (T : ℝ)
    (v : WindowZeroIndex Z T → ℂ) : WindowZeroCoordinate Z T → ℂ :=
  fun p => v p.1

/-- Read one genuine copy per zero. Positivity of the analytic order supplies
that copy; there is no zero-multiplicity exceptional case hidden here. -/
def collapseMultiplicityCopies (Z : ZeroData) (T : ℝ)
    (w : WindowZeroCoordinate Z T → ℂ) : WindowZeroIndex Z T → ℂ :=
  fun n => w ⟨n, ⟨0, Z.multiplicity_pos n.1⟩⟩

@[simp]
theorem collapse_expandMultiplicityCopies (Z : ZeroData) (T : ℝ)
    (v : WindowZeroIndex Z T → ℂ) :
    collapseMultiplicityCopies Z T (expandMultiplicityCopies Z T v) = v := rfl

/-- Multiplicity reduction loses no value precisely on the fiber-constant
subspace. -/
theorem expand_collapseMultiplicityCopies_iff (Z : ZeroData) (T : ℝ)
    (w : WindowZeroCoordinate Z T → ℂ) :
    expandMultiplicityCopies Z T (collapseMultiplicityCopies Z T w) = w ↔
      MultiplicityFiberConstant Z T w := by
  constructor
  · intro h n k l
    have hk := congrFun h ⟨n, k⟩
    have hl := congrFun h ⟨n, l⟩
    exact hk.symm.trans hl
  · intro hw
    funext p
    exact hw p.1 ⟨0, Z.multiplicity_pos p.1.1⟩ p.2

/-- Replication is injective, although its ambient codomain can be larger. -/
theorem expandMultiplicityCopies_injective (Z : ZeroData) (T : ℝ) :
    Function.Injective (expandMultiplicityCopies Z T) := by
  intro v w h
  exact congrArg (collapseMultiplicityCopies Z T) h

/-- Exact ambient-coordinate characterization, including both constraints. -/
theorem finiteWeilCoordinateEvaluation_range_iff (Z : ZeroData) (T : ℝ)
    (w : WindowZeroCoordinate Z T → ℂ) :
    (∃ g : WeilTestFunction, finiteWeilCoordinateEvaluation Z T g = w) ↔
      MultiplicityFiberConstant Z T w ∧
        ReflectionEvenOnWindow Z T (collapseMultiplicityCopies Z T w) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨finiteWeilCoordinateEvaluation_mem_observable Z T g,
      finiteWeilIndexEvaluation_mem_observable Z T g⟩
  · rintro ⟨hw, hr⟩
    obtain ⟨g, hg⟩ :=
      (finiteWeilIndexEvaluation_range_iff Z T
        (collapseMultiplicityCopies Z T w)).2 hr
    refine ⟨g, ?_⟩
    calc
      finiteWeilCoordinateEvaluation Z T g =
          expandMultiplicityCopies Z T (finiteWeilIndexEvaluation Z T g) := rfl
      _ = expandMultiplicityCopies Z T (collapseMultiplicityCopies Z T w) :=
        congrArg (expandMultiplicityCopies Z T) hg
      _ = w := (expand_collapseMultiplicityCopies_iff Z T w).2 hw

/-- Equality of the two readout kernels on the same original test-function
state space. Analytic multiplicity changes the form's weight, not the
information available to this scalar observer. -/
theorem finiteWeilEvaluation_readout_kernel_eq (Z : ZeroData) (T : ℝ)
    (g h : WeilTestFunction) :
    finiteWeilCoordinateEvaluation Z T g = finiteWeilCoordinateEvaluation Z T h ↔
      finiteWeilIndexEvaluation Z T g = finiteWeilIndexEvaluation Z T h := by
  constructor
  · intro heq
    exact congrArg (collapseMultiplicityCopies Z T) heq
  · intro heq
    exact congrArg (expandMultiplicityCopies Z T) heq

/-- The joint observer adding replicated coordinates also has the same kernel. -/
theorem replicated_joint_readout_eq_iff (Z : ZeroData) (T : ℝ)
    (g h : WeilTestFunction) :
    (finiteWeilIndexEvaluation Z T g, finiteWeilCoordinateEvaluation Z T g) =
      (finiteWeilIndexEvaluation Z T h, finiteWeilCoordinateEvaluation Z T h) ↔
      finiteWeilIndexEvaluation Z T g = finiteWeilIndexEvaluation Z T h := by
  constructor
  · exact congrArg Prod.fst
  · intro heq
    exact Prod.ext heq ((finiteWeilEvaluation_readout_kernel_eq Z T g h).2 heq)

/-- No strict fiber-separating witness can be manufactured by multiplicity
replication. This is a semantic zero-gain result, with no finite-state score. -/
theorem no_intrinsic_kernel_escape_from_multiplicity_replication
    (Z : ZeroData) (T : ℝ) :
    ¬ ∃ g h : WeilTestFunction,
      finiteWeilIndexEvaluation Z T g = finiteWeilIndexEvaluation Z T h ∧
      finiteWeilCoordinateEvaluation Z T g ≠ finiteWeilCoordinateEvaluation Z T h := by
  rintro ⟨g, h, heq, hne⟩
  exact hne ((finiteWeilEvaluation_readout_kernel_eq Z T g h).2 heq)

/-- The actual mixed convolution form factors through the now-proved exact
observable range. This includes off-diagonal Gram entries. -/
theorem truncatedZeroSum_mixed_eq_reducedMirrorForm
    (Z : ZeroData) (T : ℝ) (g h : WeilTestFunction) :
    truncatedZeroSum Z (convolve g (involution h)) T =
      finiteMirrorReducedForm Z T
        (finiteWeilReducedEvaluation Z T g)
        (finiteWeilReducedEvaluation Z T h) := by
  classical
  symm
  change (∑ n : WindowZeroIndex Z T,
    (Z.multiplicity n.1 : ℂ) *
      (finiteWeilReducedEvaluation Z T g).1 n *
      conj ((finiteWeilReducedEvaluation Z T h).1 (windowMirrorIndex Z T n))) =
    ∑ n ∈ Z.symmetricIndices T, zeroSummand Z (convolve g (involution h)) n
  rw [← Finset.sum_subtype
    (p := fun n : ℕ => n ∈ Z.symmetricIndices T)
    (Z.symmetricIndices T) (by simp)]
  apply Fintype.sum_congr
  intro n
  rw [zeroSummand, fourierLaplace_convolve_complex, fourierLaplace_involution_conj]
  change (Z.multiplicity n.1 : ℂ) * fourierLaplace g (Z.gamma n.1) *
      conj (fourierLaplace h (Z.gamma (mirrorIndex Z n.1))) =
    (Z.multiplicity n.1 : ℂ) *
      (fourierLaplace g (Z.gamma n.1) * conj (fourierLaplace h (conj (Z.gamma n.1))))
  rw [mirrorIndex_gamma]
  ring

#print axioms finiteWeilIndexEvaluation_range_iff
#print axioms finiteWeilReducedEvaluation_surjective
#print axioms finiteWeilCoordinateEvaluation_range_iff
#print axioms finiteWeilEvaluation_readout_kernel_eq
#print axioms no_intrinsic_kernel_escape_from_multiplicity_replication
#print axioms truncatedZeroSum_mixed_eq_reducedMirrorForm

end D5.S3.Weil.ZetaBridge.WeilEvaluationExactObservableRange
