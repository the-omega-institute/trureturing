/- GID: D5/S3/Weil/ZetaBridge/WeilEvaluationObservableSubspace
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilEvaluationObservableSubspace
   mirror-E: none(waiver:canonical-zeta-observer-interface)
   anchors: []
   digest: Characterize the finite vectors reachable by scalar even Weil tests and prove multiplicity and reflection rank obstructions. -/

import D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry
import D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
import Mathlib.Tactic

/-!
# The finite observable subspace of scalar even Weil evaluations

A scalar `WeilTestFunction` assigns one Fourier--Laplace value to each distinct
zero.  It cannot distinguish different analytic-multiplicity copies of the
same zero.  Since the test is even, it also assigns the same value to the two
functional-equation reflection coordinates `gamma` and `-gamma`.

This node makes both constraints explicit and proves two genuine
non-surjectivity results.  The ambient multiplicity-expanded zero Hilbert space
therefore contains directions that are invisible to scalar even Weil tests.
The later negative-index comparison must be performed on the reachable reduced
space rather than on the whole ambient odd sector.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace

open MeasureTheory
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Midline.Cayley.ZeroHilbertCayleyUnitarity
open scoped ComplexConjugate

/-- Distinct zero indices visible in the finite symmetric spectral window. -/
abbrev WindowZeroIndex (Z : ZeroData) (T : ℝ) :=
  {n : ℕ // n ∈ Z.symmetricIndices T}

/-- The multiplicity-expanded finite zero-coordinate type. -/
abbrev WindowZeroCoordinate (Z : ZeroData) (T : ℝ) :=
  Sigma fun n : WindowZeroIndex Z T => Fin (Z.multiplicity n.1)

/-- Functional-equation reflection restricted to a finite symmetric window. -/
noncomputable def windowReflectionIndex (Z : ZeroData) (T : ℝ) :
    Equiv.Perm (WindowZeroIndex Z T) where
  toFun n :=
    ⟨Z.reflection n.1,
      (Z.reflection_mem_symmetricIndices (T := T) (n := n.1)).2 n.2⟩
  invFun n :=
    ⟨Z.reflection n.1,
      (Z.reflection_mem_symmetricIndices (T := T) (n := n.1)).2 n.2⟩
  left_inv n := Subtype.ext (Z.reflection_reflection n.1)
  right_inv n := Subtype.ext (Z.reflection_reflection n.1)

/-- A finite linear combination of Weil tests.  This is kept as an explicit
constructor instead of installing global algebraic instances on the bundled
test-function type. -/
noncomputable def finiteWeilLinearCombination
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (g : ι → WeilTestFunction) : WeilTestFunction where
  toFun x := ∑ i, a i * g i x
  contDiff' := by
    apply ContDiff.sum
    intro i _
    fun_prop
  hasCompactSupport' := by
    change HasCompactSupport (∑ i : ι, fun x : ℝ => a i * g i x)
    apply HasCompactSupport.finset_sum (s := Finset.univ)
    intro i _
    exact (g i).hasCompactSupport.mul_left
  even' := by
    intro x
    change (∑ i, a i * g i (-x)) = ∑ i, a i * g i x
    apply Finset.sum_congr rfl
    intro i _
    rw [(g i).even]

/-- Fourier--Laplace evaluation is linear on explicit finite combinations. -/
theorem fourierLaplace_finiteWeilLinearCombination
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (g : ι → WeilTestFunction) (z : ℂ) :
    fourierLaplace (finiteWeilLinearCombination a g) z =
      ∑ i, a i * fourierLaplace (g i) z := by
  rw [fourierLaplace_apply]
  change
    (∫ x : ℝ, fourierKernel z x * (∑ i, a i * g i x)) =
      ∑ i, a i * fourierLaplace (g i) z
  rw [show (fun x : ℝ => fourierKernel z x * (∑ i, a i * g i x)) =
      fun x : ℝ => ∑ i, a i * (fourierKernel z x * g i x) by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  have hIntegrable (i : ι) :
      Integrable (fun x : ℝ => a i * (fourierKernel z x * g i x)) := by
    have hk : Continuous (fun x : ℝ => fourierKernel z x) := by
      unfold fourierKernel
      fun_prop
    exact ((continuous_const.mul (hk.mul (g i).continuous))).integrable_of_hasCompactSupport
      (g i).hasCompactSupport.mul_left.mul_left
  rw [integral_finsetSum _ (fun i _ => hIntegrable i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  rfl

/-- Scalar evaluation on one distinct zero in the window. -/
noncomputable def finiteWeilIndexEvaluation
    (Z : ZeroData) (T : ℝ) (g : WeilTestFunction) :
    WindowZeroIndex Z T → ℂ :=
  fun n => fourierLaplace g (Z.gamma n.1)

/-- Scalar evaluation repeated over every analytic-multiplicity copy. -/
noncomputable def finiteWeilCoordinateEvaluation
    (Z : ZeroData) (T : ℝ) (g : WeilTestFunction) :
    WindowZeroCoordinate Z T → ℂ :=
  fun v => fourierLaplace g (Z.gamma v.1.1)

/-- Every coordinate evaluation is constant on each multiplicity fiber. -/
theorem finiteWeilCoordinateEvaluation_fiber_constant
    (Z : ZeroData) (T : ℝ) (g : WeilTestFunction)
    (n : WindowZeroIndex Z T)
    (k l : Fin (Z.multiplicity n.1)) :
    finiteWeilCoordinateEvaluation Z T g ⟨n, k⟩ =
      finiteWeilCoordinateEvaluation Z T g ⟨n, l⟩ := rfl

/-- Evenness of the test makes finite index evaluation reflection invariant. -/
theorem finiteWeilIndexEvaluation_reflection
    (Z : ZeroData) (T : ℝ) (g : WeilTestFunction)
    (n : WindowZeroIndex Z T) :
    finiteWeilIndexEvaluation Z T g (windowReflectionIndex Z T n) =
      finiteWeilIndexEvaluation Z T g n := by
  change fourierLaplace g (Z.gamma (Z.reflection n.1)) =
    fourierLaplace g (Z.gamma n.1)
  rw [Z.gamma_reflection, fourierLaplace_neg]

/-- The exact multiplicity-fiber constraint on an ambient coordinate vector. -/
def MultiplicityFiberConstant
    (Z : ZeroData) (T : ℝ)
    (v : WindowZeroCoordinate Z T → ℂ) : Prop :=
  ∀ (n : WindowZeroIndex Z T)
    (k l : Fin (Z.multiplicity n.1)), v ⟨n, k⟩ = v ⟨n, l⟩

/-- The exact reflection-even constraint on a finite distinct-zero vector. -/
def ReflectionEvenOnWindow
    (Z : ZeroData) (T : ℝ)
    (v : WindowZeroIndex Z T → ℂ) : Prop :=
  ∀ n, v (windowReflectionIndex Z T n) = v n

/-- Every scalar Weil coordinate vector lies in the multiplicity-constant
observable subspace. -/
theorem finiteWeilCoordinateEvaluation_mem_observable
    (Z : ZeroData) (T : ℝ) (g : WeilTestFunction) :
    MultiplicityFiberConstant Z T
      (finiteWeilCoordinateEvaluation Z T g) :=
  finiteWeilCoordinateEvaluation_fiber_constant Z T g

/-- Every scalar Weil index vector lies in the reflection-even observable
subspace. -/
theorem finiteWeilIndexEvaluation_mem_observable
    (Z : ZeroData) (T : ℝ) (g : WeilTestFunction) :
    ReflectionEvenOnWindow Z T (finiteWeilIndexEvaluation Z T g) :=
  finiteWeilIndexEvaluation_reflection Z T g

/-- Two analytic-multiplicity copies of the same zero can never be separated by
scalar Weil evaluation. -/
theorem no_scalar_weil_test_separates_multiplicity_copies
    (Z : ZeroData) (T : ℝ)
    (n : WindowZeroIndex Z T)
    (k l : Fin (Z.multiplicity n.1)) :
    ¬ ∃ g : WeilTestFunction,
      finiteWeilCoordinateEvaluation Z T g ⟨n, k⟩ ≠
        finiteWeilCoordinateEvaluation Z T g ⟨n, l⟩ := by
  rintro ⟨g, h⟩
  exact h (finiteWeilCoordinateEvaluation_fiber_constant Z T g n k l)

/-- If a represented zero has multiplicity at least two, scalar Weil
coordinate evaluation is not surjective onto the ambient multiplicity-expanded
finite space. -/
theorem finiteWeilCoordinateEvaluation_not_surjective_of_two_copies
    (Z : ZeroData) (T : ℝ)
    (n : WindowZeroIndex Z T)
    (hTwo : 2 ≤ Z.multiplicity n.1) :
    ¬ Function.Surjective (finiteWeilCoordinateEvaluation Z T) := by
  classical
  let k0 : Fin (Z.multiplicity n.1) := ⟨0, by omega⟩
  let k1 : Fin (Z.multiplicity n.1) := ⟨1, by omega⟩
  let v0 : WindowZeroCoordinate Z T := ⟨n, k0⟩
  let v1 : WindowZeroCoordinate Z T := ⟨n, k1⟩
  have hv : v0 ≠ v1 := by
    intro h
    have hval := congrArg
      (fun v : WindowZeroCoordinate Z T => v.2.val) h
    simp [v0, v1, k0, k1] at hval
  let target : WindowZeroCoordinate Z T → ℂ :=
    fun v => if v = v0 then 1 else 0
  intro hsurj
  obtain ⟨g, hg⟩ := hsurj target
  have h0 : finiteWeilCoordinateEvaluation Z T g v0 = 1 := by
    have := congrFun hg v0
    simpa [target] using this
  have h1 : finiteWeilCoordinateEvaluation Z T g v1 = 0 := by
    have := congrFun hg v1
    simpa [target, hv.symm] using this
  have hconst : finiteWeilCoordinateEvaluation Z T g v0 =
      finiteWeilCoordinateEvaluation Z T g v1 := by
    exact finiteWeilCoordinateEvaluation_fiber_constant Z T g n k0 k1
  have : (1 : ℂ) = 0 := h0.symm.trans (hconst.trans h1)
  exact one_ne_zero this

/-- A moved reflection pair is another independent obstruction to surjectivity
of scalar even evaluation on distinct-zero coordinates. -/
theorem finiteWeilIndexEvaluation_not_surjective_of_reflection_pair
    (Z : ZeroData) (T : ℝ)
    (n : WindowZeroIndex Z T)
    (hmove : windowReflectionIndex Z T n ≠ n) :
    ¬ Function.Surjective (finiteWeilIndexEvaluation Z T) := by
  classical
  let target : WindowZeroIndex Z T → ℂ :=
    fun j => if j = n then 1 else 0
  intro hsurj
  obtain ⟨g, hg⟩ := hsurj target
  have hn : finiteWeilIndexEvaluation Z T g n = 1 := by
    have := congrFun hg n
    simpa [target] using this
  have hmirror :
      finiteWeilIndexEvaluation Z T g (windowReflectionIndex Z T n) = 0 := by
    have := congrFun hg (windowReflectionIndex Z T n)
    simpa [target, hmove] using this
  have heven := finiteWeilIndexEvaluation_reflection Z T g n
  have : (1 : ℂ) = 0 := hn.symm.trans (heven.symm.trans hmirror)
  exact one_ne_zero this

/-- Complete range-constraint package for finite scalar even Weil evaluation. -/
theorem finite_weil_evaluation_observable_subspace_spec
    (Z : ZeroData) (T : ℝ) :
    (∀ g : WeilTestFunction,
      MultiplicityFiberConstant Z T
        (finiteWeilCoordinateEvaluation Z T g)) ∧
    (∀ g : WeilTestFunction,
      ReflectionEvenOnWindow Z T
        (finiteWeilIndexEvaluation Z T g)) :=
  ⟨finiteWeilCoordinateEvaluation_mem_observable Z T,
    finiteWeilIndexEvaluation_mem_observable Z T⟩

#print axioms fourierLaplace_finiteWeilLinearCombination
#print axioms finiteWeilCoordinateEvaluation_fiber_constant
#print axioms finiteWeilIndexEvaluation_reflection
#print axioms finiteWeilCoordinateEvaluation_not_surjective_of_two_copies
#print axioms finiteWeilIndexEvaluation_not_surjective_of_reflection_pair

end D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
