/- GID: D5/S3/Fourier/CompletionConstants/CompletionSignatureCovariance
   generality: G
   mirror-B: D5/B/S3/Fourier/CompletionConstants/CompletionSignatureCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Completion points and Gaussian self-duality are invariant under coordinate change. -/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.SetTheory.Cardinal.Defs

open scoped FourierTransform

namespace D5.S3.Fourier.CompletionConstants.CompletionSignatureCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w g

-- The source volume's completion problem `(A, X, D, F, Delta, N, G)`,
-- including the gauge actions on parameters and candidate objects.
structure CompletionProblem where
  Parameter : Type u
  Candidate : Type v
  Defect : Type w
  Gauge : Type g
  zeroDefect : Defect
  candidateFamily : Parameter -> Candidate
  defect : Parameter -> Defect
  normalized : Set Parameter
  [gaugeGroup : Group Gauge]
  [parameterGaugeAction : MulAction Gauge Parameter]
  [candidateGaugeAction : MulAction Gauge Candidate]

-- The set `K(C)` of normalized parameters with zero structural defect.
def completionPointSet (problem : CompletionProblem) : Set problem.Parameter :=
  {parameter | parameter ∈ problem.normalized /\
    problem.defect parameter = problem.zeroDefect}

-- The type carried by the completion-point set `K(C)`.
abbrev CompletionPoint (problem : CompletionProblem) := completionPointSet problem

-- The two source equivalences required of the parameter bijection `alpha`.
structure CompletionCoordinateChange
    (source target : CompletionProblem) where
  alpha : source.Parameter ≃ target.Parameter
  normalized_iff : forall parameter,
    parameter ∈ source.normalized ↔ alpha parameter ∈ target.normalized
  zeroDefect_iff : forall parameter,
    source.defect parameter = source.zeroDefect ↔
      target.defect (alpha parameter) = target.zeroDefect

-- Pinned Mathlib's `Equiv.subtypeEquiv` restricts `alpha` to the completion points.
def CompletionCoordinateChange.completionPointEquiv
    {source target : CompletionProblem}
    (change : CompletionCoordinateChange source target) :
    CompletionPoint source ≃ CompletionPoint target :=
  change.alpha.subtypeEquiv fun parameter =>
    and_congr (change.normalized_iff parameter) (change.zeroDefect_iff parameter)

def CompletionCoordinateChange.refl (problem : CompletionProblem) :
    CompletionCoordinateChange problem problem where
  alpha := Equiv.refl problem.Parameter
  normalized_iff _ := Iff.rfl
  zeroDefect_iff _ := Iff.rfl

def CompletionCoordinateChange.symm
    {source target : CompletionProblem}
    (change : CompletionCoordinateChange source target) :
    CompletionCoordinateChange target source where
  alpha := change.alpha.symm
  normalized_iff parameter := by
    simpa using (change.normalized_iff (change.alpha.symm parameter)).symm
  zeroDefect_iff parameter := by
    simpa using (change.zeroDefect_iff (change.alpha.symm parameter)).symm

def CompletionCoordinateChange.trans
    {source middle target : CompletionProblem}
    (first : CompletionCoordinateChange source middle)
    (second : CompletionCoordinateChange middle target) :
    CompletionCoordinateChange source target where
  alpha := first.alpha.trans second.alpha
  normalized_iff parameter :=
    (first.normalized_iff parameter).trans
      (second.normalized_iff (first.alpha parameter))
  zeroDefect_iff parameter :=
    (first.zeroDefect_iff parameter).trans
      (second.zeroDefect_iff (first.alpha parameter))

-- The source's coordinate changes form the equivalence relation whose quotient
-- is the isomorphism class of completion problems.
def completionProblemCoordinateSetoid : Setoid CompletionProblem where
  r source target := Nonempty (CompletionCoordinateChange source target)
  iseqv := ⟨
    fun problem => ⟨CompletionCoordinateChange.refl problem⟩,
    fun ⟨change⟩ => ⟨change.symm⟩,
    fun ⟨first⟩ ⟨second⟩ => ⟨first.trans second⟩⟩

abbrev CompletionProblemIsomorphismClass := Quotient completionProblemCoordinateSetoid

def completionProblemIsomorphismClass (problem : CompletionProblem) :
    CompletionProblemIsomorphismClass :=
  Quotient.mk completionProblemCoordinateSetoid problem

-- The nontrivial coordinate scale relating the two Fourier conventions.
noncomputable def gaussianCoordinateScale : ℝ :=
  Real.sqrt (2 * Real.pi)

theorem gaussian_coordinate_scale_pos : 0 < gaussianCoordinateScale := by
  rw [gaussianCoordinateScale, Real.sqrt_pos]
  positivity

theorem gaussian_coordinate_scale_ne_zero : gaussianCoordinateScale ≠ 0 :=
  ne_of_gt gaussian_coordinate_scale_pos

theorem gaussian_coordinate_scale_sq : gaussianCoordinateScale ^ 2 = 2 * Real.pi := by
  exact Real.sq_sqrt (by positivity)

-- Pull functions through `x |-> x / sqrt(2*pi)`.
noncomputable def gaussianCoordinateEquiv : (ℝ -> ℂ) ≃ (ℝ -> ℂ) where
  toFun function coordinate := function (coordinate / gaussianCoordinateScale)
  invFun function coordinate := function (gaussianCoordinateScale * coordinate)
  left_inv function := by
    funext coordinate
    simp [gaussian_coordinate_scale_ne_zero]
  right_inv function := by
    funext coordinate
    apply congrArg function
    field_simp [gaussian_coordinate_scale_ne_zero]

-- The standard Fourier normalization with kernel `exp(-2*pi*i*x*xi)`.
noncomputable def standardFourier (function : ℝ -> ℂ) : ℝ -> ℂ :=
  𝓕 function

-- Conjugating an operator by a coordinate equivalence.
def conjugateOperator {X : Type*} (equivalence : X ≃ X) (operator : X -> X) : X -> X :=
  fun value => equivalence (operator (equivalence.symm value))

-- The unitary angular-frequency convention obtained by the nontrivial
-- `sqrt(2*pi)` coordinate normalization.
noncomputable def angularFourier : (ℝ -> ℂ) -> (ℝ -> ℂ) :=
  conjugateOperator gaussianCoordinateEquiv standardFourier

-- Fixed points are transported by conjugating their operator.
def fixedPointEquiv {X : Type*} (equivalence : X ≃ X) (operator : X -> X) :
    {value // operator value = value} ≃
      {value // conjugateOperator equivalence operator value = value} :=
  equivalence.subtypeEquiv fun value => by
    simp [conjugateOperator]

-- The Gaussian `exp(-pi*x^2)` in the standard Fourier coordinate.
noncomputable def standardGaussian (coordinate : ℝ) : ℂ :=
  Complex.exp ((-Real.pi * coordinate ^ 2 : ℝ) : ℂ)

-- The Gaussian `exp(-x^2/2)` in the unitary angular coordinate.
noncomputable def angularGaussian (coordinate : ℝ) : ℂ :=
  Complex.exp ((-coordinate ^ 2 / 2 : ℝ) : ℂ)

theorem coordinate_standard_gaussian :
    gaussianCoordinateEquiv standardGaussian = angularGaussian := by
  funext coordinate
  have exponent_change :
      -Real.pi * (coordinate / gaussianCoordinateScale) ^ 2 =
        -coordinate ^ 2 / 2 := by
    rw [div_pow, gaussian_coordinate_scale_sq]
    field_simp [Real.pi_ne_zero]
  simp [gaussianCoordinateEquiv, standardGaussian, angularGaussian, exponent_change]

-- Coercion bridge to the exact function shape used by Mathlib.
theorem standard_gaussian_eq_mathlib :
    standardGaussian =
      fun coordinate : ℝ =>
        Complex.exp (-(Real.pi : ℂ) * (coordinate : ℂ) ^ 2) := by
  funext coordinate
  simp [standardGaussian, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow]

-- Exact pinned-Mathlib specialization at `b = 1`.
theorem standard_gaussian_self_dual :
    standardFourier standardGaussian = standardGaussian := by
  rw [standard_gaussian_eq_mathlib]
  simpa [standardFourier] using
    (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num))

theorem angular_gaussian_self_dual :
    angularFourier angularGaussian = angularGaussian := by
  calc
    angularFourier angularGaussian =
        gaussianCoordinateEquiv
          (standardFourier (gaussianCoordinateEquiv.symm angularGaussian)) := rfl
    _ = gaussianCoordinateEquiv (standardFourier standardGaussian) := by
      rw [← coordinate_standard_gaussian]
      simp
    _ = gaussianCoordinateEquiv standardGaussian := by
      rw [standard_gaussian_self_dual]
    _ = angularGaussian := coordinate_standard_gaussian

-- A concrete separation point for the two coordinate formulas.
theorem gaussian_forms_differ_at_one : standardGaussian 1 ≠ angularGaussian 1 := by
  intro equal_values
  have standard_value : standardGaussian 1 = (Real.exp (-Real.pi) : ℂ) := by
    simp [standardGaussian, Complex.ofReal_exp]
  have angular_value : angularGaussian 1 = (Real.exp (-(1 : ℝ) / 2) : ℂ) := by
    simp [angularGaussian, Complex.ofReal_exp]
  rw [standard_value, angular_value] at equal_values
  have equal_real_exponentials : Real.exp (-Real.pi) = Real.exp (-(1 : ℝ) / 2) :=
    Complex.ofReal_injective equal_values
  have equal_exponents : -Real.pi = -(1 : ℝ) / 2 :=
    Real.exp_injective equal_real_exponentials
  linarith [Real.pi_gt_three]

theorem gaussian_forms_ne : standardGaussian ≠ angularGaussian := by
  intro equal_functions
  exact gaussian_forms_differ_at_one (congrFun equal_functions 1)

theorem gaussian_coordinate_change_ne_refl :
    gaussianCoordinateEquiv ≠ Equiv.refl (ℝ -> ℂ) := by
  intro equal_equivalences
  have fixed_standard : gaussianCoordinateEquiv standardGaussian = standardGaussian := by
    rw [equal_equivalences]
    rfl
  exact gaussian_forms_ne (fixed_standard.symm.trans coordinate_standard_gaussian)

-- Completion signature covariance, including the post-proof invariant and
-- the two nonidentical Gaussian coordinate presentations from the atom.
theorem completion_signature_covariance
    {source target : CompletionProblem}
    (change : CompletionCoordinateChange source target) :
    (∃ equivalence : CompletionPoint source ≃ CompletionPoint target,
      ∀ point, (equivalence point).1 = change.alpha point.1) /\
    completionProblemIsomorphismClass source = completionProblemIsomorphismClass target /\
    gaussianCoordinateEquiv ≠ Equiv.refl (ℝ -> ℂ) /\
    standardFourier standardGaussian = standardGaussian /\
    angularFourier angularGaussian = angularGaussian /\
    standardGaussian ≠ angularGaussian /\
    ∃ equivalence :
        {function // standardFourier function = function} ≃
          {function // angularFourier function = function},
      equivalence
          (⟨standardGaussian, standard_gaussian_self_dual⟩ :
            {function // standardFourier function = function}) =
        (⟨angularGaussian, angular_gaussian_self_dual⟩ :
          {function // angularFourier function = function}) := by
  let completionEquiv := change.completionPointEquiv
  refine ⟨⟨completionEquiv, fun _ => rfl⟩, ?_, gaussian_coordinate_change_ne_refl,
    standard_gaussian_self_dual, angular_gaussian_self_dual, gaussian_forms_ne, ?_⟩
  · exact Quotient.sound ⟨change⟩
  · refine ⟨fixedPointEquiv gaussianCoordinateEquiv standardFourier, ?_⟩
    apply Subtype.ext
    exact coordinate_standard_gaussian

-- Reverse probe for A1: completion-point covariance implies equality of the
-- isomorphism classes of the two completion-point types.
example {source target : CompletionProblem}
    (change : CompletionCoordinateChange source target)
    (statement :
      (∃ equivalence : CompletionPoint source ≃ CompletionPoint target,
        ∀ point, (equivalence point).1 = change.alpha point.1) /\
      completionProblemIsomorphismClass source = completionProblemIsomorphismClass target /\
      gaussianCoordinateEquiv ≠ Equiv.refl (ℝ -> ℂ) /\
      standardFourier standardGaussian = standardGaussian /\
      angularFourier angularGaussian = angularGaussian /\
      standardGaussian ≠ angularGaussian /\
      ∃ equivalence :
          {function // standardFourier function = function} ≃
            {function // angularFourier function = function},
        equivalence
            (⟨standardGaussian, standard_gaussian_self_dual⟩ :
              {function // standardFourier function = function}) =
          (⟨angularGaussian, angular_gaussian_self_dual⟩ :
            {function // angularFourier function = function})) :
    Cardinal.mk (CompletionPoint source) = Cardinal.mk (CompletionPoint target) := by
  rcases statement.1 with ⟨equivalence, _⟩
  exact Cardinal.mk_congr equivalence

-- Reverse probe for A2: equality of the quotient classes recovers a source-exact
-- completion coordinate change.
example {source target : CompletionProblem}
    (classEquality :
      completionProblemIsomorphismClass source = completionProblemIsomorphismClass target) :
    Nonempty (CompletionCoordinateChange source target) :=
  Quotient.exact classEquality

-- Collapse probe for A3/A6: the public formulas distinguish a concrete point.
example : ∃ coordinate, standardGaussian coordinate ≠ angularGaussian coordinate :=
  ⟨1, gaussian_forms_differ_at_one⟩

-- Structure probe for A7: fixed points of the two Fourier normalizations are
-- equivalent, and the standard Gaussian is sent to the angular Gaussian.
example :
    let equivalence := fixedPointEquiv gaussianCoordinateEquiv standardFourier
    equivalence
      (⟨standardGaussian, standard_gaussian_self_dual⟩ :
        {function // standardFourier function = function}) =
      (⟨angularGaussian, angular_gaussian_self_dual⟩ :
        {function // angularFourier function = function}) := by
  apply Subtype.ext
  exact coordinate_standard_gaussian

#print axioms completion_signature_covariance

end D5.S3.Fourier.CompletionConstants.CompletionSignatureCovariance
