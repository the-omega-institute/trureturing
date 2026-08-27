/- GID: D5/S3/Quantum/Measurement/OperationalObservationKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/OperationalObservationKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive weighted quantum readouts induce the residual kernel and operational metric. -/

import D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-27):
   * Exact family hits `traceZeroHermitian`, `DensityState`, and the centered
     density-state signature from `informational_completeness_four_way` supply
     the source's real traceless-Hermitian carrier and completeness predicate.
   * Repository body-shape searches found no existing positive-weighted
     analysis, operational seminorm, state distance, or quotient distance.
   * Exact pinned-Mathlib hits `EuclideanSpace.norm_eq`, `dist_eq_zero`,
     `Setoid.ker`, and `Quotient.liftOn₂` construct the weighted seminorm and
     its canonical separated quotient. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace D5.S3.Quantum.Measurement.OperationalObservationKernel

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

/-- The weighted analysis map constructed from centered Hermitian effects. -/
def weightedEffectAnalysis
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real) :
    traceZeroHermitian d →ₗ[Real] EuclideanSpace Real Index where
  toFun D := WithLp.toLp 2 fun i =>
    Real.sqrt (weight i) * inner Real D (centeredEffects i)
  map_add' first second := by
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply, inner_add_left]
    ring
  map_smul' scalar D := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply, RingHom.id_apply,
      real_inner_smul_left]
    ring

/-- The state-side observation seminorm from the source's positive weighted
effect coordinates. -/
def operationalObservationSeminorm
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real) (D : traceZeroHermitian d) : Real :=
  ‖weightedEffectAnalysis centeredEffects weight D‖

/-- The positive-weighted readout of a density state in the centered effect
coordinates. -/
def weightedDensityReadout
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real) (rho : DensityState (Fin d)) :
    EuclideanSpace Real Index :=
  WithLp.toLp 2 fun i =>
    Real.sqrt (weight i) *
      (Matrix.trace
        (CStarMatrix.ofMatrix.symm rho.1 * (centeredEffects i).1.1)).re

/-- The observation pseudodistance is the Euclidean distance between weighted
state readouts. -/
def operationalStateDistance
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real) (rho sigma : DensityState (Fin d)) : Real :=
  dist (weightedDensityReadout centeredEffects weight rho)
    (weightedDensityReadout centeredEffects weight sigma)

/-- The operational quotient identifies density states with the same weighted
readout. -/
def OperationalStateQuotient
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real) : Type _ :=
  Quotient (Setoid.ker (weightedDensityReadout centeredEffects weight))

/-- The representative-independent distance on the operational quotient. -/
def operationalQuotientDistance
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real)
    (first second : OperationalStateQuotient centeredEffects weight) : Real :=
  Quotient.liftOn₂ first second
    (operationalStateDistance centeredEffects weight) (by
      intro rho sigma rho' sigma' hrho hsigma
      change weightedDensityReadout centeredEffects weight rho =
        weightedDensityReadout centeredEffects weight rho' at hrho
      change weightedDensityReadout centeredEffects weight sigma =
        weightedDensityReadout centeredEffects weight sigma' at hsigma
      simp only [operationalStateDistance, hrho, hsigma])

private theorem weighted_effect_analysis_apply
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real) (D : traceZeroHermitian d) (i : Index) :
    weightedEffectAnalysis centeredEffects weight D i =
      Real.sqrt (weight i) * inner Real D (centeredEffects i) := by
  rfl

private theorem operational_seminorm_kernel
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real) (hpositive : forall i, 0 < weight i) :
    {D | operationalObservationSeminorm centeredEffects weight D = 0} =
      (Submodule.span Real (Set.range centeredEffects))ᗮ := by
  ext D
  change ‖weightedEffectAnalysis centeredEffects weight D‖ = 0 <-> _
  rw [norm_eq_zero]
  constructor
  · intro hzero
    apply (Submodule.mem_orthogonal'
      (Submodule.span Real (Set.range centeredEffects)) D).2
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hgenerator =>
        rcases hgenerator with ⟨i, rfl⟩
        have hcoordinate := congrArg
          (fun value : EuclideanSpace Real Index => value i) hzero
        rw [weighted_effect_analysis_apply] at hcoordinate
        have hsqrt : Real.sqrt (weight i) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 (hpositive i))
        exact (mul_eq_zero.mp hcoordinate).resolve_left hsqrt
    | zero => simp
    | add first second _ _ hfirst hsecond =>
        simp only [inner_add_right, hfirst, hsecond, add_zero]
    | smul scalar Z _ hZ =>
        simp only [real_inner_smul_right, hZ, mul_zero]
  · intro horthogonal
    apply PiLp.ext
    intro i
    rw [weighted_effect_analysis_apply]
    have hgenerator : centeredEffects i ∈
        Submodule.span Real (Set.range centeredEffects) :=
      Submodule.subset_span (Set.mem_range_self i)
    have hinner :=
      (Submodule.mem_orthogonal'
        (Submodule.span Real (Set.range centeredEffects)) D).mp
        horthogonal (centeredEffects i) hgenerator
    simp [hinner]

private theorem quotient_distance_nonnegative
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real)
    (first second : OperationalStateQuotient centeredEffects weight) :
    0 <= operationalQuotientDistance centeredEffects weight first second := by
  refine Quotient.inductionOn₂' first second ?_
  intro rho sigma
  exact dist_nonneg

private theorem quotient_distance_self
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real)
    (state : OperationalStateQuotient centeredEffects weight) :
    operationalQuotientDistance centeredEffects weight state state = 0 := by
  refine Quotient.inductionOn' state ?_
  intro rho
  exact dist_self _

private theorem quotient_distance_comm
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real)
    (first second : OperationalStateQuotient centeredEffects weight) :
    operationalQuotientDistance centeredEffects weight first second =
      operationalQuotientDistance centeredEffects weight second first := by
  refine Quotient.inductionOn₂' first second ?_
  intro rho sigma
  exact dist_comm _ _

private theorem quotient_distance_triangle
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real)
    (first second third : OperationalStateQuotient centeredEffects weight) :
    operationalQuotientDistance centeredEffects weight first third <=
      operationalQuotientDistance centeredEffects weight first second +
        operationalQuotientDistance centeredEffects weight second third := by
  refine Quotient.inductionOn₃' first second third ?_
  intro rho sigma tau
  exact dist_triangle _ _ _

private theorem quotient_distance_zero_iff
    {d : Nat} {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real)
    (first second : OperationalStateQuotient centeredEffects weight) :
    operationalQuotientDistance centeredEffects weight first second = 0 <->
      first = second := by
  refine Quotient.inductionOn₂' first second ?_
  intro rho sigma
  constructor
  · intro hzero
    apply Quotient.sound
    change weightedDensityReadout centeredEffects weight rho =
      weightedDensityReadout centeredEffects weight sigma
    exact dist_eq_zero.mp hzero
  · intro hequal
    have hreadout : weightedDensityReadout centeredEffects weight rho =
        weightedDensityReadout centeredEffects weight sigma := by
      exact Quotient.exact hequal
    exact dist_eq_zero.mpr hreadout

/-- Positive weighted finite effects have exactly the invisible residual as
their observation-seminorm kernel. The induced state distance is a
pseudodistance, descends to a genuine metric on the operational quotient, and
separates all density states exactly when the observer is informationally
complete. -/
theorem operational_observation_kernel_and_metric
    (d : Nat) [NeZero d] {Index : Type*} [Fintype Index]
    (centeredEffects : Index -> traceZeroHermitian d)
    (weight : Index -> Real) (hpositive : forall i, 0 < weight i) :
    {D | operationalObservationSeminorm centeredEffects weight D = 0} =
        (Submodule.span Real (Set.range centeredEffects))ᗮ /\
      (forall rho sigma : DensityState (Fin d),
        0 <= operationalStateDistance centeredEffects weight rho sigma) /\
      (forall rho : DensityState (Fin d),
        operationalStateDistance centeredEffects weight rho rho = 0) /\
      (forall rho sigma : DensityState (Fin d),
        operationalStateDistance centeredEffects weight rho sigma =
          operationalStateDistance centeredEffects weight sigma rho) /\
      (forall rho sigma tau : DensityState (Fin d),
        operationalStateDistance centeredEffects weight rho tau <=
          operationalStateDistance centeredEffects weight rho sigma +
            operationalStateDistance centeredEffects weight sigma tau) /\
      (forall first second : OperationalStateQuotient centeredEffects weight,
        0 <= operationalQuotientDistance centeredEffects weight first second) /\
      (forall state : OperationalStateQuotient centeredEffects weight,
        operationalQuotientDistance centeredEffects weight state state = 0) /\
      (forall first second : OperationalStateQuotient centeredEffects weight,
        operationalQuotientDistance centeredEffects weight first second =
          operationalQuotientDistance centeredEffects weight second first) /\
      (forall first second third : OperationalStateQuotient centeredEffects weight,
        operationalQuotientDistance centeredEffects weight first third <=
          operationalQuotientDistance centeredEffects weight first second +
            operationalQuotientDistance centeredEffects weight second third) /\
      (forall first second : OperationalStateQuotient centeredEffects weight,
        operationalQuotientDistance centeredEffects weight first second = 0 <->
          first = second) /\
      ((forall rho sigma : DensityState (Fin d),
          operationalStateDistance centeredEffects weight rho sigma = 0 <->
            rho = sigma) <->
        Function.Injective (fun rho : DensityState (Fin d) => fun i =>
          (Matrix.trace
            (CStarMatrix.ofMatrix.symm rho.1 *
              (centeredEffects i).1.1)).re)) := by
  constructor
  · exact operational_seminorm_kernel centeredEffects weight hpositive
  constructor
  · intro rho sigma
    exact dist_nonneg
  constructor
  · intro rho
    exact dist_self _
  constructor
  · intro rho sigma
    exact dist_comm _ _
  constructor
  · intro rho sigma tau
    exact dist_triangle _ _ _
  constructor
  · exact quotient_distance_nonnegative centeredEffects weight
  constructor
  · exact quotient_distance_self centeredEffects weight
  constructor
  · exact quotient_distance_comm centeredEffects weight
  constructor
  · exact quotient_distance_triangle centeredEffects weight
  constructor
  · exact quotient_distance_zero_iff centeredEffects weight
  · constructor
    · intro hseparates rho sigma hreadout
      apply (hseparates rho sigma).mp
      rw [operationalStateDistance, dist_eq_zero]
      apply PiLp.ext
      intro i
      simp only [weightedDensityReadout, WithLp.ofLp_toLp]
      exact congrArg (fun value => Real.sqrt (weight i) * value)
        (congrFun hreadout i)
    · intro hinjective rho sigma
      constructor
      · intro hzero
        apply hinjective
        rw [operationalStateDistance, dist_eq_zero] at hzero
        funext i
        have hi := congrArg
          (fun value : EuclideanSpace Real Index => value i) hzero
        simp only [weightedDensityReadout, WithLp.ofLp_toLp] at hi
        exact mul_left_cancel₀
          (ne_of_gt (Real.sqrt_pos.2 (hpositive i))) hi
      · intro hequal
        subst sigma
        exact dist_self _

#print axioms operational_observation_kernel_and_metric

end D5.S3.Quantum.Measurement.OperationalObservationKernel
