/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedCoefficientOperator
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/CompletedCoefficientOperator
   mirror-E: none(waiver:completed-Hilbert-space-operator)
   anchors: []
   utility: none
   digest: Actual Hilbert-Schmidt coefficient operator of a completed two-mode vector. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
import D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis
import D5.S3.Quantum.Analysis.TraceClass.Spectral
import Batteries.Tactic.OpenPrivate

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedCoefficientOperator
open BeamSplitter DisplacementCovariance HilbertSchmidt
open private reindex_basis from D5.S3.Quantum.Analysis.TraceClass.Spectral

abbrev H := lp (fun _ : ℕ => ℂ) 2
abbrev H2 := lp (fun _ : ℕ => H) 2

private def occupationBasis : HilbertBasis ℕ ℂ H := default

private theorem slice_square_sum (w : H2) : HasSum (fun n => ‖w n‖ ^ 2) (‖w‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w

private theorem coefficient_data (w : H2) :
    ∃ C : H →L[ℂ] H, IsHilbertSchmidt C ∧
      ∀ n, C (occupationBasis n) = w n := by
  let e : ℕ ≃ Set.range occupationBasis :=
    Equiv.ofInjective occupationBasis occupationBasis.orthonormal.linearIndependent.injective
  obtain ⟨b, hb⟩ := reindex_basis occupationBasis e.symm
  have hv : Summable (fun i : Set.range occupationBasis => ‖w (e.symm i)‖ ^ 2) :=
    e.symm.summable_iff.mpr (slice_square_sum w).summable
  obtain ⟨C, hC, hHS, _, _⟩ :=
    exists_hilbertSchmidt_of_square_summable_columns b (fun i => w (e.symm i)) hv
  refine ⟨C, hHS, fun n => ?_⟩
  simpa only [hb, Equiv.symm_apply_apply] using hC (e n)

/-- Its columns are the actual completed output slices, including infinite support. -/
def coefficientOperator (w : H2) : H →L[ℂ] H := (coefficient_data w).choose

private theorem coefficient_hs (w : H2) : IsHilbertSchmidt (coefficientOperator w) :=
  (coefficient_data w).choose_spec.1

private theorem coefficient_column (w : H2) (n : ℕ) :
    coefficientOperator w (occupationBasis n) = w n := (coefficient_data w).choose_spec.2 n

/-- The operator made from actual matrix columns reproduces the existing reduced
operator. No spectral data or analytic-purity assumption enters this equality. -/
theorem coefficient_mul_adjoint (w : H2) :
    coefficientOperator w * star (coefficientOperator w) = purePartialTrace w := by
  apply ContinuousLinearMap.ext
  intro x
  have hc := (occupationBasis.hasSum_repr ((ContinuousLinearMap.adjoint
      (coefficientOperator w)) x)).mapL (coefficientOperator w)
  have hc' : HasSum (fun n => inner ℂ (w n) x • w n)
      ((coefficientOperator w * star (coefficientOperator w)) x) := by
    simpa only [map_smul, HilbertBasis.repr_apply_apply, coefficient_column,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_apply] using hc
  have hs : Summable (fun n => InnerProductSpace.rankOne ℂ (w n) (w n)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using (slice_square_sum w).summable
  have hm := hs.hasSum.mapL (ContinuousLinearMap.apply ℂ H x)
  have hm' : HasSum (fun n => inner ℂ (w n) x • w n) (purePartialTrace w x) := by
    simpa only [purePartialTrace, mixture, ContinuousLinearMap.apply_apply,
      InnerProductSpace.rankOne_apply] using hm
  exact hc'.unique hm'

/-- Positivity and trace class refer to the existing completed reduced operator. -/
theorem partial_trace_positive_traceClass (w : H2) :
    0 ≤ purePartialTrace w ∧ IsTraceClass (purePartialTrace w) := by
  rw [← coefficient_mul_adjoint]
  exact ⟨mul_star_self_nonneg _, isTraceClass_mul_star_of_isHilbertSchmidt (coefficient_hs w)⟩

/-- Trace normalization follows from the actual column square sum and the
basis-independent Hilbert-Schmidt adjoint identity. -/
theorem partial_trace_trace (w : H2) :
    trace (purePartialTrace w) (partial_trace_positive_traceClass w).2 = (‖w‖ ^ 2 : ℂ) := by
  let e : ℕ ≃ Set.range occupationBasis :=
    Equiv.ofInjective occupationBasis occupationBasis.orthonormal.linearIndependent.injective
  obtain ⟨b, hb⟩ := reindex_basis occupationBasis e.symm
  have hv : HasSum (fun i : Set.range occupationBasis => ‖coefficientOperator w (b i)‖ ^ 2)
      (‖w‖ ^ 2) := by
    simpa only [hb, coefficient_column, Function.comp_apply] using
      e.symm.hasSum_iff.mpr (slice_square_sum w)
  have hadj := hasSum_norm_sq_apply_eq_adjoint b b hv.summable
  rw [hv.tsum_eq] at hadj
  rw [trace_eq_of_hilbertBasis_of_nonneg (partial_trace_positive_traceClass w).1
    (partial_trace_positive_traceClass w).2 b]
  have hdiag (i : Set.range occupationBasis) :
      inner ℂ (b i) (purePartialTrace w (b i)) =
      (‖ContinuousLinearMap.adjoint (coefficientOperator w) (b i)‖ ^ 2 : ℂ) := by
    rw [← coefficient_mul_adjoint, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.star_eq_adjoint]
    have hi := ContinuousLinearMap.adjoint_inner_right
      (ContinuousLinearMap.adjoint (coefficientOperator w)) (b i)
      (ContinuousLinearMap.adjoint (coefficientOperator w) (b i))
    simpa only [ContinuousLinearMap.adjoint_adjoint, inner_self_eq_norm_sq_to_K,
      Complex.ofReal_pow] using hi
  simp_rw [hdiag]
  simpa only [Complex.ofReal_pow] using (Complex.hasSum_ofReal.mpr hadj).tsum_eq

/-- The physical balanced two-photon output is obtained from the published
completed beam splitter, with no support restriction on the input. -/
def balancedFockTwoOutput (a : H) : H2 :=
  beamSplitter (1 / 2) (by norm_num) (tensor a (lp.single 2 2 1))

def balancedFockTwoCoefficient (a : H) : H →L[ℂ] H :=
  coefficientOperator (balancedFockTwoOutput a)

private theorem tensor_norm_sq (v w : H) : ‖tensor v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
  have ht := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (tensor v w)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ht
  rw [ht]
  change (∑' n, ‖w n • v‖ ^ 2) = _
  simp only [norm_smul, mul_pow]
  rw [(slice_square_sum w).summable.tsum_mul_right, (slice_square_sum w).tsum_eq,
    mul_comm]

private theorem balanced_output_norm_sq (a : H) :
    ‖balancedFockTwoOutput a‖ ^ 2 = ‖a‖ ^ 2 := by
  rw [balancedFockTwoOutput, LinearIsometryEquiv.norm_map, tensor_norm_sq]
  simp [lp.norm_single]

/-- Actual normalization for every input, including zero. -/
theorem balanced_fock_two_normalization (a : H) :
    IsHilbertSchmidt (balancedFockTwoCoefficient a) ∧
    balancedFockTwoCoefficient a * star (balancedFockTwoCoefficient a) =
      purePartialTrace (balancedFockTwoOutput a) ∧
    trace (purePartialTrace (balancedFockTwoOutput a))
      (partial_trace_positive_traceClass _).2 = (‖a‖ ^ 2 : ℂ) := by
  refine ⟨coefficient_hs _, coefficient_mul_adjoint _, ?_⟩
  rw [partial_trace_trace, ← Complex.ofReal_pow, balanced_output_norm_sq, Complex.ofReal_pow]

#print axioms coefficient_mul_adjoint
#print axioms partial_trace_positive_traceClass
#print axioms partial_trace_trace
#print axioms balanced_fock_two_normalization

end D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedCoefficientOperator
