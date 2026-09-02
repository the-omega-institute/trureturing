/- GID: D5/S3/Observer/PositiveWeightedReadoutGramKernel
   generality: G
   mirror-B: D5/B/S3/Observer/PositiveWeightedReadoutGramKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive weighted readout Gram operator has the common readout kernel. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Library-search audit trail (2026-09-02):
* D5 literal, symbol-variant, receipt, digest, generalized-body, and in-flight
  lane searches found scalar dual-Gram, quantum weighted-kernel, finite-time,
  and sensor-family specializations, but no theorem with dependent output
  spaces, strictly positive weights, the energy identity, and the common kernel.
* Pinned Mathlib provides `LinearMap.adjoint_inner_right`,
  `real_inner_self_eq_norm_sq`, `Finset.sum_eq_zero_iff_of_nonneg`, and
  `Submodule.mem_iInf`. No packaged positive weighted family theorem was found.
-/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.PositiveWeightedReadoutGramKernel

/-- The finite positive-weighted Gram operator associated with a family of
readouts. Positivity is imposed by the theorem that identifies its kernel. -/
def weightedReadoutGram
    {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Y : ι → Type*}
    [∀ i, NormedAddCommGroup (Y i)]
    [∀ i, InnerProductSpace ℝ (Y i)]
    [∀ i, FiniteDimensional ℝ (Y i)]
    (readout : ∀ i, V →ₗ[ℝ] Y i) (weight : ι → ℝ) : V →ₗ[ℝ] V :=
  ∑ i, weight i • ((readout i).adjoint.comp (readout i))

/-- For finitely many readouts into possibly different real inner-product
spaces, strict positivity of every weight makes the weighted Gram kernel
exactly the common readout kernel. The first conjunct records the source
energy identity used by the reverse inclusion. -/
theorem positive_weighted_readout_gram
    {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Y : ι → Type*}
    [∀ i, NormedAddCommGroup (Y i)]
    [∀ i, InnerProductSpace ℝ (Y i)]
    [∀ i, FiniteDimensional ℝ (Y i)]
    (readout : ∀ i, V →ₗ[ℝ] Y i) (weight : ι → ℝ)
    (weight_pos : ∀ i, 0 < weight i) :
    (∀ v : V, inner ℝ v ((weightedReadoutGram readout weight) v) =
      ∑ i, weight i * ‖readout i v‖ ^ 2) ∧
      LinearMap.ker (weightedReadoutGram readout weight) =
        ⨅ i, LinearMap.ker (readout i) := by
  unfold weightedReadoutGram
  have energyIdentity :
      ∀ v, inner ℝ v ((∑ i, weight i •
        ((readout i).adjoint.comp (readout i))) v) =
        ∑ i, weight i * ‖readout i v‖ ^ 2 := by
    intro v
    simp only [LinearMap.sum_apply, inner_sum, LinearMap.smul_apply,
      real_inner_smul_right, LinearMap.comp_apply,
      LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  refine ⟨energyIdentity, le_antisymm ?_ ?_⟩
  · intro v vInGramKernel
    rw [LinearMap.mem_ker] at vInGramKernel
    have energyZero : ∑ i, weight i * ‖readout i v‖ ^ 2 = 0 := by
      rw [← energyIdentity v, vInGramKernel, inner_zero_right]
    rw [Submodule.mem_iInf]
    intro i
    rw [LinearMap.mem_ker]
    have termZero : weight i * ‖readout i v‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        mul_nonneg (weight_pos j).le (sq_nonneg ‖readout j v‖)).mp
          energyZero i (Finset.mem_univ i)
    have normSquareZero : ‖readout i v‖ ^ 2 = 0 :=
      (mul_eq_zero.mp termZero).resolve_left (ne_of_gt (weight_pos i))
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp normSquareZero)
  · intro v vInCommonKernel
    rw [LinearMap.mem_ker]
    rw [LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have readoutZero : readout i v = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp vInCommonKernel i)
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, readoutZero,
      map_zero, smul_zero]

#print axioms positive_weighted_readout_gram

end D5.S3.Observer.PositiveWeightedReadoutGramKernel
