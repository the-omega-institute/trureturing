/- GID: D5/S3/Weil/Pick/PairedComplexChannelCompleteness
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/PairedComplexChannelCompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive paired complex-channel energies have exactly the common channel kernel and are definite exactly under joint separation. -/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/- Library-search audit trail (2026-08-30):
   * The closest frozen finite theorem is
     `WeightedKernelCompleteness.weighted_kernel_completeness`, specialized to
     real trace-effect coordinates on traceless Hermitian matrices.
   * The closest norm-square theorem is
     `ObservabilityGramianKernelEnergy.observability_gramian_kernel_energy`,
     specialized to one time-indexed output channel and an infinite stable
     observability series.
   * Repository searches found no owner for a finite family of paired complex
     linear readouts with positive real weights, its exact common kernel, and
     the equivalence between strict energy positivity and joint injectivity.
   * Pinned Mathlib supplies finite nonnegative-sum elimination, norm-zero
     separation, and linear-map subtraction. -/

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Pick.PairedComplexChannelCompleteness

/-- The joint observation map records both complex channels at every finite
sensor index. -/
def pairedComplexObservation
    {V Index : Type*} [AddCommGroup V] [Module ℂ V] [Fintype Index]
    (minus plus : Index → V →ₗ[ℂ] ℂ) :
    V →ₗ[ℂ] (Index → ℂ × ℂ) where
  toFun x i := (minus i x, plus i x)
  map_add' x y := by
    funext i
    simp
  map_smul' scalar x := by
    funext i
    simp

/-- The paired energy is the positive-weighted finite sum of the two channel
norm squares. -/
def pairedComplexChannelEnergy
    {V Index : Type*} [AddCommGroup V] [Module ℂ V] [Fintype Index]
    (minus plus : Index → V →ₗ[ℂ] ℂ)
    (weight : Index → ℝ) (x : V) : ℝ :=
  ∑ i, weight i * (‖minus i x‖ ^ 2 + ‖plus i x‖ ^ 2)

/-- Strictly positive weights make the paired energy nonnegative, identify its
zero set with the common kernel of every channel, and make positive
definiteness equivalent to injectivity of the joint observation map. -/
theorem paired_complex_channel_completeness
    {V Index : Type*} [AddCommGroup V] [Module ℂ V] [Fintype Index]
    (minus plus : Index → V →ₗ[ℂ] ℂ)
    (weight : Index → ℝ) (hpositive : ∀ i, 0 < weight i) :
    {x | pairedComplexChannelEnergy minus plus weight x = 0} =
        {x | ∀ i, minus i x = 0 ∧ plus i x = 0} ∧
      ((∀ x, x ≠ 0 → 0 < pairedComplexChannelEnergy minus plus weight x) ↔
        Function.Injective (pairedComplexObservation minus plus)) := by
  classical
  have hnonnegative :
      ∀ x, 0 ≤ pairedComplexChannelEnergy minus plus weight x := by
    intro x
    unfold pairedComplexChannelEnergy
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (le_of_lt (hpositive i))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hkernel :
      {x | pairedComplexChannelEnergy minus plus weight x = 0} =
        {x | ∀ i, minus i x = 0 ∧ plus i x = 0} := by
    ext x
    constructor
    · intro henergy i
      have hterm :
          weight i * (‖minus i x‖ ^ 2 + ‖plus i x‖ ^ 2) = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
          mul_nonneg (le_of_lt (hpositive j))
            (add_nonneg (sq_nonneg _) (sq_nonneg _)))).mp
            henergy i (Finset.mem_univ i)
      have hpair :
          ‖minus i x‖ ^ 2 + ‖plus i x‖ ^ 2 = 0 :=
        (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hpositive i))
      have hminusSquare : ‖minus i x‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖minus i x‖, sq_nonneg ‖plus i x‖]
      have hplusSquare : ‖plus i x‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖minus i x‖, sq_nonneg ‖plus i x‖]
      exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp hminusSquare),
        norm_eq_zero.mp (sq_eq_zero_iff.mp hplusSquare)⟩
    · intro hchannels
      unfold pairedComplexChannelEnergy
      apply Finset.sum_eq_zero
      intro i hi
      simp [(hchannels i).1, (hchannels i).2]
  refine ⟨hkernel, ?_⟩
  constructor
  · intro hstrict x y hreadout
    by_contra hxy
    have hchannels :
        ∀ i, minus i (x - y) = 0 ∧ plus i (x - y) = 0 := by
      intro i
      have hi := congrFun hreadout i
      change (minus i x, plus i x) = (minus i y, plus i y) at hi
      constructor
      · rw [map_sub]
        exact sub_eq_zero.mpr (congrArg Prod.fst hi)
      · rw [map_sub]
        exact sub_eq_zero.mpr (congrArg Prod.snd hi)
    have henergy :
        pairedComplexChannelEnergy minus plus weight (x - y) = 0 := by
      have hmembership :
          x - y ∈ {z | ∀ i, minus i z = 0 ∧ plus i z = 0} :=
        hchannels
      rw [← hkernel] at hmembership
      exact hmembership
    exact (ne_of_gt (hstrict (x - y) (sub_ne_zero.mpr hxy))) henergy
  · intro hinjective x hx
    have henergyNonzero :
        pairedComplexChannelEnergy minus plus weight x ≠ 0 := by
      intro henergy
      have hmembership :
          x ∈ {z | pairedComplexChannelEnergy minus plus weight z = 0} :=
        henergy
      rw [hkernel] at hmembership
      have hchannels : ∀ i, minus i x = 0 ∧ plus i x = 0 :=
        hmembership
      have hreadout :
          pairedComplexObservation minus plus x =
            pairedComplexObservation minus plus (0 : V) := by
        funext i
        change (minus i x, plus i x) =
          (minus i (0 : V), plus i (0 : V))
        simp [(hchannels i).1, (hchannels i).2]
      exact hx (hinjective hreadout)
    exact lt_of_le_of_ne (hnonnegative x) (Ne.symm henergyNonzero)

#print axioms paired_complex_channel_completeness

end D5.S3.Weil.Pick.PairedComplexChannelCompleteness
