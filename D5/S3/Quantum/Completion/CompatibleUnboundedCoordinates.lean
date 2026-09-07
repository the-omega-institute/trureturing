/- GID: D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates
   generality: I
   mirror-B: D5/B/S3/Quantum/Completion/CompatibleUnboundedCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:de2f7e3e5a2594df30db62adc8bb60c1f800096c292c11f096ebee34c5044ce4; result=D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.compatible_unbounded_coordinates
   digest: Actual first-coordinate projections are compatible but the partial-one family is unbounded and unrealizable. -/

import D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Real.Sqrt

noncomputable section

open Filter
open scoped BoundedContinuousFunction InnerProductSpace Topology

namespace D5.S3.Quantum.Completion.CompatibleUnboundedCoordinates

universe u
variable (K : Type u) [RCLike K]

/-- The span of exactly the first `n` standard coordinates in the actual Hilbert space. -/
def coordinateSpace (n : Nat) : Submodule K (lp (fun _ : Nat => K) 2) :=
  Submodule.span K (Set.range (fun i : Fin n =>
    lp.single (E := fun _ : Nat => K) 2 i.val (1 : K)))

/-- The actual finite sum of the first `n` coordinate unit vectors. -/
def partialOnes (n : Nat) : lp (fun _ : Nat => K) 2 :=
  ∑ i ∈ Finset.range n, lp.single 2 i (1 : K)

instance coordinateSpaceFiniteDimensional (n : Nat) :
    FiniteDimensional K (coordinateSpace K n) :=
  FiniteDimensional.span_of_finite K (Set.finite_range _)

instance coordinateSpaceHasOrthogonalProjection (n : Nat) :
    (coordinateSpace K n).HasOrthogonalProjection := by
  let := FiniteDimensional.complete K (coordinateSpace K n)
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

private theorem coordinate_sum_mem (n : Nat) (a : Nat → K) :
    (∑ i ∈ Finset.range n, lp.single 2 i (a i)) ∈ coordinateSpace K n := by
  apply Submodule.sum_mem
  intro i hi
  have hunit : lp.single (E := fun _ : Nat => K) 2 i (1 : K) ∈
      coordinateSpace K n :=
    Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  simpa only [← lp.single_smul, smul_eq_mul, mul_one] using
    (coordinateSpace K n).smul_mem (a i) hunit

private theorem coordinate_sum_apply (n : Nat) (a : Nat → K) (i : Nat) :
    (∑ j ∈ Finset.range n, lp.single (E := fun _ : Nat => K) 2 j (a j)) i =
      if i < n then a i else 0 := by
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single,
    Finset.mem_range]

/-- Orthogonal projection onto the independently defined coordinate span is truncation. -/
theorem coordinate_projection (n : Nat) (x : lp (fun _ : Nat => K) 2) :
    (coordinateSpace K n).starProjection x =
      ∑ i ∈ Finset.range n, lp.single 2 i (x i) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (coordinate_sum_mem K n x)
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    rw [lp.inner_single_right]
    change inner K (x i.val -
      (∑ j ∈ Finset.range n, lp.single 2 j (x j)) i.val) (1 : K) = 0
    rw [coordinate_sum_apply, if_pos i.isLt, sub_self, inner_zero_left]
  | zero => simp
  | add x y hx hy hx' hy' => simp [inner_add_right, hx', hy']
  | smul a x hx hx' => simp [inner_smul_right, hx']

private theorem partialOnes_apply (n i : Nat) :
    partialOnes K n i = if i < n then 1 else 0 :=
  coordinate_sum_apply K n (fun _ => 1) i

private theorem partialOnes_norm_sq (n : Nat) :
    ‖partialOnes K n‖ ^ 2 = (n : Real) := by
  simpa [partialOnes, Real.rpow_two] using
    lp.norm_sum_single (E := fun _ : Nat => K) (p := 2) (by norm_num)
      (fun _ => (1 : K)) (Finset.range n)

private theorem partialOnes_norm (n : Nat) :
    ‖partialOnes K n‖ = Real.sqrt n := by
  rw [← partialOnes_norm_sq K n, Real.sqrt_sq (norm_nonneg _)]

/-- The actual partial-one family is compatible at every earlier stage, but is neither
    the projections of an `lp` vector nor a member of the bounded inverse limit. -/
theorem compatible_unbounded_coordinates :
    Monotone (coordinateSpace K) ∧
    (∀ n, partialOnes K n ∈ coordinateSpace K n) ∧
    (∀ n i, partialOnes K n i = if i < n then 1 else 0) ∧
    (∀ m n, m ≤ n →
      (coordinateSpace K m).starProjection (partialOnes K n) = partialOnes K m) ∧
    (∀ n, ‖partialOnes K n‖ ^ 2 = (n : Real)) ∧
    (∀ n, ‖partialOnes K n‖ = Real.sqrt n) ∧
    Tendsto (fun n => ‖partialOnes K n‖) atTop atTop ∧
    ¬ BddAbove (Set.range (fun n => ‖partialOnes K n‖)) ∧
    (∀ x : lp (fun _ : Nat => K) 2, ∀ n,
      ‖(coordinateSpace K n).starProjection x‖ ≤ ‖x‖ ∧
      ‖(coordinateSpace K n).starProjection x‖ ^ 2 ≤ ‖x‖ ^ 2) ∧
    (¬ ∃ x : lp (fun _ : Nat => K) 2, ∀ n,
      (coordinateSpace K n).starProjection x = partialOnes K n) ∧
    (∀ x : lp (fun _ : Nat => K) 2, Summable (fun i => ‖x i‖ ^ 2)) ∧
    (¬ Summable (fun _ : Nat => ‖(1 : K)‖ ^ 2)) ∧
    (¬ Memℓp (fun _ : Nat => (1 : K)) 2) ∧
    (¬ ∃ z : BoundedInverseLimitReconstruction.boundedInverseLimit (coordinateSpace K),
      ∀ n, (z : Nat →ᵇ lp (fun _ : Nat => K) 2) n = partialOnes K n) := by
  have hdiv : Tendsto (fun n => ‖partialOnes K n‖) atTop atTop := by
    simpa only [partialOnes_norm, Function.comp_def] using
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := Real))
  have hunbounded := not_bddAbove_of_tendsto_atTop hdiv
  have hbound (x : lp (fun _ : Nat => K) 2) (n : Nat) :
      ‖(coordinateSpace K n).starProjection x‖ ≤ ‖x‖ ∧
      ‖(coordinateSpace K n).starProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have h := (coordinateSpace K n).norm_starProjection_apply_le x
    exact ⟨h, pow_le_pow_left₀ (norm_nonneg _) h 2⟩
  have hnotSummable : ¬ Summable (fun _ : Nat => ‖(1 : K)‖ ^ 2) := by
    simp [summable_const_iff]
  refine ⟨?_, (fun n => coordinate_sum_mem K n (fun _ => 1)), partialOnes_apply K,
    ?_, partialOnes_norm_sq K, partialOnes_norm K, hdiv, hunbounded, hbound,
    ?_, ?_, hnotSummable, ?_, ?_⟩
  · intro m n hmn
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hmn⟩, rfl⟩
  · intro m n hmn
    rw [coordinate_projection]
    change (∑ i ∈ Finset.range m, lp.single 2 i (partialOnes K n i)) =
      ∑ i ∈ Finset.range m, lp.single 2 i (1 : K)
    apply Finset.sum_congr rfl
    intro i hi
    rw [partialOnes_apply, if_pos (lt_of_lt_of_le (Finset.mem_range.mp hi) hmn)]
  · rintro ⟨x, hx⟩
    apply hunbounded
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    simpa only [hx n] using (hbound x n).1
  · intro x
    simpa [Real.rpow_two] using (lp.memℓp x).summable (by norm_num)
  · intro h
    apply hnotSummable
    simpa [Real.rpow_two] using h.summable (by norm_num)
  · rintro ⟨z, hz⟩
    apply hunbounded
    refine ⟨‖(z : Nat →ᵇ lp (fun _ : Nat => K) 2)‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    simpa only [hz n] using
      BoundedContinuousFunction.norm_coe_le_norm (z : Nat →ᵇ lp (fun _ : Nat => K) 2) n

end D5.S3.Quantum.Completion.CompatibleUnboundedCoordinates
