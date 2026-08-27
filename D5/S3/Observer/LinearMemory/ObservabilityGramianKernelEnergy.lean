/- GID: D5/S3/Observer/LinearMemory/ObservabilityGramianKernelEnergy
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/ObservabilityGramianKernelEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The stable ordinary Gramian kernel and zero form are exactly the all-future kernel. -/

import D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity
import D5.S3.ObserverMemory.Dynamics.MaximalUnobservableSubspace

/- Library-search audit trail (2026-08-28):
   * The frozen discounted-kernel theorem requires a strict discount below one,
     so it is not an exact hit for the source's ordinary stable Gramian.
   * Body-shape searches found the canonical `discountedObservabilityGramian`,
     `discountedGramianTerm`, `observedIterate`, and all-future kernel. The
     ordinary Gramian is their weight-one instance; no new definition is made.
   * Exact pinned-Mathlib component hits
     `ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right`,
     `ContinuousLinearMap.map_tsum`, and `Summable.tsum_pos` supply the term
     identity, energy sum, and strict zero test. No packaged ordinary theorem
     with all three public clauses was found. -/

namespace D5.S3.Observer.LinearMemory.ObservabilityGramianKernelEnergy

open InnerProductSpace RCLike
open scoped InnerProduct ComplexConjugate ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity

private theorem ordinary_gramian_term_energy
    {K V Y : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V]
    [NormedAddCommGroup Y] [InnerProductSpace K Y]
    [FiniteDimensional K Y]
    (T : V →ₗ[K] V) (C : V →ₗ[K] Y) (n : Nat) (x : V) :
    RCLike.re (inner K x (discountedGramianTerm T C 1 n x)) =
      ‖C ((T ^ n) x)‖ ^ 2 := by
  letI := FiniteDimensional.complete K V
  letI := FiniteDimensional.complete K Y
  rw [discountedGramianTerm]
  simp only [one_pow, RCLike.ofReal_one, one_smul]
  rw [← ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  rfl

/-- For the source's stable ordinary observability series, the Gramian kernel
is the canonical all-future readout kernel, its quadratic form is total future
output energy, and zero energy is equivalent to every future output vanishing. -/
theorem observability_gramian_kernel_energy
    {K V Y : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V]
    [NormedAddCommGroup Y] [InnerProductSpace K Y]
    [FiniteDimensional K Y]
    (T : V →ₗ[K] V) (C : V →ₗ[K] Y)
    (stable : Summable (discountedGramianTerm T C 1)) :
    LinearMap.ker (discountedObservabilityGramian T C 1).toLinearMap =
        (⨅ k : Nat, LinearMap.ker (C.comp (T ^ k))) ∧
      (forall x : V,
        RCLike.re (inner K x (discountedObservabilityGramian T C 1 x)) =
          ∑' k : Nat, ‖C ((T ^ k) x)‖ ^ 2) ∧
      (forall x : V,
        RCLike.re (inner K x (discountedObservabilityGramian T C 1 x)) = 0 ↔
          forall k : Nat, C ((T ^ k) x) = 0) := by
  letI := FiniteDimensional.complete K V
  letI := FiniteDimensional.complete K Y
  have energySummable (x : V) :
      Summable (fun n : Nat => ‖C ((T ^ n) x)‖ ^ 2) := by
    have applied := stable.mapL ((ContinuousLinearMap.apply K V) x)
    have paired := applied.mapL (innerSL K x)
    have realPart := paired.mapL RCLike.reCLM
    change Summable (fun n : Nat =>
      RCLike.re (inner K x (discountedGramianTerm T C 1 n x))) at realPart
    simpa only [ordinary_gramian_term_energy] using realPart
  have energyIdentity (x : V) :
      RCLike.re (inner K x (discountedObservabilityGramian T C 1 x)) =
        ∑' n : Nat, ‖C ((T ^ n) x)‖ ^ 2 := by
    rw [discountedObservabilityGramian]
    change RCLike.re (inner K x (((ContinuousLinearMap.apply K V) x)
      (∑' n : Nat, discountedGramianTerm T C 1 n))) =
        ∑' n : Nat, ‖C ((T ^ n) x)‖ ^ 2
    rw [((ContinuousLinearMap.apply K V) x).map_tsum stable]
    have applied := stable.mapL ((ContinuousLinearMap.apply K V) x)
    change RCLike.re ((innerSL K x)
      (∑' n : Nat, ((ContinuousLinearMap.apply K V) x)
        (discountedGramianTerm T C 1 n))) =
          ∑' n : Nat, ‖C ((T ^ n) x)‖ ^ 2
    rw [(innerSL K x).map_tsum applied]
    have paired := applied.mapL (innerSL K x)
    change RCLike.reCLM
      (∑' n : Nat, (innerSL K x) (((ContinuousLinearMap.apply K V) x)
        (discountedGramianTerm T C 1 n))) =
          ∑' n : Nat, ‖C ((T ^ n) x)‖ ^ 2
    rw [RCLike.reCLM.map_tsum paired]
    exact tsum_congr fun n => ordinary_gramian_term_energy T C n x
  constructor
  · apply le_antisymm
    · intro x xMem
      have gramianZero : discountedObservabilityGramian T C 1 x = 0 := by
        simpa [LinearMap.mem_ker] using xMem
      have energyZero : (∑' n : Nat, ‖C ((T ^ n) x)‖ ^ 2) = 0 := by
        rw [← energyIdentity x, gramianZero]
        simp
      apply (Submodule.mem_iInf _).mpr
      intro k
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      by_contra futureNonzero
      have termPositive : 0 < ‖C ((T ^ k) x)‖ ^ 2 :=
        sq_pos_of_pos (norm_pos_iff.mpr futureNonzero)
      have totalPositive : 0 < ∑' n : Nat, ‖C ((T ^ n) x)‖ ^ 2 :=
        (energySummable x).tsum_pos (fun n => sq_nonneg _) k termPositive
      exact totalPositive.ne energyZero.symm
    · intro x xMem
      rw [LinearMap.mem_ker]
      change discountedObservabilityGramian T C 1 x = 0
      rw [discountedObservabilityGramian]
      change ((ContinuousLinearMap.apply K V) x)
        (∑' n : Nat, discountedGramianTerm T C 1 n) = 0
      rw [((ContinuousLinearMap.apply K V) x).map_tsum stable]
      have termZero : forall n : Nat,
          discountedGramianTerm T C 1 n x = 0 := by
        intro n
        have future := (Submodule.mem_iInf _).mp xMem n
        have observedZero : observedIterate T C n x = 0 := by
          simpa [observedIterate, LinearMap.mem_ker, LinearMap.comp_apply] using future
        rw [discountedGramianTerm]
        simp [observedZero]
      calc
        (∑' n : Nat, discountedGramianTerm T C 1 n x) =
            ∑' _n : Nat, (0 : V) := tsum_congr termZero
        _ = 0 := tsum_zero
  · constructor
    · exact energyIdentity
    · intro x
      constructor
      · intro quadraticZero k
        by_contra futureNonzero
        have termPositive : 0 < ‖C ((T ^ k) x)‖ ^ 2 :=
          sq_pos_of_pos (norm_pos_iff.mpr futureNonzero)
        have totalPositive : 0 < ∑' n : Nat, ‖C ((T ^ n) x)‖ ^ 2 :=
          (energySummable x).tsum_pos (fun n => sq_nonneg _) k termPositive
        have totalZero : (∑' n : Nat, ‖C ((T ^ n) x)‖ ^ 2) = 0 := by
          rw [← energyIdentity x, quadraticZero]
        exact totalPositive.ne totalZero.symm
      · intro everyFutureZero
        calc
          RCLike.re (inner K x (discountedObservabilityGramian T C 1 x)) =
              ∑' n : Nat, ‖C ((T ^ n) x)‖ ^ 2 := energyIdentity x
          _ = 0 := by simp [everyFutureZero]

#print axioms observability_gramian_kernel_energy

end D5.S3.Observer.LinearMemory.ObservabilityGramianKernelEnergy
