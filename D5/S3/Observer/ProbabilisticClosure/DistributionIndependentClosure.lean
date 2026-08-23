/- GID: D5/S3/Observer/ProbabilisticClosure/DistributionIndependentClosure
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/DistributionIndependentClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distribution-independent readout closure is exactly deterministic depth-zero closure. -/

import D5.S3.Observer.Separation.FiniteObservationRefinementBound
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-23):
   * Repository searches found no exact distribution-independent kernel
     criterion. The existing observer SSOT supplies `observationStabilityDepth`
     and the theorem witnessing stability at that least depth; both are reused.
   * Pinned Mathlib exact hits `PMF.pure_map`, `PMF.pure_bind`,
     `PMF.bind_map`, `PMF.map_comp`, and `Nat.sInf_eq_zero` are applied below.
   * Pinned Mathlib and repository searches found no declaration combining the
     three equivalences with determinism and uniqueness of the effective kernel. -/

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.DistributionIndependentClosure

open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

/-- A readout kernel advances every initial law exactly as the hidden update
followed by the readout. -/
def IsEffectiveKernel {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (kernel : O -> PMF O) : Prop :=
  forall initial : PMF Y,
    (initial.map tau).map q = (initial.map q).bind kernel

private theorem pure_injective {O : Type*} :
    Function.Injective (@PMF.pure O) := by
  intro first second h
  have hsupport := congrArg (fun law : PMF O => law.support) h
  simpa using hsupport

private theorem effective_kernel_on_state {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) (kernel : O -> PMF O)
    (effective : IsEffectiveKernel tau q kernel) (y : Y) :
    kernel (q y) = PMF.pure (q (tau y)) := by
  simpa only [PMF.pure_map, PMF.pure_bind] using
    (effective (PMF.pure y)).symm

private theorem factor_of_effective_kernel {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) (q_surjective : Function.Surjective q)
    (kernel : O -> PMF O) (effective : IsEffectiveKernel tau q kernel) :
    exists sigma : O -> O, Function.Semiconj q tau sigma := by
  let sigma : O -> O := fun o => q (tau (Function.surjInv q_surjective o))
  refine ⟨sigma, fun y => ?_⟩
  have hstate := effective_kernel_on_state tau q kernel effective y
  have hsection := effective_kernel_on_state tau q kernel effective
    (Function.surjInv q_surjective (q y))
  rw [Function.surjInv_eq q_surjective] at hsection
  apply pure_injective
  exact hstate.symm.trans hsection

private theorem effective_kernel_of_factor {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) (sigma : O -> O)
    (factor : Function.Semiconj q tau sigma) :
    IsEffectiveKernel tau q (fun o => PMF.pure (sigma o)) := by
  intro initial
  rw [PMF.map_comp, PMF.bind_map]
  change initial.map (q ∘ tau) = initial.bind (PMF.pure ∘ (sigma ∘ q))
  rw [PMF.bind_pure_comp]
  exact congrArg (fun readout => initial.map readout) (funext factor)

private theorem depth_zero_of_factor {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) (sigma : O -> O)
    (factor : Function.Semiconj q tau sigma) :
    observationStabilityDepth tau q = 0 := by
  rw [observationStabilityDepth, Nat.sInf_eq_zero]
  left
  apply Setoid.ext
  intro y y'
  constructor
  · intro hzero
    have hcurrent : q y = q y' := by
      simpa [futureReadoutWord] using congrFun hzero (0 : Fin 1)
    funext k
    fin_cases k
    · simpa [futureReadoutWord] using hcurrent
    · change q (tau y) = q (tau y')
      exact (factor y).trans ((congrArg sigma hcurrent).trans (factor y').symm)
  · intro hone
    funext k
    have hk : k = (0 : Fin 1) := Fin.eq_zero k
    subst k
    simpa [futureReadoutWord] using congrFun hone (0 : Fin 2)

private theorem factor_of_depth_zero {Y O : Type*} [Finite Y] [Nonempty Y]
    (tau : Y -> Y) (q : Y -> O) (q_surjective : Function.Surjective q)
    (depth_zero : observationStabilityDepth tau q = 0) :
    exists sigma : O -> O, Function.Semiconj q tau sigma := by
  classical
  letI : Fintype Y := Fintype.ofFinite Y
  letI : Fintype O := Fintype.ofSurjective q q_surjective
  have hgeneral := finite_observation_refinement_and_stability_bound
    tau q q_surjective
  have hstable := hgeneral.2.2.1.1
  rw [depth_zero] at hstable
  let sigma : O -> O := fun o => q (tau (Function.surjInv q_surjective o))
  refine ⟨sigma, fun y => ?_⟩
  let representative := Function.surjInv q_surjective (q y)
  have hzero : observationSetoid tau q 0 y representative := by
    funext k
    have hk : k = (0 : Fin 1) := Fin.eq_zero k
    subst k
    simpa [futureReadoutWord, representative] using
      (Function.surjInv_eq q_surjective (q y)).symm
  have hone : observationSetoid tau q 1 y representative := by
    rw [← hstable]
    exact hzero
  simpa [futureReadoutWord, representative, sigma] using
    congrFun hone (1 : Fin 2)

private theorem deterministic_form_of_effective {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) (q_surjective : Function.Surjective q)
    (kernel : O -> PMF O) (effective : IsEffectiveKernel tau q kernel) :
    ∃! sigma : O -> O,
      Function.Semiconj q tau sigma /\
        forall o, kernel o = PMF.pure (sigma o) := by
  obtain ⟨sigma, factor⟩ :=
    factor_of_effective_kernel tau q q_surjective kernel effective
  refine ⟨sigma, ⟨factor, ?_⟩, ?_⟩
  · intro o
    obtain ⟨y, rfl⟩ := q_surjective o
    exact (effective_kernel_on_state tau q kernel effective y).trans
      (congrArg PMF.pure (factor y))
  · intro other hother
    funext o
    obtain ⟨y, rfl⟩ := q_surjective o
    exact ((factor y).symm.trans (hother.1 y)).symm

private theorem unique_effective_kernel {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) (q_surjective : Function.Surjective q)
    (exists_effective : exists kernel : O -> PMF O,
      IsEffectiveKernel tau q kernel) :
    ∃! kernel : O -> PMF O, IsEffectiveKernel tau q kernel := by
  obtain ⟨kernel, effective⟩ := exists_effective
  refine ⟨kernel, effective, ?_⟩
  intro other other_effective
  funext o
  obtain ⟨y, rfl⟩ := q_surjective o
  exact ((effective_kernel_on_state tau q kernel effective y).trans
    (effective_kernel_on_state tau q other other_effective y).symm).symm

/-- A finite surjective readout admits one distribution-independent Markov
closure exactly when it is already a deterministic factor, equivalently when
its future-word refinement depth is zero. Every effective kernel is the point
mass kernel of the unique factor update, and the effective kernel itself is
unique. -/
theorem distribution_independent_closure_criterion
    {Y O : Type*} [Finite Y] [Nonempty Y]
    (tau : Y -> Y) (q : Y -> O) (q_surjective : Function.Surjective q) :
    ((exists kernel : O -> PMF O, IsEffectiveKernel tau q kernel) <->
      exists sigma : O -> O, Function.Semiconj q tau sigma) /\
    ((exists sigma : O -> O, Function.Semiconj q tau sigma) <->
      observationStabilityDepth tau q = 0) /\
    (forall kernel : O -> PMF O, IsEffectiveKernel tau q kernel ->
      ∃! sigma : O -> O,
        Function.Semiconj q tau sigma /\
          forall o, kernel o = PMF.pure (sigma o)) /\
    ((exists kernel : O -> PMF O, IsEffectiveKernel tau q kernel) ->
      ∃! kernel : O -> PMF O, IsEffectiveKernel tau q kernel) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨kernel, effective⟩
      exact factor_of_effective_kernel tau q q_surjective kernel effective
    · rintro ⟨sigma, factor⟩
      exact ⟨fun o => PMF.pure (sigma o),
        effective_kernel_of_factor tau q sigma factor⟩
  · constructor
    · rintro ⟨sigma, factor⟩
      exact depth_zero_of_factor tau q sigma factor
    · exact factor_of_depth_zero tau q q_surjective
  · exact fun kernel effective =>
      deterministic_form_of_effective tau q q_surjective kernel effective
  · exact unique_effective_kernel tau q q_surjective

#print axioms distribution_independent_closure_criterion

end D5.S3.Observer.ProbabilisticClosure.DistributionIndependentClosure
