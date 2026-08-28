/- GID: D5/S3/Observer/Completion/ThreeCompletionOrthogonality
   generality: I
   mirror-B: D5/B/S3/Observer/Completion/ThreeCompletionOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three tasks separate; identity under one readout still determines future behavior. -/
/- Library-search audit trail (2026-08-28):
   * The FPOD source was checked at `FORMAL_PRIME_OBSERVER_DYNAMICS.md`, Section 108.
   * D5 hits were `RationalValuationRecovery`, `DirichletUnitCompletion`,
     `LocalPrincipalityBlindness`, `PrincipalIdealCriterion`,
     `IdealIdentityPrincipalityGeneratorLayers`, and
     `FactorizedTranscriptKernelBarrier`; their declaration bodies were inspected and reused.
   * `ClassGroup.mk0_eq_one_iff`, `Ideal.IsPrincipal`, `Setoid.ker`, and
     `FractionalIdeal.coeIdeal_injective` were exact pinned-Mathlib hits.
   * Searches found no canonical `Function.fiber`; equality fibers are expressed by `Setoid.ker`.
   * No D5 theorem combined all three completion tasks or the directional implication audit. -/

import D5.S3.Factorization.Embeddings.DirichletUnitCompletion
import D5.S3.Factorization.IdealClassGroups.IdealIdentityPrincipalityGeneratorLayers
import D5.S3.Factorization.IdealClassGroups.LocalPrincipalityBlindness
import D5.S3.Observer.MeasureSeparation.FactorizedTranscriptKernelBarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped nonZeroDivisors

namespace D5.S3.Observer.Completion.ThreeCompletionOrthogonality

open D5.S3.Factorization.Embeddings.DirichletUnitCompletion
open D5.S3.Factorization.Embeddings.RationalValuationRecovery
open D5.S3.Factorization.IdealClassGroups.IdealIdentityPrincipalityGeneratorLayers
open D5.S3.Factorization.IdealClassGroups.LocalPrincipalityBlindness
open D5.S3.Observer.MeasureSeparation.FactorizedTranscriptKernelBarrier

/-- FPOD Definition 108.1: a readout completes identity when equal readouts force equality. -/
def IdentityCompletion {X Readout : Type*} (readout : X → Readout) : Prop :=
  Function.Injective readout

/-- FPOD Definition 108.2: every object has exactly one representative satisfying the relation. -/
def NormalizationCompletion {X Representative : Type*}
    (represents : X → Representative → Prop) : Prop :=
  ∀ object, ∃! representative, represents object representative

/-- The generator specialization of normalization completion for an ideal. -/
def GeneratorNormalizationCompletion {R : Type*} [CommSemiring R]
    (I : Ideal R) : Prop :=
  ∃! generator : R, Ideal.span {generator} = I

/-- FPOD Definition 108.3: future behavior is constant on every readout fiber. -/
def BehaviorCompletion {X Readout Future : Type*}
    (readout : X → Readout) (future : X → Future) : Prop :=
  ∀ x y, readout x = readout y → future x = future y

/-- Prime-ideal valuations identify one nonzero integral ideal among all such ideals. -/
def PrimeValuationIdentityCompletion {R : Type*}
    [CommRing R] [IsDedekindDomain R] (I : Ideal R) : Prop :=
  I ≠ ⊥ ∧
    ∀ (J : Ideal R), J ≠ ⊥ →
      (∀ prime : IsDedekindDomain.HeightOneSpectrum R,
        FractionalIdeal.count (FractionRing R) prime
            (J : FractionalIdeal R⁰ (FractionRing R)) =
          FractionalIdeal.count (FractionRing R) prime
            (I : FractionalIdeal R⁰ (FractionRing R))) →
      J = I

/-- The class-group layer decides whether one nonzero integral ideal is principal. -/
def ClassGroupPrincipalityDecision {R : Type*}
    [CommRing R] [IsDedekindDomain R] (I : Ideal R) : Prop :=
  ∃ hI : I ≠ ⊥,
    I.IsPrincipal ↔
      ClassGroup.mk0
        (show (Ideal R)⁰ from
          ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩) = 1

/-- A nontrivial class group supplies an ideal identified by all prime valuations but having no
global generator, hence no unique normalized generator. -/
theorem prime_valuation_identity_without_global_generator
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Nontrivial (ClassGroup R)] :
    ∃ I : Ideal R,
      PrimeValuationIdentityCompletion I ∧
        ¬ I.IsPrincipal ∧ ¬ GeneratorNormalizationCompletion I := by
  obtain ⟨I, _, hI, _, _⟩ :=
    local_principality_observers_are_blind_of_nontrivial_class_group (R := R)
  have hIne : I ≠ ⊥ := by
    intro hbot
    apply hI
    rw [hbot]
    exact bot_isPrincipal
  refine ⟨I, ⟨hIne, ?_⟩, hI, ?_⟩
  · intro J hJ sameValuation
    have hFractional :
        (J : FractionalIdeal R⁰ (FractionRing R)) =
          (I : FractionalIdeal R⁰ (FractionRing R)) :=
      congrArg Subtype.val
        (ideal_valuation_layer_recovers_fractional_ideal
          ⟨(J : FractionalIdeal R⁰ (FractionRing R)),
            FractionalIdeal.coeIdeal_ne_zero.mpr hJ⟩
          ⟨(I : FractionalIdeal R⁰ (FractionRing R)),
            FractionalIdeal.coeIdeal_ne_zero.mpr hIne⟩
          sameValuation)
    exact FractionalIdeal.coeIdeal_injective hFractional
  · rintro ⟨generator, generator_spec, _⟩
    exact hI ⟨generator, generator_spec.symm⟩
#print axioms prime_valuation_identity_without_global_generator

/-- The valuation/nonprincipal gap disappears over the PID `ℤ`; this is the concrete necessity
counterexample for the nontrivial-class-group hypothesis. -/
theorem nontrivial_class_group_is_necessary_for_valuation_generator_gap :
    ¬ ∃ I : Ideal ℤ,
      PrimeValuationIdentityCompletion I ∧ ¬ I.IsPrincipal := by
  rintro ⟨I, _, hI⟩
  exact nontrivial_class_group_is_necessary ⟨I, hI⟩
#print axioms nontrivial_class_group_is_necessary_for_valuation_generator_gap

/-- The ideal generated by the imported integer witnesses is class-group classified and
principal, but its two distinct generators rule out uniqueness. -/
theorem class_group_principality_without_unique_generator :
    ∃ I : Ideal ℤ,
      ClassGroupPrincipalityDecision I ∧ I.IsPrincipal ∧
        ¬ GeneratorNormalizationCompletion I := by
  obtain ⟨x, y, hxy, hspan⟩ := principality_does_not_determine_generator
  have hIne : Ideal.span {x} ≠ (⊥ : Ideal ℤ) := by
    intro hbot
    have hxzero : x = 0 := by
      have hxmem : x ∈ Ideal.span ({x} : Set ℤ) :=
        Ideal.subset_span (by simp)
      rw [hbot] at hxmem
      simpa using hxmem
    have hyzero : y = 0 := by
      have hymem : y ∈ Ideal.span ({y} : Set ℤ) :=
        Ideal.subset_span (by simp)
      rw [← hspan, hbot] at hymem
      simpa using hymem
    exact hxy (hxzero.trans hyzero.symm)
  refine ⟨Ideal.span {x}, ?_, ⟨x, rfl⟩, ?_⟩
  · refine ⟨hIne, ?_⟩
    exact (ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr hIne)).symm
  · rintro ⟨generator, generator_spec, unique⟩
    have hxg : x = generator := unique x rfl
    have hyg : y = generator := unique y hspan.symm
    exact hxy (hxg.trans hyg.symm)
#print axioms class_group_principality_without_unique_generator

/-- Every finite Boolean transcript, including the zero-sample transcript, closes through the
constant behavior quotient while its fiber contains the distinct states `false` and `true`. -/
theorem future_behavior_quotient_merges_micro_identity :
    ∀ n : Nat,
      KernelFactorsThrough booleanInterface
          (iidRepetition n constantBooleanTranscriptKernel) ∧
        BehaviorCompletion booleanInterface
          (iidRepetition n constantBooleanTranscriptKernel) ∧
        ∃ x y : Bool, x ≠ y ∧ Setoid.ker booleanInterface x y := by
  intro n
  have hOneShot :
      KernelFactorsThrough booleanInterface constantBooleanTranscriptKernel := by
    exact ⟨fun _ ↦ MeasureTheory.diracProba (), rfl⟩
  have hFactor := iid_repetition_preserves_factorization
    booleanInterface constantBooleanTranscriptKernel n hOneShot
  refine ⟨hFactor, ?_, ⟨false, true, by decide, rfl⟩⟩
  intro x y sameFiber
  exact factorized_repeated_kernel_eq_on_fiber
    booleanInterface (iidRepetition n constantBooleanTranscriptKernel)
      x y hFactor sameFiber
#print axioms future_behavior_quotient_merges_micro_identity

/-- Identity completion does not imply unique normalization: the identity readout on `Bool`
coexists with a two-valued indiscriminate representative relation. -/
theorem identity_completion_does_not_imply_normalization_completion :
    IdentityCompletion (id : Bool → Bool) ∧
      ¬ NormalizationCompletion (fun _ _ : Bool ↦ True) := by
  constructor
  · exact Function.injective_id
  · intro normalized
    obtain ⟨_, _, unique⟩ := normalized false
    have hfalse := unique false trivial
    have htrue := unique true trivial
    exact Bool.false_ne_true (hfalse.trans htrue.symm)
#print axioms identity_completion_does_not_imply_normalization_completion

/-- Unique normalization does not imply identity completion: equality supplies one representative
per Boolean object while the constant interface merges the objects. -/
theorem normalization_completion_does_not_imply_identity_completion :
    NormalizationCompletion (fun object representative : Bool ↦ representative = object) ∧
      ¬ IdentityCompletion booleanInterface := by
  constructor
  · intro object
    exact ⟨object, rfl, fun _ equality ↦ equality⟩
  · intro injective
    exact Bool.false_ne_true (injective rfl)
#print axioms normalization_completion_does_not_imply_identity_completion

/-- Unique normalization does not imply behavior completion: the same constant readout merges
states whose identity-valued futures differ. -/
theorem normalization_completion_does_not_imply_behavior_completion :
    NormalizationCompletion (fun object representative : Bool ↦ representative = object) ∧
      ¬ BehaviorCompletion booleanInterface booleanTarget := by
  constructor
  · intro object
    exact ⟨object, rfl, fun _ equality ↦ equality⟩
  · intro behavior
    exact Bool.false_ne_true (behavior false true rfl)
#print axioms normalization_completion_does_not_imply_behavior_completion

/-- Behavior completion does not imply identity completion: a constant future closes on the
constant Boolean interface, whose unique fiber still has two states. -/
theorem behavior_completion_does_not_imply_identity_completion :
    BehaviorCompletion booleanInterface (fun _ : Bool ↦ ()) ∧
      ¬ IdentityCompletion booleanInterface := by
  constructor
  · intro _ _ _
    rfl
  · intro injective
    exact Bool.false_ne_true (injective rfl)
#print axioms behavior_completion_does_not_imply_identity_completion

/-- Behavior completion does not imply unique normalization: constant behavior coexists with a
two-valued indiscriminate representative relation. -/
theorem behavior_completion_does_not_imply_normalization_completion :
    BehaviorCompletion booleanInterface (fun _ : Bool ↦ ()) ∧
      ¬ NormalizationCompletion (fun _ _ : Bool ↦ True) := by
  constructor
  · intro _ _ _
    rfl
  · intro normalized
    obtain ⟨_, _, unique⟩ := normalized false
    have hfalse := unique false trivial
    have htrue := unique true trivial
    exact Bool.false_ne_true (hfalse.trans htrue.symm)
#print axioms behavior_completion_does_not_imply_normalization_completion

/-- Honest missing direction: for one deterministic readout, identity completion always implies
behavior completion for every future map, so no counterexample to this direction exists. -/
theorem same_readout_identity_implies_behavior_completion
    {X Readout Future : Type*} (readout : X → Readout) (future : X → Future) :
    IdentityCompletion readout → BehaviorCompletion readout future := by
  intro injective x y sameReadout
  exact congrArg future (injective sameReadout)
#print axioms same_readout_identity_implies_behavior_completion

/- Degenerate audit: empty state types make identity and behavior clauses vacuous. -/
example {Readout Future : Type*} (readout : Empty → Readout) (future : Empty → Future) :
    IdentityCompletion readout ∧ BehaviorCompletion readout future := by
  constructor
  · intro x
    exact Empty.elim x
  · intro x
    exact Empty.elim x

/- Degenerate audit: all three tasks hold on singleton carriers with equality representatives. -/
example :
    IdentityCompletion (id : Unit → Unit) ∧
      NormalizationCompletion
        (fun object representative : Unit ↦ representative = object) ∧
      BehaviorCompletion (id : Unit → Unit) (id : Unit → Unit) := by
  constructor
  · exact Function.injective_id
  constructor
  · rintro ⟨⟩
    exact ⟨(), rfl, fun representative _ ↦ Subsingleton.elim representative ()⟩
  · intro _ _ equality
    exact equality

/- Degenerate audit at `K = ℚ`: finite valuations merge `1` and `-1`; the sign coordinate is
exactly the missing layer, while the free Dirichlet unit rank is zero. -/
example :
    NumberField.Units.rank ℚ = 0 ∧
      rationalFiniteValuationProfile 1 = rationalFiniteValuationProfile (-1) ∧
      ((1 : ℚ) = -1 ↔ SignType.sign (1 : ℚ) = SignType.sign (-1 : ℚ)) := by
  have hProfile := sign_equality_is_necessary
  exact ⟨rational_unit_rank_zero, hProfile.1,
    rational_two_layer_recovery_iff_sign hProfile.1⟩

/- Degenerate audit at `n = 0`: the behavior quotient still merges the Boolean states. -/
example :
    BehaviorCompletion booleanInterface
      (iidRepetition 0 constantBooleanTranscriptKernel) :=
  (future_behavior_quotient_merges_micro_identity 0).2.1

/- Assumption and primality audit:
   * `CommRing R` is definitional for ideals, fraction rings, and the class group.
   * `IsDedekindDomain R` is consumed by the prime-valuation reconstruction and `ClassGroup.mk0`.
   * `Nontrivial (ClassGroup R)` is consumed only to obtain a nonprincipal ideal; the named
     integer theorem above proves that this strictness disappears when the class group is trivial.
   * Height-one-spectrum primality is load-bearing only in the valuation witness. The class-group
     criterion uses Dedekind invertibility but no prime distribution. The rational audit invokes
     the imported `padicValRat` profile. No primality or number-field assumption reaches behavior.
   * No public theorem assumes a nonempty state space. Empty, singleton, constant, identity, and
     zero-sample cases are checked above. There is no other natural-number parameter. -/

end D5.S3.Observer.Completion.ThreeCompletionOrthogonality
