/- GID: D5/S3/Observer/Naturality/InvariantOriginRecoveryObstruction
   generality: G
   mirror-B: D5/B/S3/Observer/Naturality/InvariantOriginRecoveryObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A transitive invariant readout cannot recover or duplicate a nontrivial origin. -/

import D5.S3.Observer.Completion.StructuralCompletionSignature

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Naturality.InvariantOriginRecoveryObstruction

/- Library-search audit trail (2026-08-29):
   * The imported observer completion family already uses the canonical
     `MulAction.IsPretransitive` carrier; that action vocabulary is reused here.
   * Mathlib's exact supporting hit `MulAction.exists_smul_eq` supplies the orbit comparison.
   * Repository searches found no theorem packaging constant internal description, decoder
     impossibility, duplicator impossibility, and an explicit indistinguishable distinct pair. -/

/-- On a nontrivial transitive origin space, an invariant internal readout is constant. Hence it
has neither a left-inverse decoder nor a process producing two copies of every origin, and two
distinct origins have the same internal description. -/
theorem no_absolute_origin_reconstruction
    {G A Y : Type*} [Group G] [MulAction G A]
    [MulAction.IsPretransitive G A] [Nontrivial A]
    (readout : A -> Y)
    (invariant : forall (g : G) (a : A), readout (g • a) = readout a) :
    (forall a b : A, readout a = readout b) /\
    (Not (exists decoder : Y -> A, Function.LeftInverse decoder readout)) /\
    (Not (exists duplicate : Y -> A × A,
      forall a : A, duplicate (readout a) = (a, a))) /\
    (exists a b : A, Not (a = b) /\ readout a = readout b) := by
  have same_readout : forall a b : A, readout a = readout b := by
    intro a b
    obtain ⟨g, action_eq⟩ := MulAction.exists_smul_eq G a b
    calc
      readout a = readout (g • a) := (invariant g a).symm
      _ = readout b := congrArg readout action_eq
  obtain ⟨a, b, distinct⟩ := exists_pair_ne A
  refine ⟨same_readout, ?_, ?_, ⟨a, b, distinct, same_readout a b⟩⟩
  · rintro ⟨decoder, leftInverse⟩
    apply distinct
    calc
      a = decoder (readout a) := (leftInverse a).symm
      _ = decoder (readout b) := congrArg decoder (same_readout a b)
      _ = b := leftInverse b
  · rintro ⟨duplicate, duplicates⟩
    have pair_eq : (a, a) = (b, b) := by
      calc
        (a, a) = duplicate (readout a) := (duplicates a).symm
        _ = duplicate (readout b) := congrArg duplicate (same_readout a b)
        _ = (b, b) := duplicates b
    exact distinct (congrArg Prod.fst pair_eq)

#print axioms no_absolute_origin_reconstruction

end D5.S3.Observer.Naturality.InvariantOriginRecoveryObstruction
