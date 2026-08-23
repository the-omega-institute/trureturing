/- GID: D5/S3/Observer/Prediction/RecursiveSignatureCompletion
   generality: G
   mirror-B: D5/B/S3/Observer/Prediction/RecursiveSignatureCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Recursive signatures recover finite-future classes and their stable completion. -/

import D5.S3.Observer.Separation.FiniteObservationRefinementBound

/- Library-search audit trail (2026-08-23):
   * Exact repository hits `finite_observation_refinement_and_stability_bound`,
     `PredictionState`, `finiteWordRangeEquiv`, `stableCompletionEquiv`, and
     `completionProjection` supply the canonical finite and completed quotients;
     they are imported and applied below rather than redeclared.
   * Exact pinned-Mathlib hits `Setoid.quotientKerEquivRange`, `Quotient.congr`,
     `Nat.sInf_mem`, and `Equiv.trans` construct the canonical realized-label
     equivalence and least stable stage; the quotient equivalences are applied below.
   * Repository and pinned-Mathlib searches found no exact theorem identifying
     recursively nested signature labels with every finite future readout word. -/

noncomputable section

namespace D5.S3.Observer.Prediction.RecursiveSignatureCompletion

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Refinement.GradedPredictionShift
open D5.S3.ObserverMemory.Refinement.PredictionCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- The raw recursive signature carrier: a current readout followed by the signature after one
update. This realizes canonical labels without choosing integer names for the classes. -/
def SignatureLabel (O : Type u) : Nat -> Type u
  | 0 => O
  | m + 1 => O × SignatureLabel O m

/-- The canonical recursive signature constructed only from update and readout. -/
def signatureLabel {Y O : Type*} (update : Y -> Y) (readout : Y -> O) :
    (m : Nat) -> Y -> SignatureLabel O m
  | 0 => readout
  | m + 1 => fun y => (readout y, signatureLabel update readout m (update y))

private theorem signature_label_eq_iff_finite_future {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) (y y' : Y) :
    signatureLabel update readout m y = signatureLabel update readout m y' <->
      (y, y') ∈ finiteFutureRelation update readout m := by
  induction m generalizing y y' with
  | zero =>
      rw [finite_relation_zero]
      rfl
  | succ m ih =>
      rw [finite_relation_succ]
      change
        (readout y, signatureLabel update readout m (update y)) =
            (readout y', signatureLabel update readout m (update y')) <->
          readout y = readout y' /\
            (update y, update y') ∈ finiteFutureRelation update readout m
      rw [Prod.mk.injEq]
      exact and_congr_right fun _ => ih (update y) (update y')

private theorem future_readout_word_eq_iff_finite_future {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) (y y' : Y) :
    futureReadoutWord update readout m y = futureReadoutWord update readout m y' <->
      (y, y') ∈ finiteFutureRelation update readout m := by
  constructor
  · intro hword k hk
    simpa only [futureReadoutWord, observedAt] using
      congrFun hword (show Fin (m + 1) from ⟨k, Nat.lt_succ_of_le hk⟩)
  · intro hfuture
    funext k
    simpa only [futureReadoutWord, observedAt] using
      hfuture k (Nat.le_of_lt_succ k.isLt)

private theorem signature_label_eq_iff_future_readout_word_eq {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) (y y' : Y) :
    signatureLabel update readout m y = signatureLabel update readout m y' <->
      futureReadoutWord update readout m y = futureReadoutWord update readout m y' :=
  (signature_label_eq_iff_finite_future update readout m y y').trans
    (future_readout_word_eq_iff_finite_future update readout m y y').symm

/-- Two consecutive recursive signatures induce the same state partition. -/
def signaturePartitionStableAt {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) : Prop :=
  forall y y',
    signatureLabel update readout (m + 1) y =
        signatureLabel update readout (m + 1) y' <->
      signatureLabel update readout m y = signatureLabel update readout m y'

/-- The first partition-stable recursive signature depth, using the source's adjacent-partition
test rather than a property of the desired completion. -/
def signatureStabilityDepth {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) : Nat :=
  sInf {m | signaturePartitionStableAt update readout m}

private theorem signature_partition_stable_iff_observation_setoid_eq {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    signaturePartitionStableAt update readout m <->
      observationSetoid update readout m =
        observationSetoid update readout (m + 1) := by
  constructor
  · intro hstable
    apply Setoid.ext
    intro y y'
    change
      futureReadoutWord update readout m y =
          futureReadoutWord update readout m y' <->
        futureReadoutWord update readout (m + 1) y =
          futureReadoutWord update readout (m + 1) y'
    calc
      futureReadoutWord update readout m y =
          futureReadoutWord update readout m y' <->
          signatureLabel update readout m y =
            signatureLabel update readout m y' :=
        (signature_label_eq_iff_future_readout_word_eq
          update readout m y y').symm
      _ <-> signatureLabel update readout (m + 1) y =
          signatureLabel update readout (m + 1) y' :=
        (hstable y y').symm
      _ <-> futureReadoutWord update readout (m + 1) y =
          futureReadoutWord update readout (m + 1) y' :=
        signature_label_eq_iff_future_readout_word_eq
          update readout (m + 1) y y'
  · intro hsetoid y y'
    have hpartition := Setoid.ext_iff.mp hsetoid y y'
    change
      signatureLabel update readout (m + 1) y =
          signatureLabel update readout (m + 1) y' <->
        signatureLabel update readout m y = signatureLabel update readout m y'
    calc
      signatureLabel update readout (m + 1) y =
          signatureLabel update readout (m + 1) y' <->
          futureReadoutWord update readout (m + 1) y =
            futureReadoutWord update readout (m + 1) y' :=
        signature_label_eq_iff_future_readout_word_eq
          update readout (m + 1) y y'
      _ <-> futureReadoutWord update readout m y =
          futureReadoutWord update readout m y' := hpartition.symm
      _ <-> signatureLabel update readout m y =
          signatureLabel update readout m y' :=
        (signature_label_eq_iff_future_readout_word_eq
          update readout m y y').symm

private theorem signature_stability_depth_eq_observation_stability_depth
    {Y O : Type*} (update : Y -> Y) (readout : Y -> O) :
    signatureStabilityDepth update readout =
      observationStabilityDepth update readout := by
  apply congrArg sInf
  ext m
  exact signature_partition_stable_iff_observation_setoid_eq update readout m

/-- The realized recursive labels at the algorithm's first stable partition. -/
def FinalSignatureLabels {Y O : Type*} (update : Y -> Y) (readout : Y -> O) :=
  Set.range
    (signatureLabel update readout (signatureStabilityDepth update readout))

private theorem observation_setoid_stable_at_depth
    {Y O : Type*} [Finite Y] [Finite O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    observationSetoid update readout
        (observationStabilityDepth update readout) =
      observationSetoid update readout
        (observationStabilityDepth update readout + 1) := by
  letI := Fintype.ofFinite Y
  letI := Fintype.ofFinite O
  exact
    (finite_observation_refinement_and_stability_bound
      update readout hreadout).2.2.1.1

/-- Realized signatures are canonically equivalent to the corresponding finite prediction
quotient. -/
def signatureRangePredictionEquiv {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    Set.range (signatureLabel update readout m) ≃
      PredictionState update readout m :=
  (Setoid.quotientKerEquivRange (signatureLabel update readout m)).symm |>.trans
    (Quotient.congr (Equiv.refl Y)
      (signature_label_eq_iff_future_readout_word_eq update readout m))

private theorem signature_range_prediction_equiv_apply {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) (y : Y) :
    signatureRangePredictionEquiv update readout m
        ⟨signatureLabel update readout m y, ⟨y, rfl⟩⟩ =
      (Quotient.mk _ y : PredictionState update readout m) := by
  change
    Quotient.congr (Equiv.refl Y)
        (signature_label_eq_iff_future_readout_word_eq update readout m)
        ((Setoid.quotientKerEquivRange
          (signatureLabel update readout m)).symm
          ⟨signatureLabel update readout m y, ⟨y, rfl⟩⟩) =
      Quotient.mk _ y
  have hrange :
      (Setoid.quotientKerEquivRange (signatureLabel update readout m)).symm
          ⟨signatureLabel update readout m y, ⟨y, rfl⟩⟩ =
        Quotient.mk _ y := by
    apply (Setoid.quotientKerEquivRange
      (signatureLabel update readout m)).injective
    simp only [Equiv.apply_symm_apply]
    rfl
  rw [hrange]
  rfl

/-- At any stable signature stage, its realized labels canonically identify with the complete
prediction quotient. -/
def signatureRangeCompletionEquiv {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout m) =
        Setoid.ker (futureReadoutWord update readout (m + 1))) :
    Set.range (signatureLabel update readout m) ≃ CompletedState update readout :=
  (signatureRangePredictionEquiv update readout m).trans
    (stableCompletionEquiv update readout m hstable)

private theorem signature_range_completion_equiv_apply {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout m) =
        Setoid.ker (futureReadoutWord update readout (m + 1)))
    (y : Y) :
    signatureRangeCompletionEquiv update readout m hstable
        ⟨signatureLabel update readout m y, ⟨y, rfl⟩⟩ =
      completionProjection update readout y := by
  change
    stableCompletionEquiv update readout m hstable
        (signatureRangePredictionEquiv update readout m
          ⟨signatureLabel update readout m y, ⟨y, rfl⟩⟩) =
      completionProjection update readout y
  rw [signature_range_prediction_equiv_apply]
  rfl

private theorem signature_setoid_stable_at_depth
    {Y O : Type*} [Finite Y] [Finite O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    Setoid.ker
        (futureReadoutWord update readout
          (signatureStabilityDepth update readout)) =
      Setoid.ker
        (futureReadoutWord update readout
          (signatureStabilityDepth update readout + 1)) := by
  change observationSetoid update readout
      (signatureStabilityDepth update readout) =
    observationSetoid update readout
      (signatureStabilityDepth update readout + 1)
  simpa [signature_stability_depth_eq_observation_stability_depth]
    using observation_setoid_stable_at_depth update readout hreadout

/-- The canonical equivalence from realized final signatures to complete-future state classes. It
is the first-isomorphism equivalence for the signature map, followed by relation congruence and
the existing stable finite-to-complete quotient equivalence. -/
def finalSignatureCompletionEquiv
    {Y O : Type*} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    FinalSignatureLabels update readout ≃ CompletedState update readout :=
  signatureRangeCompletionEquiv update readout
    (signatureStabilityDepth update readout)
    (signature_setoid_stable_at_depth update readout hreadout)

private theorem final_signature_completion_equiv_apply
    {Y O : Type*} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (y : Y) :
    finalSignatureCompletionEquiv update readout hreadout
        ⟨signatureLabel update readout (signatureStabilityDepth update readout) y,
          ⟨y, rfl⟩⟩ =
      completionProjection update readout y := by
  exact signature_range_completion_equiv_apply update readout
    (signatureStabilityDepth update readout)
    (signature_setoid_stable_at_depth update readout hreadout) y

/-- Recursive signatures recover exactly every finite-future partition; their first repeated
partition is the canonical stability depth; and the named final-label equivalence computes to the
canonical complete-future quotient projection on every state. -/
theorem recursive_signature_labels_stable_depth_and_completion
    {Y O : Type*} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    (forall m y y',
      signatureLabel update readout m y = signatureLabel update readout m y' <->
        (y, y') ∈ finiteFutureRelation update readout m) /\
    signatureStabilityDepth update readout =
      observationStabilityDepth update readout /\
    (let finalEquiv :
        FinalSignatureLabels update readout ≃ CompletedState update readout :=
        finalSignatureCompletionEquiv update readout hreadout
      forall y,
        finalEquiv
            ⟨signatureLabel update readout (signatureStabilityDepth update readout) y,
              ⟨y, rfl⟩⟩ =
          completionProjection update readout y) := by
  refine ⟨signature_label_eq_iff_finite_future update readout,
    signature_stability_depth_eq_observation_stability_depth update readout, ?_⟩
  dsimp only
  intro y
  exact final_signature_completion_equiv_apply update readout hreadout y

#print axioms recursive_signature_labels_stable_depth_and_completion

end D5.S3.Observer.Prediction.RecursiveSignatureCompletion
