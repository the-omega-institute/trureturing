/- GID: D5/S3/ObserverMemory/Algorithms/ControlledSignatureStabilization
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/ControlledSignatureStabilization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Recursive controlled signatures stabilize at the complete behavior quotient. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod

/- Library-search audit trail (2026-08-18):
   * Repository search found the exact controlled-word semantics `runWord`,
     `controlledBehavior`, and `ControlledCompletion` in
     `ControlledBehaviorUniversality`; they are imported and reused below.
   * The autonomous `FiniteFutureCongruence` module is a supporting but
     non-exact hit for taking the latest first-separation time on a finite
     carrier. No repository theorem covers branching input words.
   * Pinned-Mathlib search exactly found `Function.ne_iff`, `Finset.le_sup`,
     `Nat.find_spec`, `Nat.find_min'`, and `Quotient.congrRight`; each is
     applied below. No exact theorem packages recursive controlled signatures,
     least finite stabilization, and the complete controlled quotient. -/

namespace D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- The type of recursively refined labels after a fixed number of rounds. -/
def Signature (U O : Type u) : Nat -> Type u
  | 0 => O
  | depth + 1 => O × (U -> Signature U O depth)

/-- The recursive signature algorithm: retain the current readout and append
the previous-round label of every controlled successor. -/
def controlledSignature {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) :
    (depth : Nat) -> Y -> Signature U O depth
  | 0, y => readout y
  | depth + 1, y =>
      (readout y, fun input =>
        controlledSignature update readout depth (update input y))

/-- The source's depth relation, constructed independently by testing every
input word whose length is at most the stated depth. -/
def boundedWordEquivalent {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O)
    (depth : Nat) (y y' : Y) : Prop :=
  forall word : List U, word.length <= depth ->
    readout (runWord update word y) = readout (runWord update word y')

/-- States modulo equality of their recursively computed depth signatures. -/
abbrev SignatureCompletion {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (depth : Nat) :=
  Quotient (Setoid.ker (controlledSignature update readout depth))

/-- The canonical output projection of the signature algorithm at one depth. -/
def signatureProjection {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (depth : Nat) :
    Y -> SignatureCompletion update readout depth :=
  Quotient.mk _

private theorem signature_correct_at_depth {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) :
    forall depth y y',
      controlledSignature update readout depth y =
          controlledSignature update readout depth y' <->
        boundedWordEquivalent update readout depth y y' := by
  intro depth
  induction depth with
  | zero =>
      intro y y'
      constructor
      · intro h word hlength
        have hword : word = [] :=
          List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlength)
        subst word
        simpa [controlledSignature, Signature, runWord] using h
      · intro h
        simpa [controlledSignature, Signature, runWord] using
          h [] (Nat.zero_le 0)
  | succ depth ih =>
      intro y y'
      constructor
      · intro h word hlength
        have hcurrent : readout y = readout y' := congrArg Prod.fst h
        have hsuccessors :
            (fun input => controlledSignature update readout depth (update input y)) =
              fun input => controlledSignature update readout depth (update input y') :=
          congrArg Prod.snd h
        cases word with
        | nil => simpa [runWord] using hcurrent
        | cons input tail =>
            have htail : tail.length <= depth := by
              simpa using Nat.le_of_succ_le_succ hlength
            have htailReadout :=
              (ih (update input y) (update input y')).mp
                (congrFun hsuccessors input) tail htail
            simpa [runWord] using htailReadout
      · intro h
        apply Prod.ext
        · simpa [controlledSignature, runWord] using
            h [] (Nat.zero_le (depth + 1))
        · funext input
          apply (ih (update input y) (update input y')).mpr
          intro word hlength
          have hbounded : (input :: word).length <= depth + 1 := by
            simpa using Nat.succ_le_succ hlength
          simpa [runWord] using h (input :: word) hbounded

/-- A word witnessing distinct complete behaviors, with the empty word used
only when the pair has identical complete behavior. -/
noncomputable def separatingWord {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (pair : Y × Y) : List U := by
  classical
  exact if h : controlledBehavior update readout pair.1 ≠
      controlledBehavior update readout pair.2 then
    Classical.choose (Function.ne_iff.mp h)
  else
    []

/-- The latest selected distinguishing-word length among all pairs. -/
noncomputable def distinguishingBound {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) : Nat :=
  Finset.univ.sup fun pair : Y × Y =>
    (separatingWord update readout pair).length

private theorem separating_word_spec {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (pair : Y × Y)
    (h : controlledBehavior update readout pair.1 ≠
      controlledBehavior update readout pair.2) :
    controlledBehavior update readout pair.1
        (separatingWord update readout pair) ≠
      controlledBehavior update readout pair.2
        (separatingWord update readout pair) := by
  classical
  simp only [separatingWord, dif_pos h]
  exact Classical.choose_spec (Function.ne_iff.mp h)

private theorem separating_word_length_le_bound
    {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) (pair : Y × Y) :
    (separatingWord update readout pair).length <=
      distinguishingBound update readout := by
  exact Finset.le_sup
    (f := fun statePair : Y × Y =>
      (separatingWord update readout statePair).length)
    (Finset.mem_univ pair)

/-- At a depth satisfying this predicate, recursive signature equality is
already exactly complete controlled-behavior equality. -/
def SignatureCompleteAt {Y : Type*} {U O : Type u}
    (update : U -> Y -> Y) (readout : Y -> O) (depth : Nat) : Prop :=
  forall y y',
    controlledSignature update readout depth y =
        controlledSignature update readout depth y' <->
      controlledBehavior update readout y =
        controlledBehavior update readout y'

private theorem complete_depth_exists {Y : Type*} {U O : Type u} [Finite Y]
    (update : U -> Y -> Y) (readout : Y -> O) :
    exists depth, SignatureCompleteAt update readout depth := by
  letI := Fintype.ofFinite Y
  refine ⟨distinguishingBound update readout, ?_⟩
  intro y y'
  constructor
  · intro hsignature
    by_contra hbehavior
    have hbounded :=
      (signature_correct_at_depth update readout
        (distinguishingBound update readout) y y').mp hsignature
    let word := separatingWord update readout (y, y')
    exact separating_word_spec update readout (y, y') hbehavior
      (hbounded word (separating_word_length_le_bound update readout (y, y')))
  · intro hbehavior
    apply (signature_correct_at_depth update readout
      (distinguishingBound update readout) y y').mpr
    intro word _
    exact congrFun hbehavior word

/-- The least round at which the recursive signatures capture every finite
controlled behavior. -/
noncomputable def stabilizationDepth {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) : Nat :=
  by
    classical
    exact Nat.find (complete_depth_exists update readout)

private theorem stabilization_depth_complete
    {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) :
    SignatureCompleteAt update readout
      (stabilizationDepth update readout) :=
  by
    classical
    exact Nat.find_spec (complete_depth_exists update readout)

private theorem signatures_stable_after_depth
    {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) (offset : Nat)
    (y y' : Y) :
    controlledSignature update readout
          (stabilizationDepth update readout + offset) y =
        controlledSignature update readout
          (stabilizationDepth update readout + offset) y' <->
      controlledSignature update readout
          (stabilizationDepth update readout) y =
        controlledSignature update readout
          (stabilizationDepth update readout) y' := by
  constructor
  · intro hlater
    apply (signature_correct_at_depth update readout
      (stabilizationDepth update readout) y y').mpr
    have hbounded := (signature_correct_at_depth update readout
      (stabilizationDepth update readout + offset) y y').mp hlater
    intro word hlength
    exact hbounded word (hlength.trans (Nat.le_add_right _ _))
  · intro hdepth
    apply (signature_correct_at_depth update readout
      (stabilizationDepth update readout + offset) y y').mpr
    have hbehavior :=
      (stabilization_depth_complete update readout y y').mp hdepth
    intro word _
    exact congrFun hbehavior word

/-- The canonical equivalence from the stabilized signature quotient to the
complete controlled behavior quotient. -/
noncomputable def stabilizedCompletionEquiv
    {Y : Type*} {U O : Type u} [Fintype Y]
    (update : U -> Y -> Y) (readout : Y -> O) :
    SignatureCompletion update readout (stabilizationDepth update readout) ≃
      ControlledCompletion update readout :=
  Quotient.congrRight fun y y' =>
    stabilization_depth_complete update readout y y'

/-- Recursive controlled signatures are correct at every depth. At the least
complete depth their equality relation is permanently stable, and their
quotient is canonically the complete controlled behavior space. -/
theorem controlled_signature_algorithm_correctness
    {Y : Type*} {U O : Type u} [Fintype Y] [Finite U] [Finite O]
    [Nonempty Y] [Nonempty U] [Nonempty O]
    (update : U -> Y -> Y) (readout : Y -> O)
    (_readoutSurjective : Function.Surjective readout) :
    (forall depth y y',
      controlledSignature update readout depth y =
          controlledSignature update readout depth y' <->
        boundedWordEquivalent update readout depth y y') /\
    (forall y y',
      controlledSignature update readout
            (stabilizationDepth update readout) y =
          controlledSignature update readout
            (stabilizationDepth update readout) y' <->
        controlledBehavior update readout y =
          controlledBehavior update readout y') /\
    (forall offset y y',
      controlledSignature update readout
            (stabilizationDepth update readout + offset) y =
          controlledSignature update readout
            (stabilizationDepth update readout + offset) y' <->
        controlledSignature update readout
            (stabilizationDepth update readout) y =
          controlledSignature update readout
            (stabilizationDepth update readout) y') /\
    (forall depth, SignatureCompleteAt update readout depth ->
      stabilizationDepth update readout <= depth) /\
    exists outputEquiv :
        SignatureCompletion update readout (stabilizationDepth update readout) ≃
          ControlledCompletion update readout,
      forall y,
        outputEquiv
            (signatureProjection update readout
              (stabilizationDepth update readout) y) =
          completionProjection update readout y := by
  classical
  refine ⟨signature_correct_at_depth update readout,
    stabilization_depth_complete update readout,
    signatures_stable_after_depth update readout, ?_, ?_⟩
  · intro depth hdepth
    exact Nat.find_min' (complete_depth_exists update readout) hdepth
  · refine ⟨stabilizedCompletionEquiv update readout, ?_⟩
    intro y
    rfl

/-- A two-state controlled system witnesses that the hypotheses are
satisfiable with a nonconstant readout. -/
example : Function.Surjective (id : Bool -> Bool) := Function.surjective_id

#print axioms controlled_signature_algorithm_correctness

end D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization
