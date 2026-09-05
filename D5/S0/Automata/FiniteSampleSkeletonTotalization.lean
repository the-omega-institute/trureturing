/- GID: D5/S0/Automata/FiniteSampleSkeletonTotalization
   generality: G
   mirror-B: D5/B/S0/Automata/FiniteSampleSkeletonTotalization
   mirror-E: none(waiver:constructive-totalization)
   anchors: []
   digest: A first-return skeleton with a used transient signature admits a total extension preserving all successful evaluations and not increasing canonical state cost. -/

import D5.S0.Automata.BinaryZeckendorfBlockSkeleton

/- Library-first audit (2026-09-05):
   * `BinaryZeckendorfBlockSkeleton.Skeleton`, `SignatureFiber`, `evalFrom`,
     and `canonical_state_card_eq` are reused without a parallel machine type.
   * Upstream `Option.bind_eq_some_iff`, `Option.map_eq_some_iff` and
     `Fintype.card_le_of_surjective` supply the decomposition and counting laws.
   * Repository searches for `Skeleton totalization` returned no matching
     successful-run-preserving, signature-cost-nonincreasing construction.
   * A used signature is necessary: a total one-channel on a nonempty carrier
     cannot retain an empty signature set. No undefined-run equivalence is asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.FiniteSampleSkeletonTotalization

open D5.S0.Automata.BinaryZeckendorfBlockSkeleton

universe u v

variable {Output : Type u} {State : Type v}

/-- Both return actions and the terminal-one channel are everywhere defined. -/
def IsTotal (skeleton : Skeleton Output State) : Prop :=
  (∀ state, ∃ next, skeleton.zeroStep state = some next) ∧
    ∀ state, ∃ output next,
      skeleton.oneSignature state = some (output, some next)

/-- Complete the return coordinate uniformly for each old signature. -/
def fillSignature (skeleton : Skeleton Output State)
    (signature : Output × Option State) : Output × Option State :=
  (signature.1, some (signature.2.getD skeleton.start))

/-- Fill missing zero transitions with the start state. Missing one channels
reuse one already used signature, so no new signature class is forced. -/
def totalize (skeleton : Skeleton Output State) (seed : SignatureFiber skeleton) :
    Skeleton Output State where
  start := skeleton.start
  zeroStep := fun state => some ((skeleton.zeroStep state).getD skeleton.start)
  oneSignature := fun state =>
    some (fillSignature skeleton ((skeleton.oneSignature state).getD seed.1))
  zeroOutput := skeleton.zeroOutput

/-- The explicit completion is total. -/
theorem totalize_isTotal (skeleton : Skeleton Output State)
    (seed : SignatureFiber skeleton) : IsTotal (totalize skeleton seed) := by
  constructor
  · intro state
    exact ⟨(skeleton.zeroStep state).getD skeleton.start, rfl⟩
  · intro state
    let signature := (skeleton.oneSignature state).getD seed.1
    exact ⟨signature.1, signature.2.getD skeleton.start, rfl⟩

/-- The start state is unchanged. -/
@[simp] theorem totalize_start (skeleton : Skeleton Output State)
    (seed : SignatureFiber skeleton) : (totalize skeleton seed).start = skeleton.start := rfl

/-- Recurrent outputs are unchanged. -/
@[simp] theorem totalize_zeroOutput (skeleton : Skeleton Output State)
    (seed : SignatureFiber skeleton) :
    (totalize skeleton seed).zeroOutput = skeleton.zeroOutput := rfl

/-- Every successful evaluation is preserved. Undefined evaluations may become
successful, so this statement deliberately uses implication rather than equality. -/
theorem totalize_preserves_success (skeleton : Skeleton Output State)
    (seed : SignatureFiber skeleton) (state : State)
    (blocks : List ReturnBlock) (terminal : TerminalChannel) (output : Output)
    (success : skeleton.evalFrom state blocks terminal = some output) :
    (totalize skeleton seed).evalFrom state blocks terminal = some output := by
  induction blocks generalizing state with
  | nil =>
      cases terminal with
      | recurrent => exact success
      | transient =>
          have h : (skeleton.oneSignature state).map Prod.fst = some output := success
          obtain ⟨signature, hs, ho⟩ := Option.map_eq_some_iff.mp h
          change some ((fillSignature skeleton
            ((skeleton.oneSignature state).getD seed.1)).1) = some output
          rw [hs]
          exact congrArg some ho
  | cons block blocks ih =>
      cases block with
      | zero =>
          have h : (skeleton.zeroStep state).bind
              (fun next => skeleton.evalFrom next blocks terminal) = some output := success
          obtain ⟨next, hs, ht⟩ := Option.bind_eq_some_iff.mp h
          change (totalize skeleton seed).evalFrom
            ((skeleton.zeroStep state).getD skeleton.start) blocks terminal = some output
          rw [hs]
          exact ih next ht
      | oneZero =>
          have h : (skeleton.oneSignature state).bind
              (fun signature => signature.2.bind
                (fun next => skeleton.evalFrom next blocks terminal)) = some output := success
          obtain ⟨signature, hs, ht⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨next, hr, successTail⟩ := Option.bind_eq_some_iff.mp ht
          change (totalize skeleton seed).evalFrom
            (((skeleton.oneSignature state).getD seed.1).2.getD skeleton.start)
            blocks terminal = some output
          rw [hs]
          change (totalize skeleton seed).evalFrom
            (signature.2.getD skeleton.start) blocks terminal = some output
          rw [hr]
          exact ih next successTail

/-- Start-state version for arbitrary code families, including finite samples. -/
theorem totalize_preserves_eval (skeleton : Skeleton Output State)
    (seed : SignatureFiber skeleton) (code : BlockCode) (output : Output)
    (success : skeleton.eval code = some output) :
    (totalize skeleton seed).eval code = some output := by
  exact totalize_preserves_success skeleton seed skeleton.start
    code.blocks code.terminal output success

/-- The published start-zero-loop convention is preserved. -/
theorem totalize_preserves_zero_loop (skeleton : Skeleton Output State)
    (seed : SignatureFiber skeleton)
    (zeroLoop : skeleton.zeroStep skeleton.start = some skeleton.start) :
    (totalize skeleton seed).zeroStep (totalize skeleton seed).start =
      some (totalize skeleton seed).start := by
  change some ((skeleton.zeroStep skeleton.start).getD skeleton.start) = some skeleton.start
  rw [zeroLoop]
  rfl

/-- Every old used signature maps to one used completed signature. -/
def completionMap (skeleton : Skeleton Output State) (seed : SignatureFiber skeleton)
    (signature : SignatureFiber skeleton) : SignatureFiber (totalize skeleton seed) :=
  ⟨fillSignature skeleton signature.1, by
    obtain ⟨state, hs⟩ := signature.2
    refine ⟨state, ?_⟩
    change some (fillSignature skeleton ((skeleton.oneSignature state).getD seed.1)) =
      some (fillSignature skeleton signature.1)
    rw [hs]
    rfl⟩

/-- Completion creates no signature outside the image of old used signatures.
The use of an old seed is essential in the missing-channel case. -/
theorem completionMap_surjective (skeleton : Skeleton Output State)
    (seed : SignatureFiber skeleton) :
    Function.Surjective (completionMap skeleton seed) := by
  intro completed
  obtain ⟨state, ht⟩ := completed.2
  cases hs : skeleton.oneSignature state with
  | none =>
      refine ⟨seed, ?_⟩
      apply Subtype.ext
      change fillSignature skeleton seed.1 = completed.1
      have h : some (fillSignature skeleton seed.1) = some completed.1 := by
        simpa only [totalize, hs, Option.getD_none] using ht
      exact Option.some.inj h
  | some signature =>
      refine ⟨⟨signature, ⟨state, hs⟩⟩, ?_⟩
      apply Subtype.ext
      change fillSignature skeleton signature = completed.1
      have h : some (fillSignature skeleton signature) = some completed.1 := by
        simpa only [totalize, hs, Option.getD_some] using ht
      exact Option.some.inj h

/-- The number of distinct transient signatures never increases. -/
theorem totalize_signature_card_le [Fintype Output] [Fintype State]
    (skeleton : Skeleton Output State) (seed : SignatureFiber skeleton) :
    Fintype.card (SignatureFiber (totalize skeleton seed)) ≤
      Fintype.card (SignatureFiber skeleton) := by
  exact Fintype.card_le_of_surjective (completionMap skeleton seed)
    (completionMap_surjective skeleton seed)

/-- Recurrent states are retained, and canonical total state cost does not grow. -/
theorem totalize_canonical_state_card_le [Fintype Output] [Fintype State]
    (skeleton : Skeleton Output State) (seed : SignatureFiber skeleton) :
    Fintype.card (CanonicalState (totalize skeleton seed)) ≤
      Fintype.card (CanonicalState skeleton) := by
  rw [canonical_state_card_eq, canonical_state_card_eq]
  exact Nat.add_le_add_left (totalize_signature_card_le skeleton seed) _

/-- A successful transient observation supplies the used-signature premise. -/
theorem signature_nonempty_of_transient_success
    (skeleton : Skeleton Output State) (state : State)
    (blocks : List ReturnBlock) (output : Output)
    (success : skeleton.evalFrom state blocks .transient = some output) :
    Nonempty (SignatureFiber skeleton) := by
  induction blocks generalizing state with
  | nil =>
      have h : (skeleton.oneSignature state).map Prod.fst = some output := success
      obtain ⟨signature, hs, _⟩ := Option.map_eq_some_iff.mp h
      exact ⟨⟨signature, ⟨state, hs⟩⟩⟩
  | cons block blocks ih =>
      cases block with
      | zero =>
          have h : (skeleton.zeroStep state).bind
              (fun next => skeleton.evalFrom next blocks .transient) = some output := success
          obtain ⟨next, _, ht⟩ := Option.bind_eq_some_iff.mp h
          exact ih next ht
      | oneZero =>
          have h : (skeleton.oneSignature state).bind
              (fun signature => signature.2.bind
                (fun next => skeleton.evalFrom next blocks .transient)) = some output := success
          obtain ⟨signature, hs, _⟩ := Option.bind_eq_some_iff.mp h
          exact ⟨⟨signature, ⟨state, hs⟩⟩⟩

/-- Totality itself forces a nonempty transient-signature set. -/
theorem signature_nonempty_of_total (skeleton : Skeleton Output State)
    (total : IsTotal skeleton) : Nonempty (SignatureFiber skeleton) := by
  obtain ⟨output, next, hs⟩ := total.2 skeleton.start
  exact ⟨⟨(output, some next), ⟨skeleton.start, hs⟩⟩⟩

/-- Zero signature cost cannot be preserved by a fully total completion. -/
theorem empty_signature_cost_obstruction [Fintype Output] [Fintype State]
    (original completed : Skeleton Output State)
    (empty : Fintype.card (SignatureFiber original) = 0)
    (total : IsTotal completed) :
    ¬ Fintype.card (SignatureFiber completed) ≤
      Fintype.card (SignatureFiber original) := by
  have positive : 0 < Fintype.card (SignatureFiber completed) :=
    Fintype.card_pos_iff.mpr (signature_nonempty_of_total completed total)
  rw [empty]
  exact Nat.not_le_of_gt positive

/-- Central constructive theorem: a used signature suffices for a total
extension preserving all successful code evaluations and canonical state cost. -/
theorem totalization_preserves_success_and_cost [Fintype Output] [Fintype State]
    (skeleton : Skeleton Output State) (seed : SignatureFiber skeleton) :
    IsTotal (totalize skeleton seed) ∧
    (totalize skeleton seed).start = skeleton.start ∧
    (totalize skeleton seed).zeroOutput = skeleton.zeroOutput ∧
    (∀ code output, skeleton.eval code = some output →
      (totalize skeleton seed).eval code = some output) ∧
    Fintype.card (CanonicalState (totalize skeleton seed)) ≤
      Fintype.card (CanonicalState skeleton) := by
  exact ⟨totalize_isTotal skeleton seed, rfl, rfl,
    totalize_preserves_eval skeleton seed,
    totalize_canonical_state_card_le skeleton seed⟩

/-- A sample family with one successful transient observation admits a total
realization of no larger canonical state cost whenever the partial one fits. -/
theorem exists_total_sample_realization [Fintype Output] [Fintype State]
    {Index : Type*} (skeleton : Skeleton Output State)
    (code : Index → BlockCode) (label : Index → Output)
    (fits : ∀ i, skeleton.eval (code i) = some (label i))
    (observed : Index) (transient : (code observed).terminal = .transient) :
    ∃ completed : Skeleton Output State,
      IsTotal completed ∧ completed.start = skeleton.start ∧
      completed.zeroOutput = skeleton.zeroOutput ∧
      (∀ i, completed.eval (code i) = some (label i)) ∧
      Fintype.card (CanonicalState completed) ≤
        Fintype.card (CanonicalState skeleton) := by
  have success : skeleton.evalFrom skeleton.start (code observed).blocks .transient =
      some (label observed) := by
    simpa only [Skeleton.eval, transient] using fits observed
  obtain ⟨seed⟩ := signature_nonempty_of_transient_success skeleton skeleton.start
    (code observed).blocks (label observed) success
  refine ⟨totalize skeleton seed, totalize_isTotal skeleton seed, rfl, rfl, ?_,
    totalize_canonical_state_card_le skeleton seed⟩
  intro i
  exact totalize_preserves_eval skeleton seed (code i) (label i) (fits i)

#print axioms totalization_preserves_success_and_cost
#print axioms exists_total_sample_realization
#print axioms empty_signature_cost_obstruction

end D5.S0.Automata.FiniteSampleSkeletonTotalization
