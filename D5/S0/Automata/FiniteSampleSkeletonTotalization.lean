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

/-- Used signatures with their return coordinate in the ordinary state carrier. -/
abbrev ReturnPairFiber (skeleton : Skeleton Output State) :=
  {pair : Output × State //
    ∃ state, skeleton.oneSignature state = some (pair.1, some pair.2)}

noncomputable instance returnPairFiberFintype [Fintype Output] [Fintype State]
    (skeleton : Skeleton Output State) : Fintype (ReturnPairFiber skeleton) := by
  classical
  exact Fintype.ofFinite _

/-- Totality removes the optional-return wrapper without changing the set of
used signatures. This is the explicit carrier bridge to M18's output-return pairs. -/
def totalSignaturePairEquiv (skeleton : Skeleton Output State)
    (total : IsTotal skeleton) : SignatureFiber skeleton ≃ ReturnPairFiber skeleton where
  toFun := fun signature =>
    ⟨(signature.1.1, signature.1.2.getD skeleton.start), by
      obtain ⟨state, used⟩ := signature.2
      obtain ⟨output, next, defined⟩ := total.2 state
      have identified : signature.1 = (output, some next) :=
        Option.some.inj (used.symm.trans defined)
      refine ⟨state, ?_⟩
      simpa only [identified, Option.getD_some] using defined⟩
  invFun := fun pair => ⟨(pair.1.1, some pair.1.2), pair.2⟩
  left_inv := by
    intro signature
    apply Subtype.ext
    obtain ⟨state, used⟩ := signature.2
    obtain ⟨output, next, defined⟩ := total.2 state
    have identified : signature.1 = (output, some next) :=
      Option.some.inj (used.symm.trans defined)
    change (signature.1.1, some (signature.1.2.getD skeleton.start)) = signature.1
    rw [identified]
    rfl
  right_inv := by
    rintro ⟨⟨output, next⟩, used⟩
    rfl

/-- Canonical total state cost is precisely the recurrent count plus pair count. -/
theorem total_canonical_cost_eq_pair_cost [Fintype Output] [Fintype State]
    (skeleton : Skeleton Output State) (total : IsTotal skeleton) :
    Fintype.card (CanonicalState skeleton) =
      Fintype.card State + Fintype.card (ReturnPairFiber skeleton) := by
  rw [canonical_state_card_eq]
  rw [Fintype.card_congr (totalSignaturePairEquiv skeleton total)]

/-- Choose a recurrent state that requests a given used signature. -/
noncomputable def signatureSource (skeleton : Skeleton Output State)
    (signature : SignatureFiber skeleton) : State :=
  Classical.choose signature.2

/-- The chosen recurrent source requests the indexed signature. -/
theorem signatureSource_spec (skeleton : Skeleton Output State)
    (signature : SignatureFiber skeleton) :
    skeleton.oneSignature (signatureSource skeleton signature) = some signature.1 :=
  Classical.choose_spec signature.2

/-- Determinism permits at most one used signature per recurrent source. -/
theorem signatureSource_injective (skeleton : Skeleton Output State) :
    Function.Injective (signatureSource skeleton) := by
  intro left right equal
  apply Subtype.ext
  apply Option.some.inj
  calc
    some left.1 = skeleton.oneSignature (signatureSource skeleton left) :=
      (signatureSource_spec skeleton left).symm
    _ = skeleton.oneSignature (signatureSource skeleton right) :=
      congrArg skeleton.oneSignature equal
    _ = some right.1 := signatureSource_spec skeleton right

/-- Used transient signatures are bounded by the recurrent state count. -/
theorem signature_card_le_recurrent_card [Fintype Output] [Fintype State]
    (skeleton : Skeleton Output State) :
    Fintype.card (SignatureFiber skeleton) ≤ Fintype.card State := by
  exact Fintype.card_le_of_injective (signatureSource skeleton)
    (signatureSource_injective skeleton)

/-- The canonical typed machine has at most twice the recurrent state count. -/
theorem canonical_state_card_le_twice [Fintype Output] [Fintype State]
    (skeleton : Skeleton Output State) :
    Fintype.card (CanonicalState skeleton) ≤ 2 * Fintype.card State := by
  rw [canonical_state_card_eq, two_mul]
  exact Nat.add_le_add_left (signature_card_le_recurrent_card skeleton) _

section CapacityPadding

universe w

/- Continuation pre-registered in PR #5405, comment 5548870074 (2026-09-05).
   Library search `Skeleton padding` found no default-branch implementation.
   Escape witnesses: evaluation induction and the used-signature bijection.
   Consumer: M19.3 weighted fixed-capacity refutation encoding.
   Padding permits unreachable allocated states; it does not justify a SAT
   encoding that requires every allocated state to be reachable. -/

/-- Added recurrent states emulate the original start state. -/
def paddingCollapse (skeleton : Skeleton Output State) (Extra : Type w) :
    Sum State Extra → State
  | .inl state => state
  | .inr _ => skeleton.start

/-- Embed optional return targets in the original summand. -/
def paddingSignature (Extra : Type w) (signature : Output × Option State) :
    Output × Option (Sum State Extra) :=
  (signature.1, signature.2.map Sum.inl)

/-- Extra capacity is represented by copies of start-state behavior.
All defined transition targets lie in the original summand. -/
def padSkeleton (skeleton : Skeleton Output State) (Extra : Type w) :
    Skeleton Output (Sum State Extra) where
  start := .inl skeleton.start
  zeroStep := fun state =>
    (skeleton.zeroStep (paddingCollapse skeleton Extra state)).map Sum.inl
  oneSignature := fun state =>
    (skeleton.oneSignature (paddingCollapse skeleton Extra state)).map
      (paddingSignature Extra)
  zeroOutput := fun state => skeleton.zeroOutput (paddingCollapse skeleton Extra state)

/-- Padding preserves complete Option-valued evaluation from every state.
In particular, previously undefined evaluations remain undefined. -/
theorem eval_padSkeleton (skeleton : Skeleton Output State) (Extra : Type w)
    (state : Sum State Extra) (blocks : List ReturnBlock) (terminal : TerminalChannel) :
    (padSkeleton skeleton Extra).evalFrom state blocks terminal =
      skeleton.evalFrom (paddingCollapse skeleton Extra state) blocks terminal := by
  induction blocks generalizing state with
  | nil =>
      cases terminal with
      | recurrent => rfl
      | transient =>
          cases hs : skeleton.oneSignature (paddingCollapse skeleton Extra state) <;>
            simp [Skeleton.evalFrom, padSkeleton, paddingSignature, hs]
  | cons block blocks ih =>
      cases block with
      | zero =>
          cases hs : skeleton.zeroStep (paddingCollapse skeleton Extra state) with
          | none => simp [Skeleton.evalFrom, padSkeleton, hs]
          | some next =>
              simpa [Skeleton.evalFrom, padSkeleton, hs, paddingCollapse]
                using ih (Sum.inl next)
      | oneZero =>
          cases hs : skeleton.oneSignature (paddingCollapse skeleton Extra state) with
          | none => simp [Skeleton.evalFrom, padSkeleton, hs]
          | some signature =>
              cases hr : signature.2 with
              | none => simp [Skeleton.evalFrom, padSkeleton, paddingSignature, hs, hr]
              | some next =>
                  simpa [Skeleton.evalFrom, padSkeleton, paddingSignature, hs, hr,
                    paddingCollapse] using ih (Sum.inl next)

/-- Start-state evaluation is unchanged by padding. -/
theorem eval_padSkeleton_start (skeleton : Skeleton Output State) (Extra : Type w)
    (code : BlockCode) :
    (padSkeleton skeleton Extra).eval code = skeleton.eval code := by
  exact eval_padSkeleton skeleton Extra (.inl skeleton.start) code.blocks code.terminal

/-- Embedding a return target cannot identify distinct signatures. -/
theorem paddingSignature_injective (Extra : Type w) :
    Function.Injective (paddingSignature (Output := Output) (State := State) Extra) := by
  rintro ⟨leftOutput, leftReturn⟩ ⟨rightOutput, rightReturn⟩ equal
  cases leftReturn <;> cases rightReturn <;>
    simpa [paddingSignature] using equal

/-- Each originally used signature is still requested after padding. -/
def paddingSignatureMap (skeleton : Skeleton Output State) (Extra : Type w)
    (signature : SignatureFiber skeleton) : SignatureFiber (padSkeleton skeleton Extra) :=
  ⟨paddingSignature Extra signature.1, by
    obtain ⟨state, used⟩ := signature.2
    refine ⟨Sum.inl state, ?_⟩
    change (skeleton.oneSignature state).map (paddingSignature Extra) =
      some (paddingSignature Extra signature.1)
    rw [used]
    rfl⟩

/-- No two old signatures are merged by capacity padding. -/
theorem paddingSignatureMap_injective (skeleton : Skeleton Output State) (Extra : Type w) :
    Function.Injective (paddingSignatureMap skeleton Extra) := by
  intro left right equal
  apply Subtype.ext
  exact paddingSignature_injective Extra (congrArg Subtype.val equal)

/-- Every padded signature comes from an original recurrent source.
The extra states only repeat the start state's request, including when absent. -/
theorem paddingSignatureMap_surjective (skeleton : Skeleton Output State) (Extra : Type w) :
    Function.Surjective (paddingSignatureMap skeleton Extra) := by
  intro signature
  obtain ⟨state, used⟩ := signature.2
  have mapped : (skeleton.oneSignature (paddingCollapse skeleton Extra state)).map
      (paddingSignature Extra) = some signature.1 := used
  obtain ⟨original, oldUsed, equal⟩ := Option.map_eq_some_iff.mp mapped
  refine ⟨⟨original, ⟨paddingCollapse skeleton Extra state, oldUsed⟩⟩, ?_⟩
  apply Subtype.ext
  exact equal

/-- Extra recurrent capacity preserves the exact number of used signatures.
No nonempty-signature assumption is needed for padding. -/
theorem pad_signature_card_eq [Fintype Output] [Fintype State]
    (skeleton : Skeleton Output State) (Extra : Type w) [Fintype Extra] :
    Fintype.card (SignatureFiber (padSkeleton skeleton Extra)) =
      Fintype.card (SignatureFiber skeleton) := by
  apply Nat.le_antisymm
  · exact Fintype.card_le_of_surjective (paddingSignatureMap skeleton Extra)
      (paddingSignatureMap_surjective skeleton Extra)
  · exact Fintype.card_le_of_injective (paddingSignatureMap skeleton Extra)
      (paddingSignatureMap_injective skeleton Extra)

/-- Totality survives padding because each extra state emulates a total state. -/
theorem pad_isTotal (skeleton : Skeleton Output State) (Extra : Type w)
    (total : IsTotal skeleton) : IsTotal (padSkeleton skeleton Extra) := by
  constructor
  · intro state
    obtain ⟨next, defined⟩ := total.1 (paddingCollapse skeleton Extra state)
    refine ⟨Sum.inl next, ?_⟩
    change (skeleton.zeroStep (paddingCollapse skeleton Extra state)).map Sum.inl = _
    rw [defined]
    rfl
  · intro state
    obtain ⟨output, next, defined⟩ := total.2 (paddingCollapse skeleton Extra state)
    refine ⟨output, Sum.inl next, ?_⟩
    change (skeleton.oneSignature (paddingCollapse skeleton Extra state)).map
      (paddingSignature Extra) = _
    rw [defined]
    rfl

/-- An existing start-zero-loop remains a loop at the embedded start. -/
theorem pad_preserves_zero_loop (skeleton : Skeleton Output State) (Extra : Type w)
    (zeroLoop : skeleton.zeroStep skeleton.start = some skeleton.start) :
    (padSkeleton skeleton Extra).zeroStep (padSkeleton skeleton Extra).start =
      some (padSkeleton skeleton Extra).start := by
  change (skeleton.zeroStep skeleton.start).map Sum.inl = some (Sum.inl skeleton.start)
  rw [zeroLoop]
  rfl

/-- The start output, including a supplied zero anchor, is unchanged. -/
@[simp] theorem pad_start_output (skeleton : Skeleton Output State) (Extra : Type w) :
    (padSkeleton skeleton Extra).zeroOutput (padSkeleton skeleton Extra).start =
      skeleton.zeroOutput skeleton.start := rfl

/-- The only additional canonical cost is the explicitly allocated recurrent capacity. -/
theorem pad_canonical_state_card [Fintype Output] [Fintype State]
    (skeleton : Skeleton Output State) (Extra : Type w) [Fintype Extra] :
    Fintype.card (CanonicalState (padSkeleton skeleton Extra)) =
      Fintype.card (CanonicalState skeleton) + Fintype.card Extra := by
  rw [canonical_state_card_eq, canonical_state_card_eq, pad_signature_card_eq,
    Fintype.card_sum]
  omega

/-- Any larger recurrent capacity can represent the same partial behavior with
exactly the same signature count. This does not require all capacity states to be reachable. -/
theorem exists_fixed_capacity_padding [Fintype Output] [Fintype State]
    (skeleton : Skeleton Output State) (capacity : ℕ)
    (enough : Fintype.card State ≤ capacity) :
    ∃ padded : Skeleton Output (Sum State (Fin (capacity - Fintype.card State))),
      (∀ code, padded.eval code = skeleton.eval code) ∧
      Fintype.card (Sum State (Fin (capacity - Fintype.card State))) = capacity ∧
      Fintype.card (SignatureFiber padded) = Fintype.card (SignatureFiber skeleton) ∧
      (IsTotal skeleton → IsTotal padded) := by
  refine ⟨padSkeleton skeleton (Fin (capacity - Fintype.card State)), ?_, ?_, ?_, ?_⟩
  · exact eval_padSkeleton_start skeleton _
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · exact pad_signature_card_eq skeleton _
  · exact pad_isTotal skeleton _

/-- Arithmetic companion for the capacity consumer. The hypothesis `3 ≤ signatures`
must be proved from the chosen sample; it is not established by this theorem. -/
theorem budget_fourteen_capacity_cover (recurrent signatures : ℕ)
    (budget : recurrent + signatures ≤ 14)
    (sourceBound : signatures ≤ recurrent) (observedLower : 3 ≤ signatures) :
    (recurrent ≤ 7 ∧ signatures ≤ 7) ∨
    (recurrent = 8 ∧ signatures ≤ 6) ∨
    (recurrent = 9 ∧ signatures ≤ 5) ∨
    (recurrent = 10 ∧ signatures ≤ 4) ∨
    (recurrent = 11 ∧ signatures ≤ 3) := by
  omega

#print axioms eval_padSkeleton
#print axioms paddingSignatureMap_surjective
#print axioms pad_signature_card_eq
#print axioms exists_fixed_capacity_padding
#print axioms budget_fourteen_capacity_cover

end CapacityPadding

#print axioms totalSignaturePairEquiv
#print axioms canonical_state_card_le_twice
#print axioms totalization_preserves_success_and_cost
#print axioms exists_total_sample_realization
#print axioms empty_signature_cost_obstruction

end D5.S0.Automata.FiniteSampleSkeletonTotalization
