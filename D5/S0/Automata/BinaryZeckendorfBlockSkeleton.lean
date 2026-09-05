/- GID: D5/S0/Automata/BinaryZeckendorfBlockSkeleton
   generality: G
   mirror-B: D5/B/S0/Automata/BinaryZeckendorfBlockSkeleton
   mirror-E: none(waiver:first-return-skeleton)
   anchors: []
   digest: First-return codes and output-return signatures reconstruct typed binary Zeckendorf machines without increasing their state count. -/

import Mathlib
import D5.S0.Automata.TypedPartialDFAOOverBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.BinaryZeckendorfBlockSkeleton

open D5.S0.Automata.TypedPartialDFAOOverBase

universe u v

/-- The return blocks `0` and `10`. -/
inductive ReturnBlock
  | zero
  | oneZero
  deriving DecidableEq, Repr

instance : Fintype ReturnBlock where
  elems := {.zero, .oneZero}
  complete := by intro x; cases x <;> simp

/-- A code ends at the zero fiber or with a final one. -/
inductive TerminalChannel
  | recurrent
  | transient
  deriving DecidableEq, Repr

instance : Fintype TerminalChannel where
  elems := {.recurrent, .transient}
  complete := by intro x; cases x <;> simp

/-- Return blocks and a terminal channel. -/
structure BlockCode where
  blocks : List ReturnBlock
  terminal : TerminalChannel
  deriving DecidableEq, Repr

/-- Expand first-return coordinates. -/
def expand : List ReturnBlock → TerminalChannel → List (Fin 2)
  | [], .recurrent => []
  | [], .transient => [1]
  | .zero :: blocks, terminal => 0 :: expand blocks terminal
  | .oneZero :: blocks, terminal => 1 :: 0 :: expand blocks terminal

/-- Expand a packaged code. -/
def expandCode (code : BlockCode) : List (Fin 2) :=
  expand code.blocks code.terminal

/-- Parse return blocks, rejecting consecutive ones. -/
def decode : List (Fin 2) → Option BlockCode
  | [] => some ⟨[], .recurrent⟩
  | digit :: rest =>
      if digit = 0 then
        (decode rest).map fun code => {code with blocks := .zero :: code.blocks}
      else
        match rest with
        | [] => some ⟨[], .transient⟩
        | next :: tail =>
            if next = 0 then
              (decode tail).map fun code => {code with blocks := .oneZero :: code.blocks}
            else none

/-- Decoding is a left inverse of expansion. -/
@[simp] theorem decode_expand (code : BlockCode) :
    decode (expandCode code) = some code := by
  rcases code with ⟨blocks, terminal⟩
  change decode (expand blocks terminal) = some ⟨blocks, terminal⟩
  induction blocks with
  | nil => cases terminal <;> rfl
  | cons block blocks ih =>
      cases block with
      | zero =>
          change (decode (expand blocks terminal)).map
            (fun code => {code with blocks := .zero :: code.blocks}) = _
          rw [ih]
          rfl
      | oneZero =>
          change (decode (expand blocks terminal)).map
            (fun code => {code with blocks := .oneZero :: code.blocks}) = _
          rw [ih]
          rfl

/-- Expanded first-return codes are unique. -/
theorem expandCode_injective : Function.Injective expandCode := by
  intro left right h
  have h' := congrArg decode h
  simpa only [decode_expand, Option.some.injEq] using h'

/-- Words supplied with a first-return factorization. -/
def LegalWord :=
  {word : List (Fin 2) // ∃ code : BlockCode, expandCode code = word}

/-- A block code supplies its own factorization witness. -/
def legalWordOfCode (code : BlockCode) : LegalWord :=
  ⟨expandCode code, ⟨code, rfl⟩⟩

/-- The unique factorization of a word carrying a factorization witness. -/
noncomputable def compressLegalWord (word : LegalWord) : BlockCode :=
  Classical.choose word.2

/-- Expansion recovers the original word. -/
theorem expand_compressLegalWord (word : LegalWord) :
    expandCode (compressLegalWord word) = word.1 :=
  Classical.choose_spec word.2

/-- Compression recovers the original code. -/
theorem compressLegalWord_expand (code : BlockCode) :
    compressLegalWord (legalWordOfCode code) = code := by
  apply expandCode_injective
  exact expand_compressLegalWord (legalWordOfCode code)

/-- Base state of a terminal channel. -/
def terminalBaseState : TerminalChannel → BinaryZeckendorfState
  | .recurrent => .previousZero
  | .transient => .previousOne

/-- All expanded codes follow legal base transitions. -/
theorem binaryBase_evalFrom_expand
    (blocks : List ReturnBlock) (terminal : TerminalChannel) :
    binaryZeckendorfBase.evalFrom .previousZero (expand blocks terminal) =
      some (terminalBaseState terminal) := by
  induction blocks with
  | nil => cases terminal <;> rfl
  | cons block blocks ih => cases block <;> exact ih

/-- Start-state form of base acceptance. -/
theorem binaryBase_eval_expandCode (code : BlockCode) :
    binaryZeckendorfBase.eval (expandCode code) =
      some (terminalBaseState code.terminal) := by
  change binaryZeckendorfBase.evalFrom .previousZero
    (expand code.blocks code.terminal) = _
  exact binaryBase_evalFrom_expand code.blocks code.terminal

section Machine

variable {Output : Type u} {State : Type v}
variable (machine : TypedPartialDFAO binaryZeckendorfBase Output State)

/-- The fiber above the previous-zero base state. -/
abbrev ZeroFiber := {state : State // machine.stateType state = .previousZero}

/-- The fiber above the previous-one base state. -/
abbrev OneFiber := {state : State // machine.stateType state = .previousOne}

/-- Output evaluation from a specified state. -/
def evalFromState (state : State) (word : List (Fin 2)) : Option Output :=
  (machine.runFrom state word).map machine.output

/-- Lift the zero successor using the upstream proof-attaching operation. -/
def zeroSuccessor (state : ZeroFiber machine) : Option (ZeroFiber machine) :=
  (machine.step state.1 0).attachWith _ fun next h => by
    have typed := machine.step_type h
    simpa [binaryZeckendorfBase, state.2] using typed.symm

/-- Lift the one successor using its forced base type. -/
def oneSuccessor (state : ZeroFiber machine) : Option (OneFiber machine) :=
  (machine.step state.1 1).attachWith _ fun next h => by
    have typed := machine.step_type h
    simpa [binaryZeckendorfBase, state.2] using typed.symm

/-- The zero return from the previous-one fiber. -/
def returnSuccessor (state : OneFiber machine) : Option (ZeroFiber machine) :=
  (machine.step state.1 0).attachWith _ fun next h => by
    have typed := machine.step_type h
    simpa [binaryZeckendorfBase, state.2] using typed.symm

@[simp] theorem zeroSuccessor_map_val (state : ZeroFiber machine) :
    (zeroSuccessor machine state).map Subtype.val = machine.step state.1 0 := by
  exact Option.attachWith_map_subtype_val _ _

@[simp] theorem oneSuccessor_map_val (state : ZeroFiber machine) :
    (oneSuccessor machine state).map Subtype.val = machine.step state.1 1 := by
  exact Option.attachWith_map_subtype_val _ _

@[simp] theorem returnSuccessor_map_val (state : OneFiber machine) :
    (returnSuccessor machine state).map Subtype.val = machine.step state.1 0 := by
  exact Option.attachWith_map_subtype_val _ _

/-- A consecutive one has no typed successor. -/
theorem oneFiber_step_one_none (state : OneFiber machine) :
    machine.step state.1 1 = none := by
  cases h : machine.step state.1 1 with
  | none => rfl
  | some next =>
      have typed := machine.step_type h
      simp [binaryZeckendorfBase, state.2] at typed

/-- Complete output-and-return signature of a transient state. -/
def oneSignature (state : OneFiber machine) :
    Output × Option (ZeroFiber machine) :=
  (machine.output state.1, returnSuccessor machine state)

/-- Signature requested by a recurrent state's one transition. -/
def zeroOneSignature (state : ZeroFiber machine) :
    Option (Output × Option (ZeroFiber machine)) :=
  (oneSuccessor machine state).map (oneSignature machine)

/-- Equal transient signatures have equal output on every continuation. -/
theorem same_oneSignature_evalFromState
    (left right : OneFiber machine)
    (equal : oneSignature machine left = oneSignature machine right)
    (word : List (Fin 2)) :
    evalFromState machine left.1 word = evalFromState machine right.1 word := by
  have ho : machine.output left.1 = machine.output right.1 := congrArg Prod.fst equal
  have hr : returnSuccessor machine left = returnSuccessor machine right :=
    congrArg Prod.snd equal
  have hs : machine.step left.1 0 = machine.step right.1 0 := by
    calc
      _ = (returnSuccessor machine left).map Subtype.val :=
        (returnSuccessor_map_val machine left).symm
      _ = (returnSuccessor machine right).map Subtype.val := congrArg _ hr
      _ = _ := returnSuccessor_map_val machine right
  cases word with
  | nil => simpa [evalFromState, TypedPartialDFAO.runFrom, runTransition] using ho
  | cons digit tail =>
      fin_cases digit
      · simp [evalFromState, TypedPartialDFAO.runFrom, runTransition, hs]
      · simp [evalFromState, TypedPartialDFAO.runFrom, runTransition,
          oneFiber_step_one_none machine left, oneFiber_step_one_none machine right]

/-- Missing signatures correspond exactly to missing one transitions. -/
theorem zeroOneSignature_eq_none_iff (state : ZeroFiber machine) :
    zeroOneSignature machine state = none ↔ machine.step state.1 1 = none := by
  simp [zeroOneSignature, oneSuccessor]

/-- A requested signature is witnessed by an actual transient successor. -/
theorem zeroOneSignature_eq_some_iff (state : ZeroFiber machine)
    (signature : Output × Option (ZeroFiber machine)) :
    zeroOneSignature machine state = some signature ↔
      ∃ successor : OneFiber machine,
        machine.step state.1 1 = some successor.1 ∧
          oneSignature machine successor = signature := by
  simp only [zeroOneSignature, Option.map_eq_some_iff]
  constructor
  · rintro ⟨successor, hs, hv⟩
    exact ⟨successor, (Option.attachWith_eq_some_iff _).mp hs, hv⟩
  · rintro ⟨successor, hs, hv⟩
    exact ⟨successor, (Option.attachWith_eq_some_iff _).mpr hs, hv⟩

end Machine

/-- A first-return skeleton retains only the recurrent state carrier. -/
structure Skeleton (Output : Type u) (ZeroState : Type v) where
  start : ZeroState
  zeroStep : ZeroState → Option ZeroState
  oneSignature : ZeroState → Option (Output × Option ZeroState)
  zeroOutput : ZeroState → Output

namespace Skeleton

/-- Evaluate a first-return code from a selected recurrent state. -/
def evalFrom {Output : Type u} {ZeroState : Type v}
    (skeleton : Skeleton Output ZeroState) :
    ZeroState → List ReturnBlock → TerminalChannel → Option Output
  | state, [], .recurrent => some (skeleton.zeroOutput state)
  | state, [], .transient => (skeleton.oneSignature state).map Prod.fst
  | state, .zero :: blocks, terminal =>
      (skeleton.zeroStep state).bind fun next => evalFrom skeleton next blocks terminal
  | state, .oneZero :: blocks, terminal =>
      (skeleton.oneSignature state).bind fun signature =>
        signature.2.bind fun next => evalFrom skeleton next blocks terminal

/-- Evaluate from the start state. -/
def eval {Output : Type u} {ZeroState : Type v}
    (skeleton : Skeleton Output ZeroState) (code : BlockCode) : Option Output :=
  skeleton.evalFrom skeleton.start code.blocks code.terminal

end Skeleton

section Extract

variable {Output : Type u} {State : Type v}
variable (machine : TypedPartialDFAO binaryZeckendorfBase Output State)

/-- Extract first-return coordinates without changing the machine carrier. -/
def extractSkeleton : Skeleton Output (ZeroFiber machine) where
  start := ⟨machine.start, machine.start_type⟩
  zeroStep := zeroSuccessor machine
  oneSignature := zeroOneSignature machine
  zeroOutput := fun state => machine.output state.1

/-- Extraction preserves evaluation from every recurrent state. -/
theorem eval_extractSkeleton (state : ZeroFiber machine)
    (blocks : List ReturnBlock) (terminal : TerminalChannel) :
    (extractSkeleton machine).evalFrom state blocks terminal =
      evalFromState machine state.1 (expand blocks terminal) := by
  induction blocks generalizing state with
  | nil =>
      cases terminal with
      | recurrent => rfl
      | transient =>
          cases hs : zeroOneSignature machine state with
          | none =>
              have hstep := (zeroOneSignature_eq_none_iff machine state).mp hs
              simp [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                TypedPartialDFAO.runFrom, runTransition, hs, hstep]
          | some signature =>
              obtain ⟨next, hstep, hv⟩ :=
                (zeroOneSignature_eq_some_iff machine state signature).mp hs
              have ho : machine.output next.1 = signature.1 := congrArg Prod.fst hv
              simp [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                TypedPartialDFAO.runFrom, runTransition, hs, hstep, ho]
  | cons block blocks ih =>
      cases block with
      | zero =>
          cases hn : zeroSuccessor machine state with
          | none =>
              have hstep : machine.step state.1 0 = none := by
                simpa [hn] using (zeroSuccessor_map_val machine state).symm
              simp [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                TypedPartialDFAO.runFrom, runTransition, hn, hstep]
          | some next =>
              have hstep : machine.step state.1 0 = some next.1 := by
                simpa [hn] using (zeroSuccessor_map_val machine state).symm
              simpa [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                TypedPartialDFAO.runFrom, runTransition, hn, hstep] using ih next
      | oneZero =>
          cases hs : zeroOneSignature machine state with
          | none =>
              have hstep := (zeroOneSignature_eq_none_iff machine state).mp hs
              simp [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                TypedPartialDFAO.runFrom, runTransition, hs, hstep]
          | some signature =>
              obtain ⟨next, first, hv⟩ :=
                (zeroOneSignature_eq_some_iff machine state signature).mp hs
              have hr : returnSuccessor machine next = signature.2 := congrArg Prod.snd hv
              cases ht : signature.2 with
              | none =>
                  have second : machine.step next.1 0 = none := by
                    simpa [hr, ht] using (returnSuccessor_map_val machine next).symm
                  simp [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                    TypedPartialDFAO.runFrom, runTransition, hs, first, ht, second]
              | some target =>
                  have second : machine.step next.1 0 = some target.1 := by
                    simpa [hr, ht] using (returnSuccessor_map_val machine next).symm
                  simpa [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                    TypedPartialDFAO.runFrom, runTransition, hs, first, ht, second]
                    using ih target

/-- Start-state form of extraction agreement. -/
theorem eval_extractSkeleton_start (code : BlockCode) :
    (extractSkeleton machine).eval code = machine.evalOutput (expandCode code) := by
  exact eval_extractSkeleton machine (extractSkeleton machine).start
    code.blocks code.terminal

end Extract

section Canonical

variable {Output : Type u} {ZeroState : Type v}
variable (skeleton : Skeleton Output ZeroState)

/-- The distinct signatures actually requested by recurrent states. -/
abbrev SignatureFiber :=
  {signature : Output × Option ZeroState //
    ∃ state : ZeroState, skeleton.oneSignature state = some signature}

/-- Recurrent states plus one state for each distinct signature. -/
abbrev CanonicalState := Sum ZeroState (SignatureFiber skeleton)

/-- Base type of a canonical state. -/
def canonicalStateType : CanonicalState skeleton → BinaryZeckendorfState
  | .inl _ => .previousZero
  | .inr _ => .previousOne

/-- Typed signature selection, reusing `Option.attachWith`. -/
private def requestedSignature (state : ZeroState) : Option (SignatureFiber skeleton) :=
  (skeleton.oneSignature state).attachWith _ fun signature h => ⟨state, h⟩

/-- Canonical partial transitions. -/
def canonicalStep : CanonicalState skeleton → Fin 2 → Option (CanonicalState skeleton)
  | .inl state, digit =>
      if digit = 0 then (skeleton.zeroStep state).map Sum.inl
      else (requestedSignature skeleton state).map Sum.inr
  | .inr signature, digit =>
      if digit = 0 then signature.1.2.map Sum.inl else none

/-- Canonical Moore outputs. -/
def canonicalOutput : CanonicalState skeleton → Output
  | .inl state => skeleton.zeroOutput state
  | .inr signature => signature.1.1

/-- Every defined canonical transition respects the base automaton. -/
theorem canonicalStep_type
    {state next : CanonicalState skeleton} {digit : Fin 2}
    (defined : canonicalStep skeleton state digit = some next) :
    binaryZeckendorfBase.step (canonicalStateType skeleton state) digit =
      some (canonicalStateType skeleton next) := by
  rcases state with state | signature
  · fin_cases digit
    · have h : (skeleton.zeroStep state).map Sum.inl = some next := by
        simpa only [canonicalStep, if_pos rfl] using defined
      obtain ⟨target, _, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
    · have h : (requestedSignature skeleton state).map Sum.inr = some next := by
        simpa only [canonicalStep, show (1 : Fin 2) ≠ 0 by decide, if_false] using defined
      obtain ⟨target, _, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
  · fin_cases digit
    · have h : signature.1.2.map Sum.inl = some next := by
        simpa only [canonicalStep, if_pos rfl] using defined
      obtain ⟨target, _, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
    · simp only [canonicalStep, show (1 : Fin 2) ≠ 0 by decide, if_false] at defined

/-- Reconstruct the canonical typed machine. -/
def canonicalMachine :
    TypedPartialDFAO binaryZeckendorfBase Output (CanonicalState skeleton) where
  start := .inl skeleton.start
  stateType := canonicalStateType skeleton
  step := canonicalStep skeleton
  output := canonicalOutput skeleton
  start_type := rfl
  step_type := by
    intro state digit next defined
    exact canonicalStep_type skeleton defined

/-- Canonical evaluation agrees with the skeleton. -/
theorem eval_canonicalMachine_expand (state : ZeroState)
    (blocks : List ReturnBlock) (terminal : TerminalChannel) :
    evalFromState (canonicalMachine skeleton) (.inl state) (expand blocks terminal) =
      skeleton.evalFrom state blocks terminal := by
  induction blocks generalizing state with
  | nil =>
      cases terminal with
      | recurrent => rfl
      | transient =>
          cases hs : skeleton.oneSignature state <;>
            simp [evalFromState, Skeleton.evalFrom, expand, canonicalMachine,
              canonicalStep, requestedSignature, canonicalOutput,
              TypedPartialDFAO.runFrom, runTransition, hs]
  | cons block blocks ih =>
      cases block with
      | zero =>
          cases hn : skeleton.zeroStep state with
          | none =>
              simp [evalFromState, Skeleton.evalFrom, expand, canonicalMachine,
                canonicalStep, TypedPartialDFAO.runFrom, runTransition, hn]
          | some next =>
              simpa [evalFromState, Skeleton.evalFrom, expand, canonicalMachine,
                canonicalStep, TypedPartialDFAO.runFrom, runTransition, hn] using ih next
      | oneZero =>
          cases hs : skeleton.oneSignature state with
          | none =>
              simp [evalFromState, Skeleton.evalFrom, expand, canonicalMachine,
                canonicalStep, requestedSignature, TypedPartialDFAO.runFrom,
                runTransition, hs]
          | some signature =>
              cases ht : signature.2 with
              | none =>
                  simp [evalFromState, Skeleton.evalFrom, expand, canonicalMachine,
                    canonicalStep, requestedSignature, TypedPartialDFAO.runFrom,
                    runTransition, hs, ht]
              | some next =>
                  simpa [evalFromState, Skeleton.evalFrom, expand, canonicalMachine,
                    canonicalStep, requestedSignature, TypedPartialDFAO.runFrom,
                    runTransition, hs, ht] using ih next

/-- Start-state form of canonical evaluation. -/
theorem eval_canonicalMachine (code : BlockCode) :
    (canonicalMachine skeleton).evalOutput (expandCode code) = skeleton.eval code := by
  exact eval_canonicalMachine_expand skeleton skeleton.start code.blocks code.terminal

/-- Canonical reconstruction preserves a zero self-loop. -/
theorem canonicalMachine_start_zero_loop
    (zeroLoop : skeleton.zeroStep skeleton.start = some skeleton.start) :
    (canonicalMachine skeleton).step (canonicalMachine skeleton).start 0 =
      some (canonicalMachine skeleton).start := by
  simp [canonicalMachine, canonicalStep, zeroLoop]

@[simp] theorem canonicalMachine_start_output :
    (canonicalMachine skeleton).output (canonicalMachine skeleton).start =
      skeleton.zeroOutput skeleton.start := rfl

noncomputable instance signatureFiberFintype [Fintype Output] [Fintype ZeroState] :
    Fintype (SignatureFiber skeleton) := by
  classical
  exact Fintype.ofFinite _

/-- Exact cost of the canonical state carrier. -/
theorem canonical_state_card_eq [Fintype Output] [Fintype ZeroState] :
    Fintype.card (CanonicalState skeleton) =
      Fintype.card ZeroState + Fintype.card (SignatureFiber skeleton) := by
  simp

/-- Embed return signatures into the canonical zero fiber. -/
def canonicalSignatureEmbedding (signature : Output × Option ZeroState) :
    Output × Option (ZeroFiber (canonicalMachine skeleton)) :=
  (signature.1, signature.2.map fun state => ⟨Sum.inl state, rfl⟩)

/-- The canonical signature embedding is injective. -/
theorem canonicalSignatureEmbedding_injective :
    Function.Injective (canonicalSignatureEmbedding skeleton) := by
  rintro ⟨lo, lr⟩ ⟨ro, rr⟩ h
  have ho : lo = ro := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  cases lr with
  | none =>
      cases rr with
      | none => cases ho; rfl
      | some r => simp [canonicalSignatureEmbedding] at hr
  | some l =>
      cases rr with
      | none => simp [canonicalSignatureEmbedding] at hr
      | some r =>
          have hv : (Sum.inl l : CanonicalState skeleton) = Sum.inl r :=
            congrArg Subtype.val (Option.some.inj hr)
          have hlr : l = r := Sum.inl.inj hv
          cases ho
          cases hlr
          rfl

/-- Canonical transient state indexed by its used signature. -/
def canonicalOneState (signature : SignatureFiber skeleton) :
    OneFiber (canonicalMachine skeleton) := ⟨Sum.inr signature, rfl⟩

/-- Its actual transient signature is the expected embedded signature. -/
theorem oneSignature_canonicalOneState (signature : SignatureFiber skeleton) :
    oneSignature (canonicalMachine skeleton) (canonicalOneState skeleton signature) =
      canonicalSignatureEmbedding skeleton signature.1 := by
  rcases signature with ⟨⟨output, returnState⟩, witness⟩
  cases returnState <;>
    simp [canonicalOneState, oneSignature, returnSuccessor, canonicalMachine,
      canonicalStep, canonicalOutput, canonicalSignatureEmbedding]

/-- Distinct canonical transient states have distinct signatures. -/
theorem canonical_transient_signatures_injective :
    Function.Injective fun signature : SignatureFiber skeleton =>
      oneSignature (canonicalMachine skeleton) (canonicalOneState skeleton signature) := by
  intro left right h
  change oneSignature (canonicalMachine skeleton) (canonicalOneState skeleton left) =
    oneSignature (canonicalMachine skeleton) (canonicalOneState skeleton right) at h
  rw [oneSignature_canonicalOneState, oneSignature_canonicalOneState] at h
  exact Subtype.ext (canonicalSignatureEmbedding_injective skeleton h)

end Canonical

section Compression

variable {Output : Type u} {State : Type v}
variable (machine : TypedPartialDFAO binaryZeckendorfBase Output State)

/-- Every extracted signature has an original transient representative. -/
theorem signatureFiber_has_representative
    (signature : SignatureFiber (extractSkeleton machine)) :
    ∃ state : OneFiber machine, oneSignature machine state = signature.1 := by
  obtain ⟨zeroState, h⟩ := signature.2
  obtain ⟨oneState, _, hs⟩ :=
    (zeroOneSignature_eq_some_iff machine zeroState signature.1).mp h
  exact ⟨oneState, hs⟩

/-- Choose an original representative for each used signature. -/
noncomputable def signatureRepresentative
    (signature : SignatureFiber (extractSkeleton machine)) : OneFiber machine :=
  Classical.choose (signatureFiber_has_representative machine signature)

/-- The chosen representative has the indexed signature. -/
theorem signatureRepresentative_spec
    (signature : SignatureFiber (extractSkeleton machine)) :
    oneSignature machine (signatureRepresentative machine signature) = signature.1 :=
  Classical.choose_spec (signatureFiber_has_representative machine signature)

/-- Different signatures choose different representatives. -/
theorem signatureRepresentative_injective :
    Function.Injective (signatureRepresentative machine) := by
  intro left right h
  apply Subtype.ext
  calc
    left.1 = oneSignature machine (signatureRepresentative machine left) :=
      (signatureRepresentative_spec machine left).symm
    _ = oneSignature machine (signatureRepresentative machine right) := congrArg _ h
    _ = right.1 := signatureRepresentative_spec machine right

/-- Inject the canonical states into original states. -/
noncomputable def canonicalToOriginal :
    CanonicalState (extractSkeleton machine) → State
  | .inl state => state.1
  | .inr signature => (signatureRepresentative machine signature).1

/-- Type separation and representative injectivity prove state injectivity. -/
theorem canonicalToOriginal_injective : Function.Injective (canonicalToOriginal machine) := by
  intro left right h
  rcases left with l | l <;> rcases right with r | r
  · exact congrArg Sum.inl (Subtype.ext h)
  · change l.1 = (signatureRepresentative machine r).1 at h
    have ht := congrArg machine.stateType h
    rw [l.2, (signatureRepresentative machine r).2] at ht
    cases ht
  · change (signatureRepresentative machine l).1 = r.1 at h
    have ht := congrArg machine.stateType h
    rw [(signatureRepresentative machine l).2, r.2] at ht
    cases ht
  · exact congrArg Sum.inr
      (signatureRepresentative_injective machine (Subtype.ext h))

/-- Canonicalization never increases state cardinality. -/
theorem canonical_state_card_le [Fintype Output] [Fintype State] :
    Fintype.card (CanonicalState (extractSkeleton machine)) ≤ Fintype.card State := by
  exact Fintype.card_le_of_injective (canonicalToOriginal machine)
    (canonicalToOriginal_injective machine)

/-- The canonical machine preserves block-code behavior at no greater cost. -/
theorem canonical_extract_behavior_and_cardinality [Fintype Output] [Fintype State] :
    (∀ code : BlockCode,
      (canonicalMachine (extractSkeleton machine)).evalOutput (expandCode code) =
        machine.evalOutput (expandCode code)) ∧
    Fintype.card (CanonicalState (extractSkeleton machine)) ≤ Fintype.card State := by
  constructor
  · intro code
    exact (eval_canonicalMachine (extractSkeleton machine) code).trans
      (eval_extractSkeleton_start machine code)
  · exact canonical_state_card_le machine

/-- Extraction and reconstruction preserve the published zero-loop anchor. -/
theorem canonical_extract_start_zero_loop
    (zeroLoop : machine.step machine.start 0 = some machine.start) :
    (canonicalMachine (extractSkeleton machine)).step
      (canonicalMachine (extractSkeleton machine)).start 0 =
      some (canonicalMachine (extractSkeleton machine)).start := by
  apply canonicalMachine_start_zero_loop
  simp [extractSkeleton, zeroSuccessor, zeroLoop]

@[simp] theorem canonical_extract_start_output :
    (canonicalMachine (extractSkeleton machine)).output
      (canonicalMachine (extractSkeleton machine)).start = machine.output machine.start := rfl

#print axioms decode_expand
#print axioms same_oneSignature_evalFromState
#print axioms eval_extractSkeleton_start
#print axioms eval_canonicalMachine
#print axioms canonical_transient_signatures_injective
#print axioms canonical_extract_behavior_and_cardinality

end Compression
end D5.S0.Automata.BinaryZeckendorfBlockSkeleton
