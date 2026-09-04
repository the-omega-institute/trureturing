/- GID: D5/S0/Automata/BinaryZeckendorfBlockSkeleton
   generality: G
   mirror-B: D5/B/S0/Automata/BinaryZeckendorfBlockSkeleton
   mirror-E: none(waiver:first-return-skeleton)
   anchors: [mathlib/module/Mathlib]
   digest: Legal binary Zeckendorf words factor uniquely into the return blocks 0 and 10 with an optional terminal 1; the transient state fiber of every typed DFAO is quotiented by its output-and-zero-successor signature, yielding an equivalent canonical skeleton machine with no more states. -/

import Mathlib
import D5.S0.Automata.TypedPartialDFAOOverBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.BinaryZeckendorfBlockSkeleton

open D5.S0.Automata.TypedPartialDFAOOverBase

universe u v

/-- The two first-return blocks from the `previousZero` state of the binary
Zeckendorf validity automaton. -/
inductive ReturnBlock
  | zero
  | oneZero
  deriving DecidableEq, Fintype, Repr

/-- A legal word either returns to the recurrent base state or ends with one
final `1` in the transient base state. -/
inductive TerminalChannel
  | recurrent
  | transient
  deriving DecidableEq, Fintype, Repr

/-- A word over the return-block alphabet together with its terminal channel. -/
structure BlockCode where
  blocks : List ReturnBlock
  terminal : TerminalChannel
  deriving DecidableEq, Repr

/-- Expand return blocks back to the original binary alphabet. -/
def expand : List ReturnBlock → TerminalChannel → List (Fin 2)
  | [], .recurrent => []
  | [], .transient => [1]
  | .zero :: blocks, terminal => 0 :: expand blocks terminal
  | .oneZero :: blocks, terminal => 1 :: 0 :: expand blocks terminal

/-- Expansion of a packaged block code. -/
def expandCode (code : BlockCode) : List (Fin 2) :=
  expand code.blocks code.terminal

/-- Parse a legal binary Zeckendorf word into first-return blocks. Consecutive
ones are rejected. -/
def decode : List (Fin 2) → Option BlockCode
  | [] => some ⟨[], .recurrent⟩
  | digit :: rest =>
      if digit = 0 then
        (decode rest).map fun code =>
          { code with blocks := .zero :: code.blocks }
      else
        match rest with
        | [] => some ⟨[], .transient⟩
        | next :: tail =>
            if next = 0 then
              (decode tail).map fun code =>
                { code with blocks := .oneZero :: code.blocks }
            else
              none

/-- Decoding is a left inverse of block expansion. -/
@[simp] theorem decode_expand (code : BlockCode) :
    decode (expandCode code) = some code := by
  rcases code with ⟨blocks, terminal⟩
  induction blocks with
  | nil =>
      cases terminal <;> simp [expandCode, expand, decode]
  | cons block blocks inductionHypothesis =>
      cases block <;>
        simp [expandCode, expand, decode, inductionHypothesis]

/-- The first-return expansion is injective. -/
theorem expandCode_injective : Function.Injective expandCode := by
  intro left right equal
  have someEqual : some left = some right := by
    calc
      some left = decode (expandCode left) := (decode_expand left).symm
      _ = decode (expandCode right) := by rw [equal]
      _ = some right := decode_expand right
  exact Option.some.inj someEqual

/-- Binary words lying in the image of the first-return expansion. -/
def LegalWord :=
  {word : List (Fin 2) // ∃ code : BlockCode, expandCode code = word}

/-- Package any block code as a legal word. -/
def legalWordOfCode (code : BlockCode) : LegalWord :=
  ⟨expandCode code, ⟨code, rfl⟩⟩

/-- The unique block code of a legal word. -/
noncomputable def compressLegalWord (word : LegalWord) : BlockCode :=
  Classical.choose word.2

/-- Compression followed by expansion recovers a legal word. -/
theorem expand_compressLegalWord (word : LegalWord) :
    expandCode (compressLegalWord word) = word.1 :=
  Classical.choose_spec word.2

/-- Expansion followed by compression recovers the original block code. -/
theorem compressLegalWord_expand (code : BlockCode) :
    compressLegalWord (legalWordOfCode code) = code := by
  apply expandCode_injective
  exact expand_compressLegalWord (legalWordOfCode code)

/-- Base state selected by the terminal channel. -/
def terminalBaseState : TerminalChannel → BinaryZeckendorfState
  | .recurrent => .previousZero
  | .transient => .previousOne

/-- Every expanded block code is accepted by the binary Zeckendorf base
machine, ending in the base state specified by its terminal channel. -/
theorem binaryBase_evalFrom_expand
    (blocks : List ReturnBlock) (terminal : TerminalChannel) :
    binaryZeckendorfBase.evalFrom .previousZero (expand blocks terminal) =
      some (terminalBaseState terminal) := by
  induction blocks with
  | nil =>
      cases terminal <;>
        simp [expand, terminalBaseState, PartialDFA.evalFrom,
          runTransition, binaryZeckendorfBase]
  | cons block blocks inductionHypothesis =>
      cases block <;>
        simpa [expand, PartialDFA.evalFrom, runTransition,
          binaryZeckendorfBase] using inductionHypothesis

/-- Packaged form of `binaryBase_evalFrom_expand`. -/
theorem binaryBase_eval_expandCode (code : BlockCode) :
    binaryZeckendorfBase.eval (expandCode code) =
      some (terminalBaseState code.terminal) := by
  simpa [PartialDFA.eval, expandCode] using
    binaryBase_evalFrom_expand code.blocks code.terminal

section Machine

variable {Output : Type u} {State : Type v}
variable (machine : TypedPartialDFAO binaryZeckendorfBase Output State)

/-- States lying over the recurrent base state. -/
abbrev ZeroFiber :=
  {state : State // machine.stateType state = .previousZero}

/-- States lying over the transient base state. -/
abbrev OneFiber :=
  {state : State // machine.stateType state = .previousOne}

/-- Evaluate a typed machine from an explicitly supplied state. -/
def evalFromState (state : State) (word : List (Fin 2)) : Option Output :=
  (machine.runFrom state word).map machine.output

/-- A zero transition from the recurrent fiber, bundled with its forced target
type. -/
def zeroSuccessor (state : ZeroFiber machine) : Option (ZeroFiber machine) :=
  match hstep : machine.step state.1 0 with
  | none => none
  | some next =>
      some ⟨next, by
        have typed := machine.step_type hstep
        simpa [binaryZeckendorfBase, state.2] using typed⟩

/-- A one transition from the recurrent fiber, bundled with its forced target
type. -/
def oneSuccessor (state : ZeroFiber machine) : Option (OneFiber machine) :=
  match hstep : machine.step state.1 1 with
  | none => none
  | some next =>
      some ⟨next, by
        have typed := machine.step_type hstep
        simpa [binaryZeckendorfBase, state.2] using typed⟩

/-- The only legal nonempty transition from the transient fiber returns on
zero to the recurrent fiber. -/
def returnSuccessor (state : OneFiber machine) : Option (ZeroFiber machine) :=
  match hstep : machine.step state.1 0 with
  | none => none
  | some next =>
      some ⟨next, by
        have typed := machine.step_type hstep
        simpa [binaryZeckendorfBase, state.2] using typed⟩

@[simp] theorem zeroSuccessor_map_val (state : ZeroFiber machine) :
    (zeroSuccessor machine state).map Subtype.val =
      machine.step state.1 0 := by
  cases hstep : machine.step state.1 0 with
  | none => simp [zeroSuccessor, hstep]
  | some next => simp [zeroSuccessor, hstep]

@[simp] theorem oneSuccessor_map_val (state : ZeroFiber machine) :
    (oneSuccessor machine state).map Subtype.val =
      machine.step state.1 1 := by
  cases hstep : machine.step state.1 1 with
  | none => simp [oneSuccessor, hstep]
  | some next => simp [oneSuccessor, hstep]

@[simp] theorem returnSuccessor_map_val (state : OneFiber machine) :
    (returnSuccessor machine state).map Subtype.val =
      machine.step state.1 0 := by
  cases hstep : machine.step state.1 0 with
  | none => simp [returnSuccessor, hstep]
  | some next => simp [returnSuccessor, hstep]

/-- Input one is illegal from every state of the transient fiber. -/
theorem oneFiber_step_one_none (state : OneFiber machine) :
    machine.step state.1 1 = none := by
  cases hstep : machine.step state.1 1 with
  | none => rfl
  | some next =>
      have typed := machine.step_type hstep
      simp [binaryZeckendorfBase, state.2] at typed

/-- Complete legal-continuation signature of a transient state. -/
def oneSignature (state : OneFiber machine) :
    Output × Option (ZeroFiber machine) :=
  (machine.output state.1, returnSuccessor machine state)

/-- Signature requested by the one transition of a recurrent state. -/
def zeroOneSignature (state : ZeroFiber machine) :
    Option (Output × Option (ZeroFiber machine)) :=
  (oneSuccessor machine state).map (oneSignature machine)

/-- Equality of transient signatures implies equality on every continuation,
including illegal continuations, because input one is undefined in both
states. -/
theorem same_oneSignature_evalFromState
    (left right : OneFiber machine)
    (equal : oneSignature machine left = oneSignature machine right)
    (word : List (Fin 2)) :
    evalFromState machine left.1 word =
      evalFromState machine right.1 word := by
  have outputEqual : machine.output left.1 = machine.output right.1 :=
    congrArg Prod.fst equal
  have returnEqual :
      returnSuccessor machine left = returnSuccessor machine right :=
    congrArg Prod.snd equal
  cases word with
  | nil =>
      simp [evalFromState, TypedPartialDFAO.runFrom, runTransition,
        outputEqual]
  | cons digit tail =>
      fin_cases digit
      · have stepEqual : machine.step left.1 0 = machine.step right.1 0 := by
          calc
            machine.step left.1 0 =
                (returnSuccessor machine left).map Subtype.val :=
              (returnSuccessor_map_val machine left).symm
            _ = (returnSuccessor machine right).map Subtype.val := by
              rw [returnEqual]
            _ = machine.step right.1 0 :=
              returnSuccessor_map_val machine right
        simp [evalFromState, TypedPartialDFAO.runFrom, runTransition,
          stepEqual]
      · rw [oneFiber_step_one_none machine left,
          oneFiber_step_one_none machine right]
        rfl

/-- A missing requested signature is equivalent to a missing one transition. -/
theorem zeroOneSignature_eq_none_iff (state : ZeroFiber machine) :
    zeroOneSignature machine state = none ↔
      machine.step state.1 1 = none := by
  constructor
  · intro signatureNone
    unfold zeroOneSignature at signatureNone
    cases hsuccessor : oneSuccessor machine state with
    | none =>
        have specification := oneSuccessor_map_val machine state
        simpa [hsuccessor] using specification.symm
    | some successor =>
        simp [hsuccessor] at signatureNone
  · intro stepNone
    simp [zeroOneSignature, oneSuccessor, stepNone]

/-- A requested signature is witnessed by an actual transient successor. -/
theorem zeroOneSignature_eq_some_iff
    (state : ZeroFiber machine)
    (signature : Output × Option (ZeroFiber machine)) :
    zeroOneSignature machine state = some signature ↔
      ∃ successor : OneFiber machine,
        machine.step state.1 1 = some successor.1 ∧
          oneSignature machine successor = signature := by
  constructor
  · intro signatureEqual
    unfold zeroOneSignature at signatureEqual
    cases hsuccessor : oneSuccessor machine state with
    | none =>
        simp [hsuccessor] at signatureEqual
    | some successor =>
        have stepEqual :
            machine.step state.1 1 = some successor.1 := by
          have specification := oneSuccessor_map_val machine state
          simpa [hsuccessor] using specification.symm
        have valueEqual : oneSignature machine successor = signature := by
          simpa [hsuccessor] using signatureEqual
        exact ⟨successor, stepEqual, valueEqual⟩
  · rintro ⟨successor, stepEqual, valueEqual⟩
    simpa [zeroOneSignature, oneSuccessor, stepEqual, valueEqual]

end Machine

/-- A first-return skeleton retains only recurrent states. A one transition is
represented by its transient output and optional zero-return target. -/
structure Skeleton (Output : Type u) (ZeroState : Type v) where
  start : ZeroState
  zeroStep : ZeroState → Option ZeroState
  oneSignature : ZeroState → Option (Output × Option ZeroState)
  zeroOutput : ZeroState → Output

namespace Skeleton

/-- Evaluate a block code from a recurrent state. -/
def evalFrom {Output : Type u} {ZeroState : Type v}
    (skeleton : Skeleton Output ZeroState) :
    ZeroState → List ReturnBlock → TerminalChannel → Option Output
  | state, [], .recurrent => some (skeleton.zeroOutput state)
  | state, [], .transient =>
      (skeleton.oneSignature state).map Prod.fst
  | state, .zero :: blocks, terminal =>
      (skeleton.zeroStep state).bind fun next =>
        evalFrom skeleton next blocks terminal
  | state, .oneZero :: blocks, terminal =>
      (skeleton.oneSignature state).bind fun signature =>
        signature.2.bind fun next =>
          evalFrom skeleton next blocks terminal

/-- Evaluate a packaged block code from the skeleton start state. -/
def eval {Output : Type u} {ZeroState : Type v}
    (skeleton : Skeleton Output ZeroState) (code : BlockCode) :
    Option Output :=
  skeleton.evalFrom skeleton.start code.blocks code.terminal

end Skeleton

section Extract

variable {Output : Type u} {State : Type v}
variable (machine : TypedPartialDFAO binaryZeckendorfBase Output State)

/-- Extract the recurrent first-return skeleton of a typed binary Zeckendorf
machine. -/
def extractSkeleton : Skeleton Output (ZeroFiber machine) where
  start := ⟨machine.start, machine.start_type⟩
  zeroStep := zeroSuccessor machine
  oneSignature := zeroOneSignature machine
  zeroOutput := fun state => machine.output state.1

/-- Skeleton evaluation agrees with the original machine on every expanded
block code, from every recurrent state. -/
theorem eval_extractSkeleton
    (state : ZeroFiber machine)
    (blocks : List ReturnBlock) (terminal : TerminalChannel) :
    (extractSkeleton machine).evalFrom state blocks terminal =
      evalFromState machine state.1 (expand blocks terminal) := by
  induction blocks generalizing state with
  | nil =>
      cases terminal with
      | recurrent =>
          simp [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
            TypedPartialDFAO.runFrom, runTransition]
      | transient =>
          cases hsignature : zeroOneSignature machine state with
          | none =>
              have stepNone :=
                (zeroOneSignature_eq_none_iff machine state).1 hsignature
              simp [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                TypedPartialDFAO.runFrom, runTransition, hsignature,
                stepNone]
          | some signature =>
              obtain ⟨successor, stepEqual, signatureEqual⟩ :=
                (zeroOneSignature_eq_some_iff machine state signature).1
                  hsignature
              have outputEqual :
                  machine.output successor.1 = signature.1 :=
                congrArg Prod.fst signatureEqual
              simp [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                TypedPartialDFAO.runFrom, runTransition, hsignature,
                stepEqual, outputEqual]
  | cons block blocks inductionHypothesis =>
      cases block with
      | zero =>
          cases hnext : zeroSuccessor machine state with
          | none =>
              have stepNone : machine.step state.1 0 = none := by
                have specification := zeroSuccessor_map_val machine state
                simpa [hnext] using specification.symm
              simp [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                TypedPartialDFAO.runFrom, runTransition, hnext, stepNone]
          | some next =>
              have stepEqual : machine.step state.1 0 = some next.1 := by
                have specification := zeroSuccessor_map_val machine state
                simpa [hnext] using specification.symm
              simpa [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                TypedPartialDFAO.runFrom, runTransition, hnext, stepEqual]
                using inductionHypothesis next
      | oneZero =>
          cases hsignature : zeroOneSignature machine state with
          | none =>
              have stepNone :=
                (zeroOneSignature_eq_none_iff machine state).1 hsignature
              simp [Skeleton.evalFrom, extractSkeleton, evalFromState, expand,
                TypedPartialDFAO.runFrom, runTransition, hsignature,
                stepNone]
          | some signature =>
              obtain ⟨successor, firstStep, signatureEqual⟩ :=
                (zeroOneSignature_eq_some_iff machine state signature).1
                  hsignature
              have returnEqual :
                  returnSuccessor machine successor = signature.2 :=
                congrArg Prod.snd signatureEqual
              cases hreturn : signature.2 with
              | none =>
                  have successorNone :
                      returnSuccessor machine successor = none := by
                    simpa [hreturn] using returnEqual
                  have secondStep : machine.step successor.1 0 = none := by
                    have specification :=
                      returnSuccessor_map_val machine successor
                    simpa [successorNone] using specification.symm
                  simp [Skeleton.evalFrom, extractSkeleton, evalFromState,
                    expand, TypedPartialDFAO.runFrom, runTransition,
                    hsignature, firstStep, hreturn, secondStep]
              | some next =>
                  have successorEqual :
                      returnSuccessor machine successor = some next := by
                    simpa [hreturn] using returnEqual
                  have secondStep :
                      machine.step successor.1 0 = some next.1 := by
                    have specification :=
                      returnSuccessor_map_val machine successor
                    simpa [successorEqual] using specification.symm
                  simpa [Skeleton.evalFrom, extractSkeleton, evalFromState,
                    expand, TypedPartialDFAO.runFrom, runTransition,
                    hsignature, firstStep, hreturn, secondStep]
                    using inductionHypothesis next

/-- Start-state form of skeleton extraction. -/
theorem eval_extractSkeleton_start (code : BlockCode) :
    (extractSkeleton machine).eval code =
      machine.evalOutput (expandCode code) := by
  have agreement := eval_extractSkeleton machine
    (state := (extractSkeleton machine).start)
    code.blocks code.terminal
  simpa [Skeleton.eval, extractSkeleton, evalFromState, expandCode,
    TypedPartialDFAO.evalOutput, TypedPartialDFAO.run] using agreement

end Extract

section Canonical

variable {Output : Type u} {ZeroState : Type v}
variable (skeleton : Skeleton Output ZeroState)

/-- Distinct transient signatures used by a skeleton. -/
def SignatureFiber :=
  {signature : Output × Option ZeroState //
    ∃ state : ZeroState,
      skeleton.oneSignature state = some signature}

/-- Canonical state type: recurrent states plus one transient state for each
used signature. -/
abbrev CanonicalState := Sum ZeroState (SignatureFiber skeleton)

/-- Base-state type of a canonical state. -/
def canonicalStateType : CanonicalState skeleton → BinaryZeckendorfState
  | .inl _ => .previousZero
  | .inr _ => .previousOne

/-- Canonical transition table reconstructed from a skeleton. -/
def canonicalStep :
    CanonicalState skeleton → Fin 2 → Option (CanonicalState skeleton)
  | .inl state, digit =>
      if digit = 0 then
        (skeleton.zeroStep state).map Sum.inl
      else
        match hsignature : skeleton.oneSignature state with
        | none => none
        | some signature =>
            some (.inr ⟨signature, ⟨state, hsignature⟩⟩)
  | .inr signature, digit =>
      if digit = 0 then
        signature.1.2.map Sum.inl
      else
        none

/-- Canonical output table. -/
def canonicalOutput : CanonicalState skeleton → Output
  | .inl state => skeleton.zeroOutput state
  | .inr signature => signature.1.1

/-- Canonical transitions respect the binary Zeckendorf base machine. -/
theorem canonicalStep_type
    {state next : CanonicalState skeleton} {digit : Fin 2}
    (defined : canonicalStep skeleton state digit = some next) :
    binaryZeckendorfBase.step (canonicalStateType skeleton state) digit =
      some (canonicalStateType skeleton next) := by
  rcases state with state | signature
  · fin_cases digit
    · cases hstep : skeleton.zeroStep state <;>
        simp [canonicalStep, canonicalStateType, binaryZeckendorfBase,
          hstep] at defined ⊢
    · cases hsignature : skeleton.oneSignature state <;>
        simp [canonicalStep, canonicalStateType, binaryZeckendorfBase,
          hsignature] at defined ⊢
  · fin_cases digit
    · cases hreturn : signature.1.2 <;>
        simp [canonicalStep, canonicalStateType, binaryZeckendorfBase,
          hreturn] at defined ⊢
    · simp [canonicalStep] at defined

/-- Canonical typed partial DFAO reconstructed from a skeleton. -/
def canonicalMachine :
    TypedPartialDFAO binaryZeckendorfBase Output (CanonicalState skeleton) where
  start := .inl skeleton.start
  stateType := canonicalStateType skeleton
  step := canonicalStep skeleton
  output := canonicalOutput skeleton
  start_type := rfl
  step_type := canonicalStep_type skeleton

/-- Canonical-machine evaluation agrees with skeleton evaluation from every
recurrent state. -/
theorem eval_canonicalMachine_expand
    (state : ZeroState) (blocks : List ReturnBlock)
    (terminal : TerminalChannel) :
    evalFromState (canonicalMachine skeleton) (.inl state)
        (expand blocks terminal) =
      skeleton.evalFrom state blocks terminal := by
  induction blocks generalizing state with
  | nil =>
      cases terminal with
      | recurrent =>
          simp [evalFromState, Skeleton.evalFrom, expand, canonicalMachine,
            canonicalStep, canonicalOutput, TypedPartialDFAO.runFrom,
            runTransition]
      | transient =>
          cases hsignature : skeleton.oneSignature state <;>
            simp [evalFromState, Skeleton.evalFrom, expand, canonicalMachine,
              canonicalStep, canonicalOutput, TypedPartialDFAO.runFrom,
              runTransition, hsignature]
  | cons block blocks inductionHypothesis =>
      cases block with
      | zero =>
          cases hnext : skeleton.zeroStep state with
          | none =>
              simp [evalFromState, Skeleton.evalFrom, expand,
                canonicalMachine, canonicalStep, canonicalOutput,
                TypedPartialDFAO.runFrom, runTransition, hnext]
          | some next =>
              simpa [evalFromState, Skeleton.evalFrom, expand,
                canonicalMachine, canonicalStep, canonicalOutput,
                TypedPartialDFAO.runFrom, runTransition, hnext]
                using inductionHypothesis next
      | oneZero =>
          cases hsignature : skeleton.oneSignature state with
          | none =>
              simp [evalFromState, Skeleton.evalFrom, expand,
                canonicalMachine, canonicalStep, canonicalOutput,
                TypedPartialDFAO.runFrom, runTransition, hsignature]
          | some signature =>
              cases hreturn : signature.2 with
              | none =>
                  simp [evalFromState, Skeleton.evalFrom, expand,
                    canonicalMachine, canonicalStep, canonicalOutput,
                    TypedPartialDFAO.runFrom, runTransition, hsignature,
                    hreturn]
              | some next =>
                  simpa [evalFromState, Skeleton.evalFrom, expand,
                    canonicalMachine, canonicalStep, canonicalOutput,
                    TypedPartialDFAO.runFrom, runTransition, hsignature,
                    hreturn] using inductionHypothesis next

/-- Start-state form of canonical reconstruction. -/
theorem eval_canonicalMachine (code : BlockCode) :
    (canonicalMachine skeleton).evalOutput (expandCode code) =
      skeleton.eval code := by
  have agreement := eval_canonicalMachine_expand skeleton skeleton.start
    code.blocks code.terminal
  simpa [Skeleton.eval, expandCode, evalFromState,
    TypedPartialDFAO.evalOutput, TypedPartialDFAO.run, canonicalMachine]
    using agreement

/-- Reconstruction preserves a zero self-loop of the skeleton start state. -/
theorem canonicalMachine_start_zero_loop
    (zeroLoop : skeleton.zeroStep skeleton.start = some skeleton.start) :
    (canonicalMachine skeleton).step (canonicalMachine skeleton).start 0 =
      some (canonicalMachine skeleton).start := by
  simp [canonicalMachine, canonicalStep, zeroLoop]

/-- Reconstruction preserves the skeleton start output. -/
@[simp] theorem canonicalMachine_start_output :
    (canonicalMachine skeleton).output (canonicalMachine skeleton).start =
      skeleton.zeroOutput skeleton.start := by
  rfl

noncomputable instance signatureFiberFintype
    [Fintype Output] [Fintype ZeroState] :
    Fintype (SignatureFiber skeleton) :=
  Fintype.ofFinite _

/-- The canonical machine has one state per recurrent state and one state per
distinct used transient signature. -/
theorem canonical_state_card_eq
    [Fintype Output] [Fintype ZeroState] :
    Fintype.card (CanonicalState skeleton) =
      Fintype.card ZeroState + Fintype.card (SignatureFiber skeleton) := by
  simp [CanonicalState]

/-- Embed an abstract signature into the actual transient signature carried by
the canonical machine. -/
def canonicalSignatureEmbedding
    (signature : Output × Option ZeroState) :
    Output × Option (ZeroFiber (canonicalMachine skeleton)) :=
  (signature.1,
    signature.2.map fun state =>
      ⟨Sum.inl state, rfl⟩)

/-- The canonical signature embedding is injective. -/
theorem canonicalSignatureEmbedding_injective :
    Function.Injective (canonicalSignatureEmbedding skeleton) := by
  rintro ⟨leftOutput, leftReturn⟩ ⟨rightOutput, rightReturn⟩ equal
  cases leftReturn <;> cases rightReturn <;>
    simp [canonicalSignatureEmbedding] at equal ⊢

/-- Canonical transient state corresponding to a used signature. -/
def canonicalOneState (signature : SignatureFiber skeleton) :
    OneFiber (canonicalMachine skeleton) :=
  ⟨Sum.inr signature, rfl⟩

/-- A canonical transient state carries exactly its defining embedded
signature. -/
theorem oneSignature_canonicalOneState
    (signature : SignatureFiber skeleton) :
    oneSignature (canonicalMachine skeleton)
        (canonicalOneState skeleton signature) =
      canonicalSignatureEmbedding skeleton signature.1 := by
  rcases signature with ⟨⟨output, returnState⟩, witness⟩
  cases returnState <;>
    simp [canonicalOneState, oneSignature, returnSuccessor,
      canonicalMachine, canonicalStep, canonicalOutput,
      canonicalSignatureEmbedding]

/-- Distinct canonical transient states have distinct complete legal
continuation signatures. -/
theorem canonical_transient_signatures_injective :
    Function.Injective fun signature : SignatureFiber skeleton =>
      oneSignature (canonicalMachine skeleton)
        (canonicalOneState skeleton signature) := by
  intro left right equal
  rw [oneSignature_canonicalOneState,
    oneSignature_canonicalOneState] at equal
  apply Subtype.ext
  exact canonicalSignatureEmbedding_injective skeleton equal

end Canonical

section Compression

variable {Output : Type u} {State : Type v}
variable (machine : TypedPartialDFAO binaryZeckendorfBase Output State)

/-- Every used extracted signature has a witnessing original transient state. -/
theorem signatureFiber_has_representative
    (signature : SignatureFiber (extractSkeleton machine)) :
    ∃ state : OneFiber machine,
      oneSignature machine state = signature.1 := by
  rcases signature.2 with ⟨zeroState, requested⟩
  have requested' :
      zeroOneSignature machine zeroState = some signature.1 := by
    simpa [extractSkeleton] using requested
  obtain ⟨oneState, _, signatureEqual⟩ :=
    (zeroOneSignature_eq_some_iff machine zeroState signature.1).1
      requested'
  exact ⟨oneState, signatureEqual⟩

/-- Choose one original transient representative for each used signature. -/
noncomputable def signatureRepresentative
    (signature : SignatureFiber (extractSkeleton machine)) :
    OneFiber machine :=
  Classical.choose (signatureFiber_has_representative machine signature)

/-- The chosen representative realizes its indexed signature. -/
theorem signatureRepresentative_spec
    (signature : SignatureFiber (extractSkeleton machine)) :
    oneSignature machine (signatureRepresentative machine signature) =
      signature.1 :=
  Classical.choose_spec (signatureFiber_has_representative machine signature)

/-- Chosen representatives of distinct signatures are distinct. -/
theorem signatureRepresentative_injective :
    Function.Injective (signatureRepresentative machine) := by
  intro left right equal
  apply Subtype.ext
  calc
    left.1 = oneSignature machine (signatureRepresentative machine left) :=
      (signatureRepresentative_spec machine left).symm
    _ = oneSignature machine (signatureRepresentative machine right) := by
      rw [equal]
    _ = right.1 := signatureRepresentative_spec machine right

/-- Map canonical states back into distinct states of the original machine. -/
noncomputable def canonicalToOriginal :
    CanonicalState (extractSkeleton machine) → State
  | .inl state => state.1
  | .inr signature => (signatureRepresentative machine signature).1

/-- The canonical-to-original state map is injective. -/
theorem canonicalToOriginal_injective :
    Function.Injective (canonicalToOriginal machine) := by
  intro left right equal
  rcases left with leftZero | leftSignature
  · rcases right with rightZero | rightSignature
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact equal
    · have typeEqual := congrArg machine.stateType equal
      rw [leftZero.2,
        (signatureRepresentative machine rightSignature).2] at typeEqual
      cases typeEqual
  · rcases right with rightZero | rightSignature
    · have typeEqual := congrArg machine.stateType equal
      rw [(signatureRepresentative machine leftSignature).2,
        rightZero.2] at typeEqual
      cases typeEqual
    · have representativeEqual :
          signatureRepresentative machine leftSignature =
            signatureRepresentative machine rightSignature :=
        Subtype.ext equal
      have signatureEqual :=
        signatureRepresentative_injective machine representativeEqual
      rw [signatureEqual]

/-- Canonicalization never increases the number of states. -/
theorem canonical_state_card_le
    [Fintype Output] [Fintype State] :
    Fintype.card (CanonicalState (extractSkeleton machine)) ≤
      Fintype.card State := by
  exact Fintype.card_le_of_injective
    (canonicalToOriginal machine)
    (canonicalToOriginal_injective machine)

/-- The canonical machine extracted from an original machine agrees with it on
all legal block codes and uses no more states. -/
theorem canonical_extract_behavior_and_cardinality
    [Fintype Output] [Fintype State] :
    (∀ code : BlockCode,
      (canonicalMachine (extractSkeleton machine)).evalOutput
          (expandCode code) =
        machine.evalOutput (expandCode code)) ∧
      Fintype.card (CanonicalState (extractSkeleton machine)) ≤
        Fintype.card State := by
  constructor
  · intro code
    calc
      (canonicalMachine (extractSkeleton machine)).evalOutput
          (expandCode code) =
          (extractSkeleton machine).eval code :=
        eval_canonicalMachine (extractSkeleton machine) code
      _ = machine.evalOutput (expandCode code) :=
        eval_extractSkeleton_start machine code
  · exact canonical_state_card_le machine

/-- An original start-state zero loop is retained by the extracted canonical
machine. -/
theorem canonical_extract_start_zero_loop
    (zeroLoop : machine.step machine.start 0 = some machine.start) :
    (canonicalMachine (extractSkeleton machine)).step
        (canonicalMachine (extractSkeleton machine)).start 0 =
      some (canonicalMachine (extractSkeleton machine)).start := by
  apply canonicalMachine_start_zero_loop
  simp [extractSkeleton, zeroSuccessor, zeroLoop]

/-- The extracted canonical machine retains the original start output. -/
@[simp] theorem canonical_extract_start_output :
    (canonicalMachine (extractSkeleton machine)).output
        (canonicalMachine (extractSkeleton machine)).start =
      machine.output machine.start := by
  rfl

#print axioms decode_expand
#print axioms same_oneSignature_evalFromState
#print axioms eval_extractSkeleton_start
#print axioms eval_canonicalMachine
#print axioms canonical_transient_signatures_injective
#print axioms canonical_extract_behavior_and_cardinality

end Compression

end D5.S0.Automata.BinaryZeckendorfBlockSkeleton
