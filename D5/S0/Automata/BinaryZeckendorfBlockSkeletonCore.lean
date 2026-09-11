/- GID: D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore
   generality: G
   mirror-B: D5/B/S0/Automata/BinaryZeckendorfBlockSkeletonCore
   mirror-E: none(waiver:first-return-skeleton)
   anchors: []
   utility: none
   digest: Binary Zeckendorf return blocks 0 and 10 with an optional terminal 1 admit injective expansion and legal-word compression; typed-DFAO transient states with equal output-and-zero-successor signatures agree on every continuation. -/

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
  deriving DecidableEq, Repr

instance : Fintype ReturnBlock where
  elems := {ReturnBlock.zero, ReturnBlock.oneZero}
  complete := by intro block; cases block <;> simp

/-- A legal word either returns to the recurrent base state or ends with one
final `1` in the transient base state. -/
inductive TerminalChannel
  | recurrent
  | transient
  deriving DecidableEq, Repr

instance : Fintype TerminalChannel where
  elems := {TerminalChannel.recurrent, TerminalChannel.transient}
  complete := by intro terminal; cases terminal <;> simp

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
      change decode (expand blocks terminal) = some ⟨blocks, terminal⟩ at inductionHypothesis
      have mapped := congrArg
        (Option.map fun code => { code with blocks := block :: code.blocks })
        inductionHypothesis
      cases block with
      | zero =>
          cases hrest : expand blocks terminal <;>
            simpa [expandCode, expand, hrest, decode] using mapped
      | oneZero =>
          simpa [expandCode, expand, decode] using mapped

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
  simpa [PartialDFA.eval, expandCode, binaryZeckendorfBase] using
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
        simpa [binaryZeckendorfBase, state.2] using typed.symm⟩

/-- A one transition from the recurrent fiber, bundled with its forced target
type. -/
def oneSuccessor (state : ZeroFiber machine) : Option (OneFiber machine) :=
  match hstep : machine.step state.1 1 with
  | none => none
  | some next =>
      some ⟨next, by
        have typed := machine.step_type hstep
        simpa [binaryZeckendorfBase, state.2] using typed.symm⟩

/-- The only legal nonempty transition from the transient fiber returns on
zero to the recurrent fiber. -/
def returnSuccessor (state : OneFiber machine) : Option (ZeroFiber machine) :=
  match hstep : machine.step state.1 0 with
  | none => none
  | some next =>
      some ⟨next, by
        have typed := machine.step_type hstep
        simpa [binaryZeckendorfBase, state.2] using typed.symm⟩

@[simp] theorem zeroSuccessor_map_val (state : ZeroFiber machine) :
    (zeroSuccessor machine state).map Subtype.val =
      machine.step state.1 0 := by
  unfold zeroSuccessor
  split <;> simp_all

@[simp] theorem oneSuccessor_map_val (state : ZeroFiber machine) :
    (oneSuccessor machine state).map Subtype.val =
      machine.step state.1 1 := by
  unfold oneSuccessor
  split <;> simp_all

@[simp] theorem returnSuccessor_map_val (state : OneFiber machine) :
    (returnSuccessor machine state).map Subtype.val =
      machine.step state.1 0 := by
  unfold returnSuccessor
  split <;> simp_all

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
      · simp [evalFromState, TypedPartialDFAO.runFrom, runTransition,
          oneFiber_step_one_none machine left, oneFiber_step_one_none machine right]

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
    unfold zeroOneSignature oneSuccessor
    split <;> simp_all

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
    unfold zeroOneSignature oneSuccessor
    split <;> simp_all

end Machine

end D5.S0.Automata.BinaryZeckendorfBlockSkeleton
