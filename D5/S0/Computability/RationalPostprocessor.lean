/- GID: D5/S0/Computability/RationalPostprocessor
   generality: G
   mirror-B: D5/B/S0/Computability/RationalPostprocessor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: ["mathlib/module/Mathlib.Computability.TuringMachine.Computable"]
   utility: none
   digest: A fixed finite stack program reading ordinary dyadic rational responses. -/

/-
These are universal symbolic program and word laws over unbounded words and
exponents. They construct actual finite-machine executions and exact arithmetic
output, including erasure and restoration. No finite certificate or bounded
enumeration is delivered, no certified instance is retained, and no conditional
numerical estimate is used in place of a physical premise. The syntax and
divisibility tests specify the program's general response semantics; arithmetic
suitability does not certify a physical oracle answer or a SAT count.
-/

import D5.S0.Computability.PhysicalDivider.WordArithmetic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic

open Turing StateTransition
open Lax51Proofs.RamToTM

inductive ResponseSymbol
  | zero | one | slash
  deriving DecidableEq, Fintype, Inhabited

def symbolEq : ResponseSymbol -> ResponseSymbol -> Bool
  | .zero, .zero | .one, .one | .slash, .slash => true
  | _, _ => false

def isSymbol (tag : ResponseSymbol) : Option ResponseSymbol -> Bool
  | none => false
  | some value => symbolEq value tag

def bitSymbol : Bool -> ResponseSymbol
  | false => .zero
  | true => .one

def binaryWord (xs : List Bool) : List ResponseSymbol := xs.map bitSymbol

inductive PostStack
  | input | quotient | shifts | output
  deriving DecidableEq, Fintype, Inhabited

inductive PostLabel
  | first | numerator | denominatorFirst | denominatorTail | denominatorZeros
  | shift | reverse | normalize | badInput | badQuotient | badShifts
  deriving DecidableEq, Fintype, Inhabited

structure PostControl where
  remainder : Fin 3 := 0
  held : Option ResponseSymbol := none
  last : Bool := false
  deriving DecidableEq, Fintype, Inhabited

def readSymbol (s : PostControl) (a : Option ResponseSymbol) : PostControl :=
  { s with held := a }

def clearSymbol (s : PostControl) : PostControl := { s with held := none }

def quotientBit (r : Fin 3) (b : Bool) : Bool :=
  decide (3 <= 2 * r.val + b.toNat)

def nextRemainder (r : Fin 3) (b : Bool) : Fin 3 :=
  if h : 3 <= 2 * r.val + b.toNat then
    ⟨2 * r.val + b.toNat - 3, by have := r.isLt; cases b <;> simp_all <;> omega⟩
  else
    ⟨2 * r.val + b.toNat, by omega⟩

def advance (s : PostControl) (b : Bool) : PostControl :=
  ⟨nextRemainder s.remainder b, none, b⟩

def postMachine : FinTM2 where
  K := PostStack
  k₀ := .input
  k₁ := .output
  Γ _ := ResponseSymbol
  Λ := PostLabel
  main := .first
  σ := PostControl
  initialState := default
  m
    | .first =>
      .pop .input readSymbol <|
        .branch (fun s => isSymbol .one s.held)
          (.push .quotient (fun _ => .zero) <|
            .load (fun _ => ⟨1, none, true⟩) <| .goto fun _ => .numerator)
          (.goto fun _ => .badInput)
    | .numerator =>
      .pop .input readSymbol <|
        .branch (fun s => isSymbol .slash s.held)
          (.branch (fun s => decide (s.remainder.val = 0))
            (.load clearSymbol <| .goto fun _ => .denominatorFirst)
            (.goto fun _ => .badInput))
          (.branch (fun s => s.held.isNone)
            (.goto fun _ => .badInput)
            (.push .quotient (fun s =>
              bitSymbol (quotientBit s.remainder (isSymbol .one s.held))) <|
              .load (fun s => advance s (isSymbol .one s.held)) <|
                .goto fun _ => .numerator))
    | .denominatorFirst =>
      .pop .input readSymbol <|
        .branch (fun s => isSymbol .one s.held)
          (.load clearSymbol <| .goto fun _ => .denominatorTail)
          (.goto fun _ => .badInput)
    | .denominatorTail =>
      .pop .input readSymbol <|
        .branch (fun s => s.held.isNone)
          (.push .quotient (fun _ => .zero) <|
            .load clearSymbol <| .goto fun _ => .reverse)
          (.branch (fun s => isSymbol .zero s.held && s.last)
            (.load clearSymbol <| .goto fun _ => .denominatorZeros)
            (.goto fun _ => .badInput))
    | .denominatorZeros =>
      .pop .input readSymbol <|
        .branch (fun s => s.held.isNone)
          (.load clearSymbol <| .goto fun _ => .shift)
          (.branch (fun s => isSymbol .zero s.held)
            (.push .shifts (fun _ => .zero) <|
              .load clearSymbol <| .goto fun _ => .denominatorZeros)
            (.goto fun _ => .badInput))
    | .shift =>
      .pop .shifts readSymbol <|
        .branch (fun s => s.held.isNone)
          (.load clearSymbol <| .goto fun _ => .reverse)
          (.pop .quotient (fun s _ => clearSymbol s) <| .goto fun _ => .shift)
    | .reverse =>
      .pop .quotient readSymbol <|
        .branch (fun s => s.held.isNone)
          (.load clearSymbol <| .goto fun _ => .normalize)
          (.push .output (fun s => s.held.getD .zero) <|
            .load clearSymbol <| .goto fun _ => .reverse)
    | .normalize =>
      .peek .output readSymbol <|
        .branch (fun s => s.held.isNone)
          (.push .output (fun _ => .zero) <| .load (fun _ => default) .halt)
          (.branch (fun s => isSymbol .zero s.held)
            (.pop .output (fun s _ => clearSymbol s) <| .goto fun _ => .normalize)
            (.load (fun _ => default) .halt))
    | .badInput =>
      .pop .input readSymbol <|
        .branch (fun s => s.held.isNone)
          (.load clearSymbol <| .goto fun _ => .badQuotient)
          (.load clearSymbol <| .goto fun _ => .badInput)
    | .badQuotient =>
      .pop .quotient readSymbol <|
        .branch (fun s => s.held.isNone)
          (.load clearSymbol <| .goto fun _ => .badShifts)
          (.load clearSymbol <| .goto fun _ => .badQuotient)
    | .badShifts =>
      .pop .shifts readSymbol <|
        .branch (fun s => s.held.isNone)
          (.push .output (fun _ => .zero) <| .load (fun _ => default) .halt)
          (.load clearSymbol <| .goto fun _ => .badShifts)

def postStacks (input quotient shifts output : List ResponseSymbol) :
    PostStack -> List ResponseSymbol
  | .input => input
  | .quotient => quotient
  | .shifts => shifts
  | .output => output

def postCfg (label : PostLabel) (state : PostControl)
    (input quotient shifts output : List ResponseSymbol) : postMachine.Cfg :=
  ⟨some label, state, postStacks input quotient shifts output⟩

def canonicalBinary : List Bool -> List Bool
  | [] => [false]
  | false :: xs => canonicalBinary xs
  | true :: xs => true :: xs

def scan (state : PostControl) (quotient : List Bool) :
    List Bool -> Prod PostControl (List Bool)
  | [] => (state, quotient)
  | b :: bs => scan (advance state b) (quotientBit state.remainder b :: quotient) bs


private def normalizeRun (state : PostControl) (xs : List Bool) :
    EvalsToInTime postMachine.step
      (postCfg .normalize state [] [] [] (binaryWord xs))
      (some (haltList postMachine (binaryWord (canonicalBinary xs)))) (xs.length + 1) := by
  induction xs generalizing state with
  | nil =>
    have hs : postMachine.step (postCfg .normalize state [] [] [] []) =
        some (haltList postMachine (binaryWord [false])) := by
      apply congrArg some
      simp only [binaryWord, List.map_cons, List.map_nil, bitSymbol]
      dsimp [postMachine, TM2.stepAux, postCfg, postStacks, binaryWord, bitSymbol,
          isSymbol, symbolEq, readSymbol, clearSymbol, haltList]
      congr 1
      funext k
      cases k <;> rfl
    exact { steps := 1, evals_in_steps := hs, steps_le_m := by simp }
  | cons b xs ih =>
    cases b with
    | true =>
      have hs : postMachine.step
          (postCfg .normalize state [] [] [] (binaryWord (true :: xs))) =
          some (haltList postMachine (binaryWord (true :: xs))) := by
        apply congrArg some
        simp only [binaryWord, List.map_cons, List.map_nil, bitSymbol]
        dsimp [postMachine, TM2.stepAux, postCfg, postStacks, binaryWord, bitSymbol,
          isSymbol, symbolEq, readSymbol, clearSymbol, haltList]
        congr 1
        funext k
        cases k <;> rfl
      exact { steps := 1, evals_in_steps := hs, steps_le_m := by simp }
    | false =>
      have hs : postMachine.step
          (postCfg .normalize state [] [] [] (binaryWord (false :: xs))) =
          some (postCfg .normalize (clearSymbol state) [] [] [] (binaryWord xs)) := by
        apply congrArg some
        simp only [binaryWord, List.map_cons, List.map_nil, bitSymbol]
        dsimp [postMachine, TM2.stepAux, postCfg, postStacks, binaryWord, bitSymbol,
          isSymbol, symbolEq, readSymbol, clearSymbol, haltList]
        congr 1
        funext k
        cases k <;> rfl
      let one : EvalsToInTime postMachine.step
          (postCfg .normalize state [] [] [] (binaryWord (false :: xs)))
          (some (postCfg .normalize (clearSymbol state) [] [] [] (binaryWord xs))) 1 :=
        { steps := 1, evals_in_steps := hs, steps_le_m := by decide }
      have h := EvalsToInTime.trans postMachine.step 1 (xs.length + 1) _ _ _
        one (ih (clearSymbol state))
      exact h

private def reverseRun (state : PostControl) (xs out : List Bool) :
    EvalsToInTime postMachine.step
      (postCfg .reverse state [] (binaryWord xs) [] (binaryWord out))
      (some (haltList postMachine (binaryWord (canonicalBinary (xs.reverse ++ out)))))
      (2 * xs.length + out.length + 2) := by
  induction xs generalizing state out with
  | nil =>
    have hs : postMachine.step (postCfg .reverse state [] [] [] (binaryWord out)) =
        some (postCfg .normalize (clearSymbol state) [] [] [] (binaryWord out)) := by
      apply congrArg some
      simp only [binaryWord, List.map_cons, List.map_nil, bitSymbol]
      dsimp [postMachine, TM2.stepAux, postCfg, postStacks, binaryWord, bitSymbol,
          isSymbol, symbolEq, readSymbol, clearSymbol, haltList]
      congr 1
      funext k
      cases k <;> rfl
    let one : EvalsToInTime postMachine.step
        (postCfg .reverse state [] [] [] (binaryWord out))
        (some (postCfg .normalize (clearSymbol state) [] [] [] (binaryWord out))) 1 :=
      { steps := 1, evals_in_steps := hs, steps_le_m := by decide }
    have h := EvalsToInTime.trans postMachine.step 1 (out.length + 1) _ _ _
      one (normalizeRun (clearSymbol state) out)
    simpa [binaryWord, Nat.add_assoc] using h
  | cons b xs ih =>
    have hs : postMachine.step
        (postCfg .reverse state [] (binaryWord (b :: xs)) [] (binaryWord out)) =
        some (postCfg .reverse (clearSymbol state) [] (binaryWord xs) []
          (binaryWord (b :: out))) := by
      cases b <;>
        apply congrArg some <;>
        simp only [binaryWord, List.map_cons, List.map_nil, bitSymbol] <;>
        dsimp [postMachine, TM2.stepAux, postCfg, postStacks, binaryWord, bitSymbol,
          isSymbol, symbolEq, readSymbol, clearSymbol, haltList] <;>
        congr 1 <;>
        funext k <;>
        cases k <;> rfl
    let one : EvalsToInTime postMachine.step
        (postCfg .reverse state [] (binaryWord (b :: xs)) [] (binaryWord out))
        (some (postCfg .reverse (clearSymbol state) [] (binaryWord xs) []
          (binaryWord (b :: out)))) 1 :=
      { steps := 1, evals_in_steps := hs, steps_le_m := by decide }
    have h := EvalsToInTime.trans postMachine.step 1
      (2 * xs.length + (b :: out).length + 2) _ _ _
      one (ih (clearSymbol state) (b :: out))
    have h' : EvalsToInTime postMachine.step
        (postCfg .reverse state [] (binaryWord (b :: xs)) [] (binaryWord out))
        (some (haltList postMachine
          (binaryWord (canonicalBinary (xs.reverse ++ b :: out)))))
        (2 * (b :: xs).length + out.length + 2) :=
      by
        refine { h with steps_le_m := ?_ }
        have hh := h.steps_le_m
        simp only [List.length_cons] at hh ⊢
        omega
    simpa [List.reverse_cons, List.append_assoc] using h'
private def shiftRun (state : PostControl) (xs : List Bool) (k : Nat) :
    EvalsToInTime postMachine.step
      (postCfg .shift state [] (binaryWord xs) (List.replicate k .zero) [])
      (some (haltList postMachine
        (binaryWord (canonicalBinary (xs.drop k).reverse))))
      (2 * xs.length + k + 3) := by
  induction k generalizing state xs with
  | zero =>
    have hs : postMachine.step (postCfg .shift state [] (binaryWord xs) [] []) =
        some (postCfg .reverse (clearSymbol state) [] (binaryWord xs) [] []) := by
      apply congrArg some
      dsimp [postMachine, TM2.stepAux, postCfg, postStacks, isSymbol, symbolEq,
        readSymbol, clearSymbol]
      congr 1
      funext j
      cases j <;> rfl
    let one : EvalsToInTime postMachine.step
        (postCfg .shift state [] (binaryWord xs) [] [])
        (some (postCfg .reverse (clearSymbol state) [] (binaryWord xs) [] [])) 1 :=
      { steps := 1, evals_in_steps := hs, steps_le_m := by decide }
    have h := EvalsToInTime.trans postMachine.step 1 (2 * xs.length + 2) _ _ _
      one (reverseRun (clearSymbol state) xs [])
    simpa using h
  | succ k ih =>
    have hs : postMachine.step
        (postCfg .shift state [] (binaryWord xs) (List.replicate (k + 1) .zero) []) =
        some (postCfg .shift (clearSymbol state) [] (binaryWord xs.tail)
          (List.replicate k .zero) []) := by
      cases xs with
      | nil =>
        apply congrArg some
        simp only [binaryWord, List.map_nil, List.replicate_succ]
        dsimp [postMachine, TM2.stepAux, postCfg, postStacks, isSymbol, symbolEq,
          readSymbol, clearSymbol]
        congr 1
        funext j
        cases j <;> rfl
      | cons b bs =>
        cases b <;>
          apply congrArg some <;>
          simp only [binaryWord, List.map_cons, List.replicate_succ] <;>
          dsimp [postMachine, TM2.stepAux, postCfg, postStacks, bitSymbol,
            isSymbol, symbolEq, readSymbol, clearSymbol] <;>
          congr 1 <;>
          funext j <;>
          cases j <;> rfl
    let one : EvalsToInTime postMachine.step
        (postCfg .shift state [] (binaryWord xs) (List.replicate (k + 1) .zero) [])
        (some (postCfg .shift (clearSymbol state) [] (binaryWord xs.tail)
          (List.replicate k .zero) [])) 1 :=
      { steps := 1, evals_in_steps := hs, steps_le_m := by decide }
    have h := EvalsToInTime.trans postMachine.step 1
      (2 * xs.tail.length + k + 3) _ _ _ one (ih (clearSymbol state) xs.tail)
    have ht : xs.tail.length <= xs.length := by cases xs <;> simp
    have h' : EvalsToInTime postMachine.step
        (postCfg .shift state [] (binaryWord xs) (List.replicate (k + 1) .zero) [])
        (some (haltList postMachine
          (binaryWord (canonicalBinary (xs.tail.drop k).reverse))))
        (2 * xs.length + (k + 1) + 3) :=
      { h with steps_le_m := by have hh := h.steps_le_m; omega }
    cases xs <;> simpa [List.drop] using h'

def denominatorZerosRun (state : PostControl) (xs : List Bool) (k t : Nat) :
    EvalsToInTime postMachine.step
      (postCfg .denominatorZeros state (List.replicate k .zero) (binaryWord xs)
        (List.replicate t .zero) [])
      (some (haltList postMachine
        (binaryWord (canonicalBinary (xs.drop (t + k)).reverse))))
      (2 * xs.length + t + 2 * k + 4) := by
  induction k generalizing state t with
  | zero =>
    have hs : postMachine.step
        (postCfg .denominatorZeros state [] (binaryWord xs) (List.replicate t .zero) []) =
        some (postCfg .shift (clearSymbol state) [] (binaryWord xs)
          (List.replicate t .zero) []) := by
      apply congrArg some
      dsimp [postMachine, TM2.stepAux, postCfg, postStacks, isSymbol, symbolEq,
        readSymbol, clearSymbol]
      congr 1
      funext j
      cases j <;> rfl
    let one : EvalsToInTime postMachine.step
        (postCfg .denominatorZeros state [] (binaryWord xs) (List.replicate t .zero) [])
        (some (postCfg .shift (clearSymbol state) [] (binaryWord xs)
          (List.replicate t .zero) [])) 1 :=
      { steps := 1, evals_in_steps := hs, steps_le_m := by decide }
    have h := EvalsToInTime.trans postMachine.step 1 (2 * xs.length + t + 3) _ _ _
      one (shiftRun (clearSymbol state) xs t)
    simpa [Nat.add_assoc] using h
  | succ k ih =>
    have hs : postMachine.step
        (postCfg .denominatorZeros state (List.replicate (k + 1) .zero)
          (binaryWord xs) (List.replicate t .zero) []) =
        some (postCfg .denominatorZeros (clearSymbol state) (List.replicate k .zero)
          (binaryWord xs) (List.replicate (t + 1) .zero) []) := by
      apply congrArg some
      simp only [List.replicate_succ]
      dsimp [postMachine, TM2.stepAux, postCfg, postStacks, isSymbol, symbolEq,
        readSymbol, clearSymbol]
      congr 1
      funext j
      cases j <;> rfl
    let one : EvalsToInTime postMachine.step
        (postCfg .denominatorZeros state (List.replicate (k + 1) .zero)
          (binaryWord xs) (List.replicate t .zero) [])
        (some (postCfg .denominatorZeros (clearSymbol state) (List.replicate k .zero)
          (binaryWord xs) (List.replicate (t + 1) .zero) [])) 1 :=
      { steps := 1, evals_in_steps := hs, steps_le_m := by decide }
    have h := EvalsToInTime.trans postMachine.step 1
      (2 * xs.length + (t + 1) + 2 * k + 4) _ _ _ one
      (ih (clearSymbol state) (t + 1))
    have h' : EvalsToInTime postMachine.step
        (postCfg .denominatorZeros state (List.replicate (k + 1) .zero)
          (binaryWord xs) (List.replicate t .zero) [])
        (some (haltList postMachine
          (binaryWord (canonicalBinary (xs.drop ((t + 1) + k)).reverse))))
        (2 * xs.length + t + 2 * (k + 1) + 4) :=
      { h with steps_le_m := by have hh := h.steps_le_m; omega }
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

private def numeratorRun (state : PostControl) (xs quotient : List Bool)
    (denominator : List ResponseSymbol) :
    EvalsToInTime postMachine.step
      (postCfg .numerator state (binaryWord xs ++ .slash :: denominator)
        (binaryWord quotient) [] [])
      (some (postCfg .numerator (scan state quotient xs).1 (.slash :: denominator)
        (binaryWord (scan state quotient xs).2) [] [])) xs.length := by
  induction xs generalizing state quotient with
  | nil => exact EvalsToInTime.refl _ _
  | cons b bs ih =>
    have hs : postMachine.step
        (postCfg .numerator state (binaryWord (b :: bs) ++ .slash :: denominator)
          (binaryWord quotient) [] []) =
        some (postCfg .numerator (advance state b)
          (binaryWord bs ++ .slash :: denominator)
          (binaryWord (quotientBit state.remainder b :: quotient)) [] []) := by
      cases b <;>
        apply congrArg some <;>
        simp only [binaryWord, List.map_cons, List.cons_append] <;>
        dsimp [postMachine, TM2.stepAux, postCfg, postStacks, bitSymbol, advance, isSymbol,
          isSymbol, symbolEq, readSymbol, clearSymbol] <;>
        congr 1 <;>
        funext j <;>
        cases j <;> rfl
    let one : EvalsToInTime postMachine.step
        (postCfg .numerator state (binaryWord (b :: bs) ++ .slash :: denominator)
          (binaryWord quotient) [] [])
        (some (postCfg .numerator (advance state b)
          (binaryWord bs ++ .slash :: denominator)
          (binaryWord (quotientBit state.remainder b :: quotient)) [] [])) 1 :=
      { steps := 1, evals_in_steps := hs, steps_le_m := by decide }
    exact EvalsToInTime.trans postMachine.step 1 bs.length _ _ _ one
      (ih (advance state b) (quotientBit state.remainder b :: quotient))

def responseWord (numeratorTail : List Bool) (exponent : Nat) : List ResponseSymbol :=
  binaryWord (true :: numeratorTail) ++ .slash :: .one :: List.replicate exponent .zero

def responseOutput (numeratorTail : List Bool) (exponent : Nat) : List Bool :=
  let q := (scan ⟨1, none, true⟩ [false] numeratorTail).2
  canonicalBinary (if exponent = 0 then (false :: q).reverse
    else (q.drop (exponent - 1)).reverse)

def denominatorRun (state : PostControl) (q : List Bool) (e : Nat)
    (hodd : 0 < e -> state.last = true) :
    EvalsToInTime postMachine.step
      (postCfg .denominatorFirst state (.one :: List.replicate e .zero)
        (binaryWord q) [] [])
      (some (haltList postMachine (binaryWord (canonicalBinary
        (if e = 0 then (false :: q).reverse else (q.drop (e - 1)).reverse)))))
      (2 * q.length + 2 * e + 6) := by
  have hh : postMachine.step
      (postCfg .denominatorFirst state (.one :: List.replicate e .zero)
        (binaryWord q) [] []) =
      some (postCfg .denominatorTail (clearSymbol state) (List.replicate e .zero)
        (binaryWord q) [] []) := by
    apply congrArg some
    dsimp [postMachine, TM2.stepAux, postCfg, postStacks, isSymbol, symbolEq,
      readSymbol, clearSymbol]
    congr 1
    funext j
    cases j <;> rfl
  let head : EvalsToInTime postMachine.step
      (postCfg .denominatorFirst state (.one :: List.replicate e .zero)
        (binaryWord q) [] [])
      (some (postCfg .denominatorTail (clearSymbol state) (List.replicate e .zero)
        (binaryWord q) [] [])) 1 :=
    { steps := 1, evals_in_steps := hh, steps_le_m := by decide }
  cases e with
  | zero =>
    have ht : postMachine.step
        (postCfg .denominatorTail (clearSymbol state) [] (binaryWord q) [] []) =
        some (postCfg .reverse (clearSymbol (clearSymbol state)) []
          (binaryWord (false :: q)) [] []) := by
      apply congrArg some
      simp only [binaryWord, List.map_cons]
      dsimp [postMachine, TM2.stepAux, postCfg, postStacks, isSymbol, symbolEq,
        bitSymbol, readSymbol, clearSymbol]
      congr 1
      funext j
      cases j <;> rfl
    let tail : EvalsToInTime postMachine.step
        (postCfg .denominatorTail (clearSymbol state) [] (binaryWord q) [] [])
        (some (postCfg .reverse (clearSymbol (clearSymbol state)) []
          (binaryWord (false :: q)) [] [])) 1 :=
      { steps := 1, evals_in_steps := ht, steps_le_m := by decide }
    have h := EvalsToInTime.trans postMachine.step 1
      (2 * (false :: q).length + 2) _ _ _ tail
      (reverseRun (clearSymbol (clearSymbol state)) (false :: q) [])
    have h' := EvalsToInTime.trans postMachine.step 1
      ((2 * (false :: q).length + 2) + 1) _ _ _ head h
    simp only [List.append_nil] at h'
    have result : EvalsToInTime postMachine.step
        (postCfg .denominatorFirst state [.one] (binaryWord q) [] [])
        (some (haltList postMachine
          (binaryWord (canonicalBinary (false :: q).reverse)))) (2 * q.length + 6) := by
      refine { h' with steps_le_m := ?_ }
      have hb := h'.steps_le_m
      simp only [List.length_cons] at hb
      omega
    simpa using result
  | succ k =>
    have hl : state.last = true := hodd (by omega)
    have ht : postMachine.step
        (postCfg .denominatorTail (clearSymbol state) (List.replicate (k + 1) .zero)
          (binaryWord q) [] []) =
        some (postCfg .denominatorZeros (clearSymbol (clearSymbol state))
          (List.replicate k .zero) (binaryWord q) [] []) := by
      apply congrArg some
      simp only [List.replicate_succ]
      dsimp [postMachine, TM2.stepAux, postCfg, postStacks, isSymbol, symbolEq,
        readSymbol, clearSymbol]
      simp only [hl, show (true && true) = true from rfl]
      dsimp only [cond]
      congr 1
      funext j
      cases j <;> rfl
    let tail : EvalsToInTime postMachine.step
        (postCfg .denominatorTail (clearSymbol state) (List.replicate (k + 1) .zero)
          (binaryWord q) [] [])
        (some (postCfg .denominatorZeros (clearSymbol (clearSymbol state))
          (List.replicate k .zero) (binaryWord q) [] [])) 1 :=
      { steps := 1, evals_in_steps := ht, steps_le_m := by decide }
    have h := EvalsToInTime.trans postMachine.step 1 (2 * q.length + 2 * k + 4)
      _ _ _ tail (denominatorZerosRun (clearSymbol (clearSymbol state)) q k 0)
    have h' := EvalsToInTime.trans postMachine.step 1
      ((2 * q.length + 2 * k + 4) + 1) _ _ _ head h
    simp only [Nat.zero_add] at h'
    have result : EvalsToInTime postMachine.step
        (postCfg .denominatorFirst state (.one :: List.replicate (k + 1) .zero)
          (binaryWord q) [] [])
        (some (haltList postMachine (binaryWord (canonicalBinary (q.drop k).reverse))))
        (2 * q.length + 2 * (k + 1) + 6) := by
      refine { h' with steps_le_m := ?_ }
      have hb := h'.steps_le_m
      omega
    simpa using result

theorem dyadic_response_run (xs : List Bool) (e : Nat)
    (divisible : 3 ∣ msbValue (true :: xs))
    (oddNumerator : 0 < e -> Odd (msbValue (true :: xs))) :
    Nonempty (TM2OutputsInTime postMachine (responseWord xs e)
      (some (binaryWord (responseOutput xs e))) (4 * (responseWord xs e).length + 4)) ∧
    msbValue (responseOutput xs e) =
      if e = 0 then 2 * (msbValue (true :: xs) / 3)
      else (msbValue (true :: xs) / 3) / 2 ^ (e - 1) := by
  have scanBridge : ∀ (st : PostControl) (q bs : List Bool),
      (scan st q bs).2 = (divisionScan 3 ⟨q, st.remainder.val⟩ bs).quotient ∧
      (scan st q bs).1.remainder.val =
        (divisionScan 3 ⟨q, st.remainder.val⟩ bs).remainder := by
    intro st q bs
    induction bs generalizing st q with
    | nil => exact ⟨rfl, rfl⟩
    | cons b bs ih =>
      have hstep : divisionScanStep 3 ⟨q, st.remainder.val⟩ b =
          ⟨quotientBit st.remainder b :: q, (nextRemainder st.remainder b).val⟩ := by
        rcases st with ⟨r, held, last⟩
        fin_cases r <;> cases b <;> rfl
      simpa only [scan, divisionScan, hstep, advance] using
        ih (advance st b) (quotientBit st.remainder b :: q)
  let st : PostControl := (scan ⟨1, none, true⟩ [false] xs).1
  let q : List Bool := (scan ⟨1, none, true⟩ [false] xs).2
  obtain ⟨hq, hr⟩ := scanBridge ⟨1, none, true⟩ [false] xs
  change q = (divisionScan 3 ⟨[false], 1⟩ xs).quotient at hq
  change st.remainder.val = (divisionScan 3 ⟨[false], 1⟩ xs).remainder at hr
  have hv := (divisionScan_invariant (d := 3) (by decide) xs
    ⟨[false], 1⟩ (by decide)).1
  change bitsValue (divisionScan 3 ⟨[false], 1⟩ xs).quotient * 3 +
    (divisionScan 3 ⟨[false], 1⟩ xs).remainder = msbValueFrom 1 xs at hv
  rw [← hq, ← hr] at hv
  change bitsValue q * 3 + st.remainder.val = msbValue (true :: xs) at hv
  have hrem : st.remainder = 0 := by
    apply Fin.ext
    have hb := st.remainder.isLt
    rcases divisible with ⟨a, ha⟩
    omega
  have hqValue : bitsValue q = msbValue (true :: xs) / 3 := by
    have hz := congrArg Fin.val hrem
    change st.remainder.val = 0 at hz
    omega
  have parity : ∀ (bs : List Bool) (s : PostControl) (ys : List Bool) (a : Nat),
      (s.last = true ↔ Odd a) ->
      ((scan s ys bs).1.last = true ↔ Odd (msbValueFrom a bs)) := by
    intro bs
    induction bs with
    | nil => intro s ys a ha; exact ha
    | cons b bs ih =>
      intro s ys a _
      apply ih (advance s b) (quotientBit s.remainder b :: ys) (2 * a + b.toNat)
      cases b with
      | false =>
        change (false = true) ↔ Odd (2 * a)
        constructor
        · intro h; cases h
        · rintro ⟨k, hk⟩; omega
      | true =>
        change (true = true) ↔ Odd (2 * a + 1)
        constructor
        · intro _; exact ⟨a, by omega⟩
        · intro _; rfl
  have hlast : 0 < e -> st.last = true := by
    intro he
    have hp := parity xs ⟨1, none, true⟩ [false] 1 (by
      constructor
      · intro _; exact ⟨0, by decide⟩
      · intro _; rfl)
    exact hp.mpr (oddNumerator he)
  have hql : q.length = xs.length + 1 := by
    rw [hq]
    simpa [Nat.add_comm] using divisionScan_quotient_length 3 ⟨[false],1⟩ xs
  have firstStep : postMachine.step (initList postMachine (responseWord xs e)) =
      some (postCfg .numerator ⟨1, none, true⟩
        (binaryWord xs ++ .slash :: .one :: List.replicate e .zero)
        (binaryWord [false]) [] []) := by
    apply congrArg some
    simp only [responseWord, binaryWord, List.map_cons, List.map_nil, List.cons_append]
    dsimp [postMachine, TM2.stepAux, initList, postCfg, postStacks, bitSymbol,
      isSymbol, symbolEq, readSymbol, clearSymbol]
    congr 1
    funext j
    cases j <;> rfl
  have slashStep : postMachine.step
      (postCfg .numerator st (.slash :: .one :: List.replicate e .zero)
        (binaryWord q) [] []) =
      some (postCfg .denominatorFirst (clearSymbol st) (.one :: List.replicate e .zero)
        (binaryWord q) [] []) := by
    apply congrArg some
    dsimp [postMachine, TM2.stepAux, postCfg, postStacks, isSymbol, symbolEq,
      readSymbol, clearSymbol]
    simp only [hrem, show decide ((0 : Fin 3).val = 0) = true from rfl]
    dsimp only [cond]
    congr 1
    funext j
    cases j <;> rfl
  let first : EvalsToInTime postMachine.step
      (initList postMachine (responseWord xs e))
      (some (postCfg .numerator ⟨1, none, true⟩
        (binaryWord xs ++ .slash :: .one :: List.replicate e .zero)
        (binaryWord [false]) [] [])) 1 :=
    { steps := 1, evals_in_steps := firstStep, steps_le_m := by decide }
  let slash : EvalsToInTime postMachine.step
      (postCfg .numerator st (.slash :: .one :: List.replicate e .zero)
        (binaryWord q) [] [])
      (some (postCfg .denominatorFirst (clearSymbol st) (.one :: List.replicate e .zero)
        (binaryWord q) [] [])) 1 :=
    { steps := 1, evals_in_steps := slashStep, steps_le_m := by decide }
  have tail := denominatorRun (clearSymbol st) q e hlast
  have afterSlash := EvalsToInTime.trans postMachine.step 1
    (2 * q.length + 2 * e + 6) _ _ _ slash tail
  have afterNumerator := EvalsToInTime.trans postMachine.step xs.length
    ((2 * q.length + 2 * e + 6) + 1) _ _ _
    (numeratorRun ⟨1, none, true⟩ xs [false] (.one :: List.replicate e .zero)) afterSlash
  have run := EvalsToInTime.trans postMachine.step 1
    (((2 * q.length + 2 * e + 6) + 1) + xs.length) _ _ _ first afterNumerator
  have canonicalValue : ∀ bs, msbValue (canonicalBinary bs) = msbValue bs := by
    intro bs
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      cases b with
      | false => simpa only [canonicalBinary, msbValue, msbValueFrom, Bool.toNat_false,
          Nat.mul_zero, Nat.zero_add] using ih
      | true => rfl
  have digitBridge : ∀ bs : List Bool,
      bitsValue bs = Nat.ofDigits 2 (bs.map Bool.toNat) := by
    intro bs
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp [bitsValue, Nat.bit_val, Nat.ofDigits_cons, ih, Nat.add_comm, Nat.mul_comm]
  have dropValue : ∀ (k : Nat) (bs : List Bool),
      bitsValue (bs.drop k) = bitsValue bs / 2 ^ k := by
    intro k bs
    have bound : ∀ d ∈ bs.map Bool.toNat, d < 2 := by
      intro d hd
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp hd
      cases b <;> decide
    rw [digitBridge, digitBridge, List.map_drop]
    exact (Nat.ofDigits_div_pow_eq_ofDigits_drop k (by decide)
      (bs.map Bool.toNat) bound).symm
  constructor
  · refine ⟨?_⟩
    change EvalsToInTime postMachine.step _ _ _
    refine { run with steps_le_m := ?_ }
    have hb := run.steps_le_m
    simp only [responseWord, binaryWord, List.length_append, List.length_map,
      List.length_cons, List.length_replicate] at ⊢
    omega
  · rw [responseOutput, canonicalValue]
    split_ifs with he
    · rw [msbValue_reverse]
      simp only [bitsValue, Nat.bit_val, Bool.toNat_false, Nat.add_zero]
      rw [hqValue]
    · rw [msbValue_reverse, dropValue, hqValue]

end PredictiveThermodynamic
