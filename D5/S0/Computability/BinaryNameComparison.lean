/- GID: D5/S0/Computability/BinaryNameComparison
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryNameComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Computability.TuringMachine.Computable]
   utility: kind=checker; basis=consumer=D5/S0/Computability/BinaryNameDictionary.dictionary_lookup_run; instance=D5/S0/Computability/ConventionalClauseWords.comparisonSource
   digest: Paid comparison and restoration of arbitrary binary variable names. -/

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype

/-!
The dictionary converter compares binary spellings, never their potentially
exponential numeric values. This fixed finite routine handles different lengths,
backs up every consumed bit, restores both operands and preserves a caller frame.
Whole-name equality is checker infrastructure. The actual dictionary lookup
execution uses the comparison result to select its found or next-entry branch.
comparisonSource is a conventional clause containing the two opposite literals
of the same canonical binary name. Its name identification is the repeated-name
case required by the original counting converter, without adding a variable.
The exact source parse, independent count, comparison and restored dictionary
lookup applications are checked transiently; this routine does not certify a
physical response.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic.BinaryNames

open Turing StateTransition

inductive CompareStack
  | left | right | savedLeft | savedRight | output | frame
  deriving DecidableEq, Fintype, Inhabited

inductive CompareLabel
  | compare | restoreLeft | restoreRight | finish
  deriving DecidableEq, Fintype, Inhabited

structure CompareControl where
  left : Option Bool := none
  right : Option Bool := none
  equal : Bool := true
  deriving DecidableEq, Fintype, Inhabited

def clear (s : CompareControl) : CompareControl := { s with left := none, right := none }

def compareMachine : FinTM2 where
  K := CompareStack
  k₀ := .left
  k₁ := .output
  Γ _ := Bool
  Λ := CompareLabel
  main := .compare
  σ := CompareControl
  initialState := ⟨none, none, true⟩
  m
    | .compare =>
      .pop .left (fun s b => { s with left := b }) <|
      .pop .right (fun s b => { s with right := b }) <|
      .branch (fun s => s.left.isNone && s.right.isNone)
        (.load clear <| .goto fun _ => .restoreLeft)
        (.load (fun s => { s with equal := s.equal && decide (s.left = s.right) }) <|
          .branch (fun s => s.left.isSome)
            (.push .savedLeft (fun s => s.left.getD false) <|
              .branch (fun s => s.right.isSome)
                (.push .savedRight (fun s => s.right.getD false) <|
                  .load clear <| .goto fun _ => .compare)
                (.load clear <| .goto fun _ => .compare))
            (.push .savedRight (fun s => s.right.getD false) <|
              .load clear <| .goto fun _ => .compare))
    | .restoreLeft =>
      .pop .savedLeft (fun s b => { s with left := b }) <|
      .branch (fun s => s.left.isNone)
        (.load clear <| .goto fun _ => .restoreRight)
        (.push .left (fun s => s.left.getD false) <|
          .load clear <| .goto fun _ => .restoreLeft)
    | .restoreRight =>
      .pop .savedRight (fun s b => { s with right := b }) <|
      .branch (fun s => s.right.isNone)
        (.load clear <| .goto fun _ => .finish)
        (.push .right (fun s => s.right.getD false) <|
          .load clear <| .goto fun _ => .restoreRight)
    | .finish =>
      .push .output (fun s => s.equal) <|
      .load (fun _ => ⟨none, none, true⟩) .halt

def compareStacks (a b savedA savedB output frame : List Bool) : CompareStack → List Bool
  | .left => a
  | .right => b
  | .savedLeft => savedA
  | .savedRight => savedB
  | .output => output
  | .frame => frame

def compareCfg (label : Option CompareLabel) (s : CompareControl)
    (a b savedA savedB output frame : List Bool) : compareMachine.Cfg :=
  ⟨label, s, compareStacks a b savedA savedB output frame⟩

macro "name_transition" : tactic =>
  `(tactic| (
    apply congrArg some
    dsimp [compareMachine, TM2.stepAux, compareCfg, compareStacks, clear]
    simp [Function.update_apply, compareStacks] <;>
      first | rfl | (funext k; cases k <;> simp [Function.update_apply, compareStacks])))

/-- The actual routine reports whole-name equality, including the length test,
restores both unbounded operands, empties both backups and preserves the caller
frame and previous output. No comparison certificate or run is supplied. -/
theorem name_compare_run (a b output frame : List Bool) :
    Nonempty (EvalsToInTime compareMachine.step
      (compareCfg (some .compare) ⟨none, none, true⟩ a b [] [] output frame)
      (some (compareCfg none ⟨none, none, true⟩ a b [] []
        (decide (a = b) :: output) frame))
      (2 * (a.length + b.length) + 4)) := by
  let single : ∀ (x : compareMachine.Cfg) (y : Option compareMachine.Cfg),
      compareMachine.step x = y → EvalsToInTime compareMachine.step x y 1 :=
    fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  have finish : ∀ a b e, EvalsToInTime compareMachine.step
      (compareCfg (some .finish) ⟨none, none, e⟩ a b [] [] output frame)
      (some (compareCfg none ⟨none, none, true⟩ a b [] [] (e :: output) frame)) 1 := by
    intro a b e
    apply single
    name_transition
  have restoreB : ∀ saved a b e, EvalsToInTime compareMachine.step
      (compareCfg (some .restoreRight) ⟨none, none, e⟩ a b [] saved output frame)
      (some (compareCfg none ⟨none, none, true⟩ a (saved.reverse ++ b) [] []
        (e :: output) frame)) (saved.length + 2) := by
    intro saved
    induction saved with
    | nil =>
      intro a b e
      have hs : compareMachine.step
          (compareCfg (some .restoreRight) ⟨none, none, e⟩ a b [] [] output frame) =
          some (compareCfg (some .finish) ⟨none, none, e⟩ a b [] [] output frame) := by
        name_transition
      simpa using EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ hs) (finish a b e)
    | cons v saved ih =>
      intro a b e
      have hs : compareMachine.step
          (compareCfg (some .restoreRight) ⟨none, none, e⟩ a b [] (v :: saved) output frame) =
          some (compareCfg (some .restoreRight) ⟨none, none, e⟩ a (v :: b) [] saved output frame) := by
        cases v <;> name_transition
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (saved.length + 2) _ _ _ (single _ _ hs) (ih a (v :: b) e)
  have restoreA : ∀ savedA savedB a b e, EvalsToInTime compareMachine.step
      (compareCfg (some .restoreLeft) ⟨none, none, e⟩ a b savedA savedB output frame)
      (some (compareCfg none ⟨none, none, true⟩ (savedA.reverse ++ a)
        (savedB.reverse ++ b) [] [] (e :: output) frame))
      (savedA.length + savedB.length + 3) := by
    intro savedA
    induction savedA with
    | nil =>
      intro savedB a b e
      have hs : compareMachine.step
          (compareCfg (some .restoreLeft) ⟨none, none, e⟩ a b [] savedB output frame) =
          some (compareCfg (some .restoreRight) ⟨none, none, e⟩ a b [] savedB output frame) := by
        name_transition
      simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (savedB.length + 2) _ _ _ (single _ _ hs) (restoreB savedB a b e)
    | cons v savedA ih =>
      intro savedB a b e
      have hs : compareMachine.step
          (compareCfg (some .restoreLeft) ⟨none, none, e⟩ a b (v :: savedA) savedB output frame) =
          some (compareCfg (some .restoreLeft) ⟨none, none, e⟩ (v :: a) b savedA savedB output frame) := by
        cases v <;> name_transition
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using EvalsToInTime.trans _ 1
          (savedA.length + savedB.length + 3) _ _ _ (single _ _ hs)
          (ih savedB (v :: a) b e)
  have scan : ∀ a b savedA savedB e, EvalsToInTime compareMachine.step
      (compareCfg (some .compare) ⟨none, none, e⟩ a b savedA savedB output frame)
      (some (compareCfg (some .restoreLeft) ⟨none, none, e && decide (a = b)⟩
        [] [] (a.reverse ++ savedA) (b.reverse ++ savedB) output frame))
      (a.length + b.length + 1) := by
    intro a
    induction a with
    | nil =>
      intro b
      induction b with
      | nil =>
        intro savedA savedB e
        apply single
        cases e <;> name_transition
      | cons v b ih =>
        intro savedA savedB e
        have hs : compareMachine.step
            (compareCfg (some .compare) ⟨none, none, e⟩ [] (v :: b) savedA savedB output frame) =
            some (compareCfg (some .compare) ⟨none, none, false⟩ [] b savedA (v :: savedB) output frame) := by
          cases e <;> cases v <;> name_transition
        simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
          EvalsToInTime.trans _ 1 (b.length + 1) _ _ _ (single _ _ hs)
            (by simpa using ih savedA (v :: savedB) false)
    | cons u a ih =>
      intro b savedA savedB e
      cases b with
      | nil =>
        have hs : compareMachine.step
            (compareCfg (some .compare) ⟨none, none, e⟩ (u :: a) [] savedA savedB output frame) =
            some (compareCfg (some .compare) ⟨none, none, false⟩ a [] (u :: savedA) savedB output frame) := by
          cases e <;> cases u <;> name_transition
        simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
          EvalsToInTime.trans _ 1 (a.length + 1) _ _ _ (single _ _ hs)
            (ih [] (u :: savedA) savedB false)
      | cons v b =>
        have hs : compareMachine.step
            (compareCfg (some .compare) ⟨none, none, e⟩ (u :: a) (v :: b) savedA savedB output frame) =
            some (compareCfg (some .compare) ⟨none, none, e && decide (u = v)⟩
              a b (u :: savedA) (v :: savedB) output frame) := by
          cases e <;> cases u <;> cases v <;> name_transition
        have run := EvalsToInTime.trans _ 1 (a.length + b.length + 1) _ _ _
          (single _ _ hs) (ih b (u :: savedA) (v :: savedB) (e && decide (u = v)))
        have flags : ((e && decide (u = v)) && decide (a = b)) =
            (e && decide (u :: a = v :: b)) := by simp [Bool.and_assoc]
        rw [flags] at run
        simpa [List.reverse_cons, List.append_assoc] using
          (show EvalsToInTime compareMachine.step _ _
            ((u :: a).length + (v :: b).length + 1) from
            { run with steps_le_m := by have := run.steps_le_m; simp only [List.length_cons]; omega })
  have first := scan a b [] [] true
  have last := restoreA a.reverse b.reverse [] [] (decide (a = b))
  simp only [Bool.true_and, List.append_nil] at first
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at last
  exact ⟨by simpa [Nat.mul_add, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using (EvalsToInTime.trans _ (a.length + b.length + 1)
      (a.length + b.length + 3) _ _ _ first last)⟩

end PredictiveThermodynamic.BinaryNames
