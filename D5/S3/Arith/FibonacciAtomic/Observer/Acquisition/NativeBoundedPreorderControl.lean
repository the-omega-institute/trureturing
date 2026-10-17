/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Path compression of the actual preorder frontier and bounded trial control. -/

import D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial
import D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord

/-! The cursor retains only an address. Pending siblings and report sequences
are mathematical relations used to compare it with the full acquisition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl

open GenealogicalFiberTransport (Source substitution composition)
open ActualTreeReadoutAcquisition (Address Reply readout acquisitionTrace acquisitionStep
  frontier acquisitionPolicy)
open BoundedPreorderTrial (History branches leafVisits betas parity trial)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (execute)
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution (Instruction Run)

/-- Pending right siblings, deepest first. This list is mathematical data. -/
def rightsPending : Address → List Address
  | [] => []
  | false :: p => (rightsPending p).map (false :: ·) ++ [[true]]
  | true :: p => (rightsPending p).map (true :: ·)

/-- Replace the last left edge by a right edge and discard its suffix. -/
def nextPath : Address → Option Address
  | [] => none
  | false :: p => match nextPath p with
      | none => some [true]
      | some q => some (false :: q)
  | true :: p => (nextPath p).map (true :: ·)

/-- The empty cursor denotes a completed traversal. -/
def pending : Option Address → List Address
  | none => []
  | some p => p :: rightsPending p

/-- A branch descends left; any closed node advances to the next sibling. -/
def cursorStep (p : Address) (r : Reply) : Option Address :=
  if r = .branch then some (p ++ [false]) else nextPath p

private theorem pending_next (p : Address) : pending (nextPath p) = rightsPending p := by
  induction p with
  | nil => rfl
  | cons d p ih =>
    cases d <;> cases hp : nextPath p with
    | none => simp [nextPath, hp, pending, rightsPending] at ih ⊢; simp [← ih]
    | some q =>
        simp only [hp, pending] at ih
        simp [nextPath, hp, pending, rightsPending, ← ih]

private theorem pending_left (p : Address) :
    rightsPending (p ++ [false]) = (p ++ [true]) :: rightsPending p := by
  induction p with
  | nil => rfl
  | cons d p ih => cases d <;> simp [rightsPending, ih]

private theorem cursor_frontier (p : Address) (r : Reply) :
    pending (cursorStep p r) = acquisitionStep (pending (some p)) ⟨p, r⟩ := by
  by_cases hr : r = .branch
  · simp [cursorStep, hr, pending, acquisitionStep, pending_left]
  · rw [cursorStep, ite_eq_right hr, pending_next]
    simp [pending, acquisitionStep, hr]

/-- A report sequence chosen by the path rule itself, with no source argument. -/
inductive CursorRun : Option Address → History → Option Address → Prop
  | nil (c : Option Address) : CursorRun c [] c
  | cons (p : Address) (r : Reply) {s : History} {c : Option Address} :
      CursorRun (cursorStep p r) s c → CursorRun (some p) (⟨p, r⟩ :: s) c

private theorem cursor_fold {c d : Option Address} {s : History}
    (run : CursorRun c s d) : s.foldl acquisitionStep (pending c) = pending d := by
  induction run with
  | nil => rfl
  | cons p r _ ih =>
      simp only [List.foldl_cons, ← cursor_frontier]
      exact ih

private theorem execute_cursor (n : Nat) (h : History) (u : Source)
    (s : History) (b : Bool) (c : Option Address)
    (hc : frontier h = pending c)
    (run : execute readout acquisitionPolicy n h u = some (s, b)) :
    CursorRun c s none := by
  induction n generalizing h s c with
  | zero => simp [execute] at run
  | succ n ih =>
    cases c with
    | none =>
      cases hb : acquisitionPolicy h with
      | inl q =>
        simp only [acquisitionPolicy, hc, pending] at hb
        split at hb <;> contradiction
      | inr v =>
        simp only [execute, hb, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        exact .nil none
    | some p =>
      have hp : acquisitionPolicy h = .inl p := by simp [acquisitionPolicy, hc, pending]
      simp only [execute, hp] at run
      obtain ⟨⟨t, v⟩, rest, eq⟩ := Option.map_eq_some_iff.mp run
      simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      apply CursorRun.cons
      apply ih (h ++ [⟨p, readout p u⟩]) t (cursorStep p (readout p u)) _ rest
      simp only [ActualTreeReadoutAcquisition.frontier, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      change acquisitionStep (frontier h) ⟨p, readout p u⟩ = _
      rw [hc, ← cursor_frontier]

private theorem cursor_split {c d : Option Address} {s t : History}
    (run : CursorRun c (s ++ t) d) :
    ∃ e, CursorRun c s e ∧ CursorRun e t d := by
  induction s generalizing c with
  | nil => exact ⟨c, .nil c, run⟩
  | cons a s ih =>
    cases run with
    | cons p r rest =>
      obtain ⟨e, left, right⟩ := ih rest
      exact ⟨e, .cons p r left, right⟩

/-- Prefixes of the path-selected actual traversal, with histories only as labels. -/
inductive ActualCursorPrefix (u : Source) : Option Address → History → Prop
  | initial : ActualCursorPrefix u (some []) []
  | read {p : Address} {h : History} : ActualCursorPrefix u (some p) h →
      ActualCursorPrefix u (cursorStep p (readout p u)) (h ++ [⟨p, readout p u⟩])

private theorem actual_cursor_residual (u : Source) {c : Option Address} {h : History}
    (actual : ActualCursorPrefix u c h) :
    CursorRun (some []) h c ∧ ∃ s, acquisitionTrace [] u = h ++ s ∧
      CursorRun c s none := by
  have full : CursorRun (some []) (acquisitionTrace [] u) none :=
    execute_cursor _ [] u _ _ (some []) rfl (ActualTreeReadoutAcquisition.acquisition_foundation.2 u)
  have truth := (D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.execute_transfer
    readout acquisitionPolicy _ [] u _ _
    (ActualTreeReadoutAcquisition.acquisition_foundation.2 u)).1
  induction actual with
  | initial => exact ⟨.nil _, _, rfl, full⟩
  | @read p h previous ih =>
    obtain ⟨pref, s, hs, suffix⟩ := ih
    cases suffix with
    | @cons _ r s _ tail =>
      have hr : readout p u = r := truth ⟨p, r⟩ (by rw [hs]; simp)
      subst r
      have one : CursorRun (some p) [⟨p, readout p u⟩] (cursorStep p (readout p u)) :=
        .cons p (readout p u) (.nil _)
      have join {x y z : Option Address} {a b : History}
          (left : CursorRun x a y) (right : CursorRun y b z) :
          CursorRun x (a ++ b) z := by
        induction left with
        | nil => exact right
        | cons p r _ ih => exact .cons p r (ih right)
      exact ⟨join pref one, s, by simpa only [List.append_assoc, List.singleton_append]
        using hs, tail⟩

/-- Every actual finite cursor prefix agrees with the source producer's order,
and the entire unvisited address queue is determined by the current path. -/
theorem reachable_compressed_frontier_and_trial_simulation (u : Source) :
    CursorRun (some []) (acquisitionTrace [] u) none ∧
    (∀ (c : Option Address) (h : History), ActualCursorPrefix u c h →
      h.IsPrefix (acquisitionTrace [] u) ∧ frontier h = pending c ∧
      CursorRun (some []) h c) ∧
    (∀ (h : History) (a : BoundedPreorderTrial.Report) (s : History),
      acquisitionTrace [] u = h ++ a :: s →
      CursorRun (some []) h (some a.1) ∧
      frontier h = a.1 :: rightsPending a.1 ∧
      CursorRun (cursorStep a.1 a.2) s none) := by
  have full : CursorRun (some []) (acquisitionTrace [] u) none :=
    execute_cursor _ [] u _ _ (some []) rfl (ActualTreeReadoutAcquisition.acquisition_foundation.2 u)
  refine ⟨full, ?_, ?_⟩
  · intro c h actual
    obtain ⟨run, s, hs, _⟩ := actual_cursor_residual u actual
    exact ⟨⟨s, hs.symm⟩, cursor_fold run, run⟩
  · intro h a s hs
    have split := full
    rw [hs] at split
    obtain ⟨c, pref, suffix⟩ := cursor_split split
    cases suffix with
    | cons p r tail => exact ⟨pref, cursor_fold pref, tail⟩

open DelayedOriginalReadout (rights halfCeil rightClock right_clock_iterate
  right_clock_readout decodeLabel guardAccept)

/-- The seven mode values occupy codes zero through six, in this order. -/
inductive Mode where
  | value | guard | poll | update | halt0 | halt1 | error
  deriving DecidableEq

/-- All intermediate fields. No source, stack, or history is retained. -/
structure Control where
  p : Address
  s : Nat
  b : Nat
  l : Nat
  j : Nat
  a : Bool
  mu : Mode
  deriving DecidableEq

/-- Constants of one installed bounded controller. -/
structure Parameters where
  h : Nat
  start : Nat
  last : Nat
  pollDepth : Nat
  active : Bool

/-- Canonical exceptional and polling controls have every other field zero. -/
def canonical (mu : Mode) : Control := ⟨[], 0, 0, 0, 0, false, mu⟩

/-- Each trial begins with only its candidate index nonzero. -/
def fresh (j : Nat) : Control := ⟨[], 0, 0, 0, j, false, .value⟩

/-- A new nonroot query has a guard exactly when its offset is positive. -/
def queryMode (N : Nat) (p : Address) : Mode :=
  if N = 0 ∨ p = [] then .value else .guard

/-- Typed decoded fields, before bit padding is considered. -/
def Valid (P : Parameters) (z : Control) : Prop :=
  match z.mu with
  | .value | .guard => z.s = z.p.length ∧ z.s < P.h ∧ z.b < P.h ∧
      z.l ≤ P.h ∧ z.j ≤ P.last ∧
      (z.mu = .guard → 0 < P.start + z.j ∧ z.p ≠ [])
  | .poll | .update => P.active = true ∧ z = canonical z.mu
  | .halt0 | .halt1 | .error => z = canonical z.mu

local instance validDecidable (P : Parameters) (z : Control) : Decidable (Valid P z) := by
  unfold Valid
  split <;> infer_instance

/-- Total virtual-reply rows; invalid paths, counters, and candidates fail closed. -/
def virtualDelta (P : Parameters) (z : Control) (r : Reply) : Control :=
  match r with
  | .absent => canonical .error
  | .branch =>
      if z.b + 1 = P.h then
        if z.j < P.last then fresh (z.j + 1) else canonical .error
      else if z.b + 1 < P.h ∧ z.s + 1 < P.h then
        { z with
          p := z.p ++ [false]
          s := z.s + 1
          b := z.b + 1
          mu := queryMode (P.start + z.j) (z.p ++ [false]) }
      else canonical .error
  | .alpha | .beta =>
      if z.l = P.h then canonical .error else
      let a := Bool.xor z.a (r == .beta)
      match nextPath z.p with
      | some q => { z with
          p := q
          s := q.length
          l := z.l + 1
          a := a
          mu := queryMode (P.start + z.j) q }
      | none => if z.l + 1 = P.h ∧ z.b = P.h - 1 then
          canonical (if a then .halt1 else .halt0) else canonical .error

/-- The source-blind row program, including all unsupported typed replies. -/
def controlProgram (P : Parameters) (z : Control) : Instruction Control Address Reply :=
  if Valid P z then
    match z.mu with
    | .value => .read (z.p ++ rights (halfCeil (P.start + z.j)))
        (fun r => virtualDelta P z (decodeLabel (P.start + z.j) r))
    | .guard => .read (z.p.dropLast ++ rights ((P.start + z.j) / 2 + 1))
        (fun r => if guardAccept (P.start + z.j) r then { z with mu := .value }
          else canonical .error)
    | .poll => .read (rights P.pollDepth) (fun r => match r with
        | .absent => canonical .update
        | .alpha => fresh 0
        | .beta | .branch => canonical .error)
    | .update => .update (canonical .poll)
    | .halt0 | .halt1 => .halt
    | .error => .read [] (fun _ => canonical .error)
  else .read [] (fun _ => canonical .error)

end D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl
