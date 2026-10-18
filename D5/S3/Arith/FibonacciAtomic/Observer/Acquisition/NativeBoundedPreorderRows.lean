/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Path compression of the actual preorder frontier and bounded trial control. -/

import D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial
import D5.S3.Arith.FibonacciAtomic.Observer.NativePollingAlignment
import D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport

/-! The cursor retains only an address. Pending siblings and report sequences
are mathematical relations used to compare it with the full acquisition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows

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

private theorem cursor_balance {c d : Option Address} {s : History}
    (run : CursorRun c s d) (honest : ∀ a ∈ s, a.2 ≠ .absent) :
    (pending d).length + leafVisits s = (pending c).length + branches s := by
  induction run with
  | nil => simp [leafVisits, branches]
  | @cons p r s d rest ih =>
    have hr := honest ⟨p, r⟩ (by simp)
    have ht : ∀ a ∈ s, a.2 ≠ .absent := by
      intro a ha
      exact honest a (by simp [ha])
    have balance := ih ht
    rw [cursor_frontier] at balance
    cases r <;> simp [acquisitionStep, pending, branches, leafVisits] at hr balance ⊢ <;> omega

/-- A finite actual execution carrying a mathematical predicate at every point. -/
inductive RefinedRun (P : Parameters) (obs : Nat → Address → Reply)
    (I : Control → Nat → Prop) : Control → Nat → Control → Nat → Prop
  | refl (x : Control) (a : Nat) : I x a → RefinedRun P obs I x a x a
  | read {x : Control} {p : Address} {k : Reply → Control} {a : Nat}
      {y : Control} {b : Nat} : I x a → controlProgram P x = .read p k →
      RefinedRun P obs I (k (obs a p)) a y b → RefinedRun P obs I x a y b
  | update {x z : Control} {a : Nat} {y : Control} {b : Nat} :
      I x a → controlProgram P x = .update z → RefinedRun P obs I z (a + 1) y b →
      RefinedRun P obs I x a y b

private theorem refined_run {P : Parameters} {obs : Nat → Address → Reply}
    {I : Control → Nat → Prop} {x y : Control} {a b : Nat}
    (path : RefinedRun P obs I x a y b) : Run (controlProgram P) obs x a y b := by
  induction path with
  | refl => exact .refl _ _
  | read _ hop _ ih => exact .read hop ih
  | update _ hop _ ih => exact .update hop ih

private theorem refined_prefix {P : Parameters} {obs : Nat → Address → Reply}
    {I : Control → Nat → Prop} {x y : Control} {a b : Nat}
    (path : RefinedRun P obs I x a y b) (halt : controlProgram P y = .halt) :
    ∀ z e, Run (controlProgram P) obs x a z e → I z e := by
  induction path with
  | refl x a good =>
    intro z e other
    cases other with
    | refl => exact good
    | read hop _ => cases halt.symm.trans hop
    | update hop _ => cases halt.symm.trans hop
  | read good hop tail ih =>
    intro z e other
    cases other with
    | refl => exact good
    | read h rest => cases hop.symm.trans h; exact ih halt _ _ rest
    | update h _ => cases hop.symm.trans h
  | update good hop tail ih =>
    intro z e other
    cases other with
    | refl => exact good
    | read h _ => cases hop.symm.trans h
    | update h rest => cases hop.symm.trans h; exact ih halt _ _ rest

private theorem one_update_polling (P : Parameters) (u : Source)
    (active : P.active = true) (I : Control → Nat → Prop)
    (pollGood : ∀ a, rightClock u + a ≤ 2 * P.pollDepth → I (canonical .poll) a)
    (updateGood : ∀ a, rightClock u + a < 2 * P.pollDepth → I (canonical .update) a)
    (d : Nat) :
    ∀ a, rightClock u + a + d = 2 * P.pollDepth →
      ∀ final lastEpoch,
      RefinedRun P (NativePollingAlignment.observations u) I
        (fresh 0) (a + d) final lastEpoch →
      RefinedRun P (NativePollingAlignment.observations u) I
        (canonical .poll) a final lastEpoch := by
  induction d with
  | zero =>
    intro a clock final lastEpoch continuation
    have reply : NativePollingAlignment.observations u a (rights P.pollDepth) = .alpha :=
      (right_clock_readout P.pollDepth (substitution^[a] u)).2.1.mpr
        (by rw [right_clock_iterate]; omega)
    apply RefinedRun.read (pollGood a (by omega)) (p := rights P.pollDepth)
      (k := fun r => match r with
        | .absent => canonical .update
        | .alpha => fresh 0
        | .beta | .branch => canonical .error)
      (by simp [controlProgram, Valid, canonical, active])
    rw [reply]
    simpa using continuation
  | succ d ih =>
    intro a clock final lastEpoch continuation
    have reply : NativePollingAlignment.observations u a (rights P.pollDepth) = .absent :=
      (right_clock_readout P.pollDepth (substitution^[a] u)).1.mpr
        (by rw [right_clock_iterate]; omega)
    apply RefinedRun.read (pollGood a (by omega)) (p := rights P.pollDepth)
      (k := fun r => match r with
        | .absent => canonical .update
        | .alpha => fresh 0
        | .beta | .branch => canonical .error)
      (by simp [controlProgram, Valid, canonical, active])
    rw [reply]
    apply RefinedRun.update (updateGood a (by omega)) (z := canonical .poll)
      (by simp [controlProgram, Valid, canonical, active])
    apply ih (a + 1) (by omega) final lastEpoch
    convert continuation using 1 <;> omega

private theorem right_clock_size (u : Source) : rightClock u ≤ 2 * u.length - 1 := by
  induction u with
  | of b => cases b <;> decide
  | mul x y _hx hy =>
    have positive := x.length_pos
    have positiveY := y.length_pos
    change 2 + rightClock y ≤ 2 * (x.length + y.length) - 1
    omega

/-- The even right-ray threshold fixed at installation. -/
def alignmentBudget (h T : Nat) : Nat := 2 * halfCeil (T + 2 * h)

/-- Active alignment installs only a fixed starting offset and a short index range. -/
def activeParameters (h T : Nat) : Parameters :=
  ⟨h, alignmentBudget h T - 2 * h + 1, 2 * h - 1,
    alignmentBudget h T / 2, true⟩

/-- Actual one-Update polling reaches exactly the certified stationary interval. -/
theorem native_one_update_alignment (h T t : Nat) (u : Source)
    (hu : u.length = h) (ht : t ≤ T) :
    let B := alignmentBudget h T
    let U := B - t - rightClock u
    0 < U ∧ t + U = B - rightClock u ∧
    B - 2 * h + 1 ≤ t + U ∧ t + U ≤ B ∧
    t + U - (B - 2 * h + 1) ≤ 2 * h - 1 ∧
    Run (controlProgram (activeParameters h T))
      (NativePollingAlignment.observations (substitution^[t] u))
      (canonical .poll) 0 (fresh 0) U := by
  dsimp only
  have size := right_clock_size u
  rw [hu] at size
  have hh : 0 < h := by rw [← hu]; exact u.length_pos
  have rem := Nat.mod_lt (T + 2 * h) (by decide : 0 < 2)
  have div := Nat.mod_add_div (T + 2 * h) 2
  have lower : T + 2 * h ≤ alignmentBudget h T := by
    unfold alignmentBudget halfCeil
    omega
  have clock : rightClock (substitution^[t] u) +
      (alignmentBudget h T - t - rightClock u) =
      2 * (activeParameters h T).pollDepth := by
    rw [right_clock_iterate]
    simp only [activeParameters, alignmentBudget]
    have halve : 2 * halfCeil (T + 2 * h) / 2 = halfCeil (T + 2 * h) := by omega
    rw [halve]
    unfold alignmentBudget at lower
    omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  have certified := one_update_polling (activeParameters h T) (substitution^[t] u) rfl
    (fun _ _ => True) (by intros; trivial) (by intros; trivial)
    (alignmentBudget h T - t - rightClock u) 0 (by simpa using clock)
    (fresh 0) (alignmentBudget h T - t - rightClock u) (by
      simpa only [Nat.zero_add] using RefinedRun.refl (P := activeParameters h T)
        (obs := NativePollingAlignment.observations (substitution^[t] u))
        (I := fun _ _ => True) (fresh 0) (alignmentBudget h T - t - rightClock u) trivial)
  exact refined_run certified

private theorem trial_geometry (h τ N : Nat) (u y : Source)
    (spec : BoundedPreorderTrial.TrialSpec h τ N u y)
    (H : History) (a : BoundedPreorderTrial.Report) (tail : History)
    (split : trial h (BoundedPreorderTrial.virtualSource u τ N) = H ++ a :: tail) :
    CursorRun (some []) H (some a.1) ∧
    frontier H = a.1 :: rightsPending a.1 ∧
    branches H < h ∧ leafVisits H < h ∧ a.1.length < h := by
  let v := BoundedPreorderTrial.virtualSource u τ N
  have pre : (trial h v).IsPrefix (acquisitionTrace [] v) := List.take_prefix _ _
  obtain ⟨extra, full⟩ := pre
  have hs : acquisitionTrace [] v = H ++ a :: (tail ++ extra) := by
    rw [← full, split]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨run, front, _⟩ :=
    (reachable_compressed_frontier_and_trial_simulation v).2.2 H a (tail ++ extra) hs
  have pref : H.IsPrefix (acquisitionTrace [] v) := ⟨a :: (tail ++ extra), hs.symm⟩
  have before := spec.before_cutoff H.length (by rw [split]; simp)
  rw [← List.prefix_iff_eq_take.mp pref] at before
  have Hsub : H ⊆ trial h v := by rw [split]; exact List.subset_append_left _ _
  have honest : ∀ r ∈ H, r.2 ≠ .absent :=
    fun r hr => (spec.reached r (Hsub hr)).2
  have mass := cursor_balance run honest
  simp only [pending, rightsPending, List.length_cons, List.length_nil] at mass
  have member : a ∈ trial h v := by rw [split]; simp
  have depth := (spec.reached a member).1
  exact ⟨run, front, before, by omega, by omega⟩

/-- Mathematical comparison of fields with a report prefix; never used by the rows. -/
def atPrefix (j : Nat) (H : History) (p : Address) (mu : Mode) : Control :=
  ⟨p, p.length, branches H, leafVisits H, j, decide (betas H % 2 = 1), mu⟩

/-- A licensed proper trial prefix and its exact compressed control fields.
All quantified reports and frontiers are mathematical comparison data. -/
def TrialPoint (P : Parameters) (τ : Nat) (u : Source) (z : Control) : Prop :=
  ∃ N j H a tail,
    P.start + j = N ∧ N ≤ τ ∧ j ≤ P.last ∧
    trial P.h (BoundedPreorderTrial.virtualSource u τ N) = H ++ a :: tail ∧
    H.IsPrefix (acquisitionTrace [] (BoundedPreorderTrial.virtualSource u τ N)) ∧
    frontier H = a.1 :: rightsPending a.1 ∧
    branches H < P.h ∧ leafVisits H < P.h ∧ a.1.length < P.h ∧
    (z = atPrefix j H a.1 (queryMode N a.1) ∨ z = atPrefix j H a.1 .value)

private theorem guard_value_progress (P : Parameters) (τ N : Nat) (u y : Source)
    (spec : BoundedPreorderTrial.TrialSpec P.h τ N u y)
    (j : Nat) (hj : j ≤ P.last) (offset : P.start + j = N)
    (H : History) (a : BoundedPreorderTrial.Report) (tail : History)
    (split : trial P.h (BoundedPreorderTrial.virtualSource u τ N) = H ++ a :: tail)
    (obs : Nat → Address → Reply) (epoch : Nat)
    (response : ∀ p, obs epoch p = readout p y)
    (I : Control → Nat → Prop)
    (good : ∀ mu, mu = .value ∨ mu = queryMode N a.1 → I (atPrefix j H a.1 mu) epoch)
    (final : Control) (lastEpoch : Nat)
    (continuation : RefinedRun P obs I
      (virtualDelta P (atPrefix j H a.1 .value) a.2) epoch final lastEpoch) :
    RefinedRun P obs I
      (atPrefix j H a.1 (queryMode N a.1)) epoch final lastEpoch := by
  obtain ⟨_, _, hb, hl, hp⟩ := trial_geometry P.h τ N u y spec H a tail split
  have member : a ∈ trial P.h (BoundedPreorderTrial.virtualSource u τ N) := by
    rw [split]; simp
  have decoded := spec.decoded a member
  have label : decodeLabel N (readout (a.1 ++ rights (halfCeil N)) y) = a.2 := by
    by_cases hn : N = 0
    · simpa [hn, DelayedOriginalReadout.originalDecode, DelayedOriginalReadout.originalQueries,
        decodeLabel, halfCeil, rights] using decoded
    · by_cases root : a.1 = []
      · simpa [DelayedOriginalReadout.originalDecode, DelayedOriginalReadout.originalQueries,
          hn, root] using decoded
      · simpa [DelayedOriginalReadout.originalDecode, DelayedOriginalReadout.originalQueries,
          hn, root, spec.guard_accept a member root] using decoded
  have valid : Valid P (atPrefix j H a.1 .value) := by
    simpa [Valid, atPrefix] using And.intro hp ⟨hb, Nat.le_of_lt hl, hj⟩
  have value : RefinedRun P obs I (atPrefix j H a.1 .value) epoch
      final lastEpoch := by
    apply RefinedRun.read (good .value (Or.inl rfl)) (p := a.1 ++ rights (halfCeil N))
      (k := fun r => virtualDelta P (atPrefix j H a.1 .value) (decodeLabel N r))
      (by rw [controlProgram, ite_eq_left valid]; simp only [atPrefix, offset])
    rw [response, label]
    exact continuation
  by_cases direct : N = 0 ∨ a.1 = []
  · simpa [queryMode, direct] using value
  · have positive : 0 < N := by omega
    have nonroot : a.1 ≠ [] := fun root => direct (Or.inr root)
    have validGuard : Valid P (atPrefix j H a.1 .guard) := by
      simp [Valid, atPrefix, offset, hp, hb, Nat.le_of_lt hl, hj, positive, nonroot]
    simp only [queryMode, ite_eq_right direct]
    apply RefinedRun.read (good .guard (Or.inr (by simp [queryMode, direct])))
      (p := a.1.dropLast ++ rights (N / 2 + 1))
      (k := fun r => if guardAccept N r then
        { atPrefix j H a.1 .guard with mu := .value } else canonical .error)
      (by rw [controlProgram, ite_eq_left validGuard]; simp only [atPrefix, offset])
    rw [response, spec.guard_accept a member nonroot]
    simpa [atPrefix] using value

private theorem virtual_next (P : Parameters) (τ N : Nat) (u y : Source)
    (spec : BoundedPreorderTrial.TrialSpec P.h τ N u y)
    (j : Nat) (offset : P.start + j = N)
    (H : History) (a next : BoundedPreorderTrial.Report) (tail : History)
    (split : trial P.h (BoundedPreorderTrial.virtualSource u τ N) =
      H ++ a :: next :: tail) :
    virtualDelta P (atPrefix j H a.1 .value) a.2 =
      atPrefix j (H ++ [a]) next.1 (queryMode N next.1) := by
  have splitNext : trial P.h (BoundedPreorderTrial.virtualSource u τ N) =
      (H ++ [a]) ++ next :: tail := by simpa using split
  obtain ⟨_, front, _, hl, _⟩ := trial_geometry P.h τ N u y spec H a (next :: tail) split
  obtain ⟨_, frontNext, hbNext, _, depthNext⟩ :=
    trial_geometry P.h τ N u y spec (H ++ [a]) next tail splitNext
  have step : cursorStep a.1 a.2 = some next.1 := by
    have same : pending (cursorStep a.1 a.2) = next.1 :: rightsPending next.1 := by
      rw [cursor_frontier]
      change acquisitionStep (a.1 :: rightsPending a.1) a = _
      rw [← front, ← frontNext]
      simp [ActualTreeReadoutAcquisition.frontier, List.foldl_append]
    cases eq : cursorStep a.1 a.2 with
    | none => simp [eq, pending] at same
    | some p => simpa [eq, pending] using congrArg List.head? same
  have honest := (spec.reached a (by rw [split]; simp)).2
  cases reply : a.2 with
  | absent => exact (honest reply).elim
  | branch =>
    have path : a.1 ++ [false] = next.1 := by simpa [cursorStep, reply] using step
    have counts : branches H + 1 < P.h := by
      simpa [branches, reply] using hbNext
    have depth : a.1.length + 1 < P.h := by simpa [← path] using depthNext
    have len : a.1.length + 1 = next.1.length := by simpa using congrArg List.length path
    simp [virtualDelta, atPrefix, reply, counts, Nat.ne_of_lt counts, depth, path, offset]
    simp [branches, leafVisits, betas, reply, len]
  | alpha =>
    have path : nextPath a.1 = some next.1 := by simpa [cursorStep, reply] using step
    simp [virtualDelta, atPrefix, reply, Nat.ne_of_lt hl, path, offset]
    simp [branches, leafVisits, betas, reply, show (Reply.alpha == Reply.beta) = false by decide]
    rfl
  | beta =>
    have path : nextPath a.1 = some next.1 := by simpa [cursorStep, reply] using step
    have bits : Bool.xor (decide (betas H % 2 = 1)) true =
        decide ((betas H + 1) % 2 = 1) := by
      rcases (show betas H % 2 = 0 ∨ betas H % 2 = 1 by omega) with hm | hm
      all_goals simp [Nat.add_mod, hm]
    simp only [Bool.xor_true] at bits
    simp [virtualDelta, atPrefix, reply, Nat.ne_of_lt hl, path, offset, bits]
    simp [branches, leafVisits, betas, reply] at bits ⊢

private theorem virtual_finish (P : Parameters) (τ N : Nat) (u y : Source)
    (spec : BoundedPreorderTrial.TrialSpec P.h τ N u y)
    (j : Nat) (offset : P.start + j = N) (covers : τ ≤ P.start + P.last)
    (H : History) (a : BoundedPreorderTrial.Report)
    (split : trial P.h (BoundedPreorderTrial.virtualSource u τ N) = H ++ [a]) :
    virtualDelta P (atPrefix j H a.1 .value) a.2 =
      if branches (acquisitionTrace [] (BoundedPreorderTrial.virtualSource u τ N)) < P.h
      then canonical (if decide (betas (H ++ [a]) % 2 = 1) then .halt1 else .halt0)
      else fresh (j + 1) := by
  classical
  let v := BoundedPreorderTrial.virtualSource u τ N
  obtain ⟨_, _, _, hl, _⟩ := trial_geometry P.h τ N u y spec H a [] split
  have finalCursor (hc : BoundedPreorderTrial.Completes P.h v) :
      cursorStep a.1 a.2 = none := by
    have full : acquisitionTrace [] v = H ++ a :: [] :=
      (spec.completion hc).1.symm.trans split
    have suffix := (reachable_compressed_frontier_and_trial_simulation v).2.2 H a [] full
    have endRun := suffix.2.2
    generalize eq : cursorStep a.1 a.2 = c at endRun
    cases endRun
    rfl
  have leafComplete (hr : a.2 ≠ .branch) : BoundedPreorderTrial.Completes P.h v := by
    by_contra rejected
    have last := (spec.rejection rejected).2.1
    simpa [split, hr] using last
  have honest := (spec.reached a (by rw [split]; simp)).2
  cases reply : a.2 with
  | absent => exact (honest reply).elim
  | branch =>
    have rejected : ¬ BoundedPreorderTrial.Completes P.h v := by
      intro complete
      have impossible := finalCursor complete
      simp [cursorStep, reply] at impossible
    have reject := spec.rejection rejected
    have count : branches H + 1 = P.h := by simpa [split, branches, reply] using reject.1
    have next : j < P.last := by have before := reject.2.2; omega
    change ¬ branches (acquisitionTrace [] v) < P.h at rejected
    simp [virtualDelta, atPrefix, count, next, rejected, v]
  | alpha =>
    have complete := leafComplete (by simp [reply])
    have path : nextPath a.1 = none := by simpa [cursorStep, reply] using finalCursor complete
    obtain ⟨leaves, forks, _⟩ := spec.completed_counts complete
    have lc : leafVisits H + 1 = P.h := by simpa [split, leafVisits, reply] using leaves
    have bc : branches H = P.h - 1 := by simpa [split, branches, reply] using forks
    change branches (acquisitionTrace [] v) < P.h at complete
    simp [virtualDelta, atPrefix, Nat.ne_of_lt hl, path, lc, bc, complete, v]
    simp [betas, reply, show (Reply.alpha == Reply.beta) = false by decide]
    by_cases hm : List.countP (fun r => r.2 == Reply.beta) H % 2 = 1 <;> simp [hm]
  | beta =>
    have complete := leafComplete (by simp [reply])
    have path : nextPath a.1 = none := by simpa [cursorStep, reply] using finalCursor complete
    obtain ⟨leaves, forks, _⟩ := spec.completed_counts complete
    have lc : leafVisits H + 1 = P.h := by simpa [split, leafVisits, reply] using leaves
    have bc : branches H = P.h - 1 := by simpa [split, branches, reply] using forks
    change branches (acquisitionTrace [] v) < P.h at complete
    have bits : !decide (betas H % 2 = 1) = decide ((betas H + 1) % 2 = 1) := by
      rcases (show betas H % 2 = 0 ∨ betas H % 2 = 1 by omega) with hm | hm
      all_goals simp [Nat.add_mod, hm]
    simp [virtualDelta, atPrefix, Nat.ne_of_lt hl, path, lc, bc, complete, v, bits]
    simp [betas, reply] at bits ⊢
    rcases (show betas H % 2 = 0 ∨ betas H % 2 = 1 by omega) with hm | hm
    all_goals simp only [betas] at hm; simp [Nat.add_mod, hm]

private theorem trial_continuation (P : Parameters) (τ N : Nat) (u y : Source)
    (spec : BoundedPreorderTrial.TrialSpec P.h τ N u y)
    (j : Nat) (hj : j ≤ P.last) (offset : P.start + j = N)
    (obs : Nat → Address → Reply) (epoch : Nat)
    (response : ∀ p, obs epoch p = readout p y)
    (I : Control → Nat → Prop)
    (good : ∀ H a tail,
      trial P.h (BoundedPreorderTrial.virtualSource u τ N) = H ++ a :: tail →
      ∀ mu, mu = .value ∨ mu = queryMode N a.1 → I (atPrefix j H a.1 mu) epoch)
    (final : Control) (lastEpoch : Nat)
    (onLast : ∀ H a, trial P.h (BoundedPreorderTrial.virtualSource u τ N) = H ++ [a] →
      RefinedRun P obs I (virtualDelta P (atPrefix j H a.1 .value) a.2)
        epoch final lastEpoch) :
    ∀ tail H a, trial P.h (BoundedPreorderTrial.virtualSource u τ N) = H ++ a :: tail →
      RefinedRun P obs I (atPrefix j H a.1 (queryMode N a.1))
        epoch final lastEpoch := by
  intro tail
  induction tail with
  | nil =>
    intro H a split
    exact guard_value_progress P τ N u y spec j hj offset H a [] split
      obs epoch response I (good H a [] split) final lastEpoch (onLast H a split)
  | cons next tail ih =>
    intro H a split
    apply guard_value_progress P τ N u y spec j hj offset H a (next :: tail) split
      obs epoch response I (good H a (next :: tail) split) final lastEpoch
    rw [virtual_next P τ N u y spec j offset H a next tail split]
    exact ih (H ++ [a]) next (by simpa using split)

private theorem trial_root (h : Nat) (v : Source) :
    ∃ r tail, trial h v = (⟨[], r⟩ : BoundedPreorderTrial.Report) :: tail := by
  cases v with
  | of b => cases b <;> exact ⟨_, [], rfl⟩
  | mul x y =>
    simp only [trial, acquisitionTrace, BoundedPreorderTrial.cutLength]
    split
    · exact ⟨.branch, [], rfl⟩
    · simp only [Nat.add_comm 1, List.take_succ_cons]
      exact ⟨.branch, _, rfl⟩

private theorem stationary_refined_execution (P : Parameters) (τ : Nat) (u y : Source)
    (hu : u.length = P.h) (hy : y = substitution^[τ] u)
    (start : P.start ≤ τ) (covers : τ ≤ P.start + P.last)
    (regime : P.h % 2 = 0 ∨ τ = 0)
    (obs : Nat → Address → Reply) (epoch : Nat)
    (response : ∀ p, obs epoch p = readout p y) :
    let bit := decide ((composition u).2 % 2 = 1)
    let final := canonical (if bit then .halt1 else .halt0)
    RefinedRun P obs (fun z a => a = epoch ∧ (z = final ∨ TrialPoint P τ u z))
      (fresh 0) epoch final epoch := by
  dsimp only
  let final := canonical (if decide ((composition u).2 % 2 = 1) then .halt1 else .halt0)
  let I (z : Control) (a : Nat) : Prop := a = epoch ∧ (z = final ∨ TrialPoint P τ u z)
  obtain ⟨single, _, K, lower, upper, complete, minimal, _⟩ :=
    BoundedPreorderTrial.bounded_preorder_trial P.h τ P.start u y hu hy start
  have good (N j : Nat) (hN : N ≤ τ) (hj : j ≤ P.last) (offset : P.start + j = N)
      (spec : BoundedPreorderTrial.TrialSpec P.h τ N u y)
      (H : History) (a : BoundedPreorderTrial.Report) (tail : History)
      (split : trial P.h (BoundedPreorderTrial.virtualSource u τ N) = H ++ a :: tail)
      (mu : Mode) (hm : mu = .value ∨ mu = queryMode N a.1) :
      I (atPrefix j H a.1 mu) epoch := by
    obtain ⟨_, front, hb, hl, hp⟩ := trial_geometry P.h τ N u y spec H a tail split
    have pref : H.IsPrefix (acquisitionTrace [] (BoundedPreorderTrial.virtualSource u τ N)) :=
      (show H.IsPrefix (trial P.h (BoundedPreorderTrial.virtualSource u τ N))
        from ⟨a :: tail, split.symm⟩).trans (List.take_prefix _ _)
    refine ⟨rfl, Or.inr ⟨N, j, H, a, tail, offset, hN, hj, split, pref,
      front, hb, hl, hp, ?_⟩⟩
    rcases hm with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  have build : ∀ d j, P.start + j + d = K →
      RefinedRun P obs I (fresh j) epoch final epoch := by
    intro d
    induction d with
    | zero =>
      intro j eq
      have offset : P.start + j = K := by omega
      have hj : j ≤ P.last := by omega
      have spec := single K upper
      have parityEq : betas (trial P.h (BoundedPreorderTrial.virtualSource u τ K)) % 2 =
          (composition u).2 % 2 := by
        rcases regime with even | zero
        · exact (spec.completion complete).2.2 even
        · exact spec.endpoint_parity (by omega)
      obtain ⟨r, tail, root⟩ := trial_root P.h (BoundedPreorderTrial.virtualSource u τ K)
      have run := trial_continuation P τ K u y spec j hj offset obs epoch response I
        (good K j upper hj offset spec) final epoch
        (by
          intro H a split
          rw [virtual_finish P τ K u y spec j offset covers H a split]
          have done : branches (acquisitionTrace []
              (BoundedPreorderTrial.virtualSource u τ K)) < P.h := complete
          rw [ite_eq_left done, ← split, parityEq]
          exact .refl _ _ ⟨rfl, Or.inl rfl⟩) tail [] ⟨[], r⟩ (by simpa using root)
      simpa [atPrefix, fresh, queryMode, branches, leafVisits, betas] using run
    | succ d ih =>
      intro j eq
      let N := P.start + j
      have hN : N < K := by dsimp [N]; omega
      have hj : j ≤ P.last := by dsimp [N] at hN; omega
      have spec := single N (by omega)
      have rejected := minimal N (by dsimp [N]; omega) hN
      obtain ⟨r, tail, root⟩ := trial_root P.h (BoundedPreorderTrial.virtualSource u τ N)
      have run := trial_continuation P τ N u y spec j hj rfl obs epoch response I
        (good N j (by omega) hj rfl spec) final epoch
        (by
          intro H a split
          rw [virtual_finish P τ N u y spec j rfl covers H a split]
          have notDone : ¬ branches (acquisitionTrace []
              (BoundedPreorderTrial.virtualSource u τ N)) < P.h := rejected
          rw [ite_eq_right notDone]
          exact ih (j + 1) (by omega)) tail [] ⟨[], r⟩ (by simpa using root)
      simpa [atPrefix, fresh, queryMode, branches, leafVisits, betas] using run
  exact build (K - P.start) 0 (by omega)

/-- The independent bounded rows finish the increasing stationary trials with
the original parity; every actual prefix retains the licensed trial relation. -/
theorem native_stationary_bounded_execution (P : Parameters) (τ : Nat) (u y : Source)
    (hu : u.length = P.h) (hy : y = substitution^[τ] u)
    (start : P.start ≤ τ) (covers : τ ≤ P.start + P.last)
    (regime : P.h % 2 = 0 ∨ τ = 0)
    (obs : Nat → Address → Reply) (epoch : Nat)
    (response : ∀ p, obs epoch p = readout p y) :
    let bit := decide ((composition u).2 % 2 = 1)
    let final := canonical (if bit then .halt1 else .halt0)
    Run (controlProgram P) obs (fresh 0) epoch final epoch ∧
    controlProgram P final = .halt ∧
    (∀ z a, Run (controlProgram P) obs (fresh 0) epoch z a →
      controlProgram P z = .halt → z = final ∧ a = epoch) ∧
    (∀ z a, Run (controlProgram P) obs (fresh 0) epoch z a →
      a = epoch ∧ (z = final ∨ TrialPoint P τ u z)) := by
  dsimp only
  let final := canonical (if decide ((composition u).2 % 2 = 1) then .halt1 else .halt0)
  have halt : controlProgram P final = .halt := by
    dsimp only [final]
    split <;> simp [controlProgram, Valid, canonical]
  have certified := stationary_refined_execution P τ u y hu hy start covers regime
    obs epoch response
  have run := refined_run certified
  refine ⟨run, halt, ?_, refined_prefix certified halt⟩
  intro z a other hz
  exact D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.run_halt_unique other run hz halt

private theorem refined_mono {P : Parameters} {obs : Nat → Address → Reply}
    {I J : Control → Nat → Prop} {x y : Control} {a b : Nat}
    (path : RefinedRun P obs I x a y b) (weaken : ∀ z e, I z e → J z e) :
    RefinedRun P obs J x a y b := by
  induction path with
  | refl x a h => exact .refl x a (weaken x a h)
  | read h hop _ ih => exact .read (weaken _ _ h) hop ih
  | update h hop _ ih => exact .update (weaken _ _ h) hop ih

/-- Active polling is available only for a positive historical bound. -/
def rowParameters (h T : Nat) (active : Bool) : Parameters :=
  if active && decide (0 < T) then activeParameters h T else ⟨h, 0, T, 0, false⟩

/-- The common entry depends only on the installed regime and bounds. -/
def rowInitial (T : Nat) (active : Bool) : Control :=
  if active && decide (0 < T) then canonical .poll else fresh 0

/-- The number of genuine Updates is comparison data, never a retained field. -/
def rowUpdates (h T t : Nat) (u : Source) (active : Bool) : Nat :=
  if active && decide (0 < T) then alignmentBudget h T - t - rightClock u else 0

/-- Polling fields are canonical; trial fields belong to the stationary image. -/
def RowPoint (P : Parameters) (τ : Nat) (u : Source) (U : Nat) (z : Control) (a : Nat) : Prop :=
  a ≤ U ∧ ((P.active = true ∧ (z = canonical .poll ∨ z = canonical .update)) ∨
    (a = U ∧ (z = canonical (if decide ((composition u).2 % 2 = 1) then .halt1 else .halt0) ∨
      TrialPoint P τ u z)))

/-- Static, direct and active rows have one common source-independent entry,
and every actual finite prefix satisfies the polling or compressed-trial relation. -/
theorem native_bounded_rows_execution (h T t : Nat) (u : Source)
    (hu : u.length = h) (ht : t ≤ T) (regime : T = 0 ∨ h % 2 = 0) (active : Bool) :
    let P := rowParameters h T active
    let U := rowUpdates h T t u active
    let bit := decide ((composition u).2 % 2 = 1)
    let final := canonical (if bit then .halt1 else .halt0)
    P.start ≤ t + U ∧ t + U ≤ P.start + P.last ∧
    (U = 0 ∨ (0 < U ∧ t + U = alignmentBudget h T - rightClock u)) ∧
    Run (controlProgram P) (NativePollingAlignment.observations (substitution^[t] u))
      (rowInitial T active) 0 final U ∧
    controlProgram P final = .halt ∧
    (∀ z a, Run (controlProgram P) (NativePollingAlignment.observations (substitution^[t] u))
      (rowInitial T active) 0 z a → controlProgram P z = .halt → z = final ∧ a = U) ∧
    (∀ z a, Run (controlProgram P) (NativePollingAlignment.observations (substitution^[t] u))
      (rowInitial T active) 0 z a → RowPoint P (t + U) u U z a) := by
  dsimp only
  let P := rowParameters h T active
  let U := rowUpdates h T t u active
  let obs := NativePollingAlignment.observations (substitution^[t] u)
  let final := canonical (if decide ((composition u).2 % 2 = 1) then .halt1 else .halt0)
  have reached : P.start ≤ t + U ∧ t + U ≤ P.start + P.last ∧
      (U = 0 ∨ (0 < U ∧ t + U = alignmentBudget h T - rightClock u)) ∧
      RefinedRun P obs (RowPoint P (t + U) u U) (rowInitial T active) 0 final U := by
    by_cases flag : (active && decide (0 < T)) = true
    · simp only [P, U, rowParameters, rowUpdates, rowInitial, flag, ite_true]
      let Q := activeParameters h T
      let d := alignmentBudget h T - t - rightClock u
      have aligned := native_one_update_alignment h T t u hu ht
      have lower : Q.start ≤ t + d := aligned.2.2.1
      have upper : t + d ≤ Q.start + Q.last := by
        have b := aligned.2.2.2.2.1
        dsimp only [Q, activeParameters] at lower ⊢
        omega
      have positive : 0 < T := by
        have both : active = true ∧ 0 < T := by simpa using flag
        exact both.2
      have even : h % 2 = 0 := by rcases regime with rfl | even; omega; exact even
      have stationary := stationary_refined_execution Q (t + d) u
        (substitution^[t + d] u) hu rfl lower upper (Or.inl even) obs d (by
          intro p
          change readout p (substitution^[d] (substitution^[t] u)) = _
          rw [← Function.iterate_add_apply, Nat.add_comm d t])
      have tail := refined_mono stationary (J := RowPoint Q (t + d) u d) (by
        intro z a good
        obtain ⟨rfl, good⟩ := good
        exact ⟨le_rfl, Or.inr ⟨rfl, good⟩⟩)
      have clock : rightClock (substitution^[t] u) + d = 2 * Q.pollDepth := by
        rw [right_clock_iterate]
        have pos := aligned.1
        dsimp [d, Q, activeParameters, alignmentBudget] at *
        omega
      have full := one_update_polling Q (substitution^[t] u) rfl
        (RowPoint Q (t + d) u d)
        (by intro a ha; exact ⟨by omega, Or.inl ⟨rfl, Or.inl rfl⟩⟩)
        (by intro a ha; exact ⟨by omega, Or.inl ⟨rfl, Or.inr rfl⟩⟩)
        d 0 (by simpa using clock) final d (by
          simpa only [final, obs, decide_eq_true_eq, Nat.zero_add] using tail)
      exact ⟨lower, upper, Or.inr ⟨aligned.1, aligned.2.1⟩, full⟩
    · simp only [P, U, rowParameters, rowUpdates, rowInitial, flag, Bool.false_eq_true,
        ite_false, Nat.add_zero]
      have ordinary : h % 2 = 0 ∨ t = 0 := by
        rcases regime with zero | even
        · exact Or.inr (by omega)
        · exact Or.inl even
      have stationary := stationary_refined_execution ⟨h, 0, T, 0, false⟩ t u
        (substitution^[t] u) hu rfl (Nat.zero_le t) (by simpa using ht)
        ordinary obs 0 (by intro p; rfl)
      refine ⟨Nat.zero_le t, by simpa using ht, Or.inl trivial, ?_⟩
      exact refined_mono stationary (by
        intro z a good
        obtain ⟨rfl, good⟩ := good
        exact ⟨le_rfl, Or.inr ⟨rfl, good⟩⟩)
  have halt : controlProgram P final = .halt := by
    dsimp [final]
    split <;> simp [controlProgram, Valid, canonical]
  have run := refined_run reached.2.2.2
  refine ⟨reached.1, reached.2.1, reached.2.2.1, run, halt, ?_,
    refined_prefix reached.2.2.2 halt⟩
  intro z a other hz
  exact D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.run_halt_unique other run hz halt

#print axioms reachable_compressed_frontier_and_trial_simulation
#print axioms native_one_update_alignment
#print axioms native_stationary_bounded_execution
#print axioms native_bounded_rows_execution

end D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows
