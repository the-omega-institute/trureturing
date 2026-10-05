/- GID: D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A depth-free carry-slot machine preserves fair-tape labels and charges. -/

import D5.S3.Arith.FibonacciAtomic.CarryGraphCriticalAttainment
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CarryGraphFiniteSampler

open scoped BigOperators ENNReal
open CarryGraphEmbedding CarryGraphCriticalAttainment MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)

local notation "S" => (fun m : ℕ => {s : State // IsState m s})
local notation "A" => (fun (m : ℕ) (s : State) => {a : Action // Legal m s a})
set_option quotPrecheck false in
local notation "P" => (fun m : ℕ => (s : S m) → A m s.val)
set_option quotPrecheck false in
local notation "labels" => (fun (m : ℕ) (s : State) (a : Action) =>
  Finset.sort (CarryGraphRealization.labelSet m ⟨fun _ => s, fun _ => a⟩ 0)
    (fun i j => i ≤ j))

/-- An active control stores a legal carry state and a slot strictly below its width. -/
def Active (m : ℕ) := {x : S m × ℕ // (x.2 : ℤ) < x.1.val.r}

/-- The initial control has width one, all labels equal, and slot zero. -/
def initial (m : ℕ) (hm : 2 ≤ m) : Sum (Active m) (Fin m) :=
  .inl ⟨(⟨root m, by dsimp [IsState, root]; omega⟩, 0), by simp [root]⟩

/-- Read one bit while active. The check on the continuing slot makes the function
 total; the simulation proves it always succeeds on the continuing branch. -/
def step (m : ℕ) (f : P m) (u : Bool) :
    Sum (Active m) (Fin m) → Sum (Active m) (Fin m)
  | .inr i => .inr i
  | .inl x =>
    let s := x.val.1
    let a := f s
    let L := labels m s.val a.val
    let z := 2 * x.val.2 + u.toNat
    if hz : z < L.length then .inr L[z]
    else
      let ns : S m := ⟨successor s.val a.val, a.property.2.2⟩
      if hj : ((z - L.length : ℕ) : ℤ) < ns.val.r then
        .inl ⟨(ns, z - L.length), hj⟩
      else .inl x

/-- Execution records the control and a separate invoice; the invoice is never
 supplied to the control transition. Returned controls consume no further bits. -/
def execute (m : ℕ) (f : P m) (start : Sum (Active m) (Fin m)) (tape : Tape) :
    ℕ → Sum (Active m) (Fin m) × ℕ
  | 0 => (start, 0)
  | d + 1 =>
    let prev := execute m f start tape d
    (step m f (tape d) prev.1, prev.2 + if prev.1.isLeft then 1 else 0)

/-- First output together with the invoice at that output, or no finite output. -/
noncomputable def sample (m : ℕ) (f : P m) (start : Sum (Active m) (Fin m))
    (tape : Tape) : Option (Fin m × ℕ) := by
  classical
  exact if h : ∃ d, (execute m f start tape d).1.isRight then
    ((execute m f start tape (Nat.find h)).1.getRight?).map
      (fun i => (i, (execute m f start tape (Nat.find h)).2))
  else none

/-- All active steps are charged, including every step on a divergent tape. -/
noncomputable def bill (m : ℕ) (f : P m) (start : Sum (Active m) (Fin m))
    (tape : Tape) : ℝ≥0∞ :=
  ∑' d : ℕ, if (execute m f start tape d).1.isLeft then 1 else 0

end D5.S3.Arith.FibonacciAtomic.CarryGraphFiniteSampler
