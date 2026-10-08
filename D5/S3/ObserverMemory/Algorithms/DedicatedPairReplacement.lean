/- GID: D5/S3/ObserverMemory/Algorithms/DedicatedPairReplacement
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/DedicatedPairReplacement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two physical reads replace disjoint adjacent-pair suffixes by one shared table. -/

import D5.S3.Observer.Budget.FinitePositiveIntervalControl
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.DedicatedPairReplacement

open ActualControlSlots (Action Controller digit)
open D5.S3.Observer.Budget.FinitePositiveIntervalControl (Follows)

variable {p P d : Nat} {E : Type}

local notation "Old" => E ⊕ (Fin p × Fin (d + 1))
local notation "Internal" => Fin d ⊕ (Fin p × Fin 2)
local notation "New" => E ⊕ Internal

/-- The common countdown ends in its zero reading state. -/
def entry (hd : 0 < d) : Internal := .inl ⟨d - 1, by omega⟩

/-- All removed states are redirected to the same entry. Only old entries
are encountered on the affected exterior paths. -/
def redirect (hd : 0 < d) : Old → New
  | .inl e => .inl e
  | .inr _ => .inr (entry hd)

/-- A successor digit is cyclic, including the last source block. -/
private def nextDigit (hp : 2 ≤ p) (b : Fin p) : Fin p :=
  ⟨(b.val + 1) % p, Nat.mod_lt _ (by omega)⟩

/-- The old internal carrier is p disjoint countdowns. Zero is the final
read, and every positive index is one charged unit wait. -/
structure Dedicated (hp : 2 ≤ p) (C : Controller p P Old)
    (labels : Fin p × Fin 2 → E) : Prop where
  waiting : ∀ b i, 0 < i.val → C.action (.inr (b, i)) = .wait
  advance : ∀ b i (hi : 0 < i.val),
    C.waitNext (.inr (b, i)) = .inr (b, ⟨i.val - 1, by omega⟩)
  reading : ∀ b, C.action (.inr (b, 0)) = .read
  lower : ∀ b, C.readNext (.inr (b, 0)) b = .inl (labels (b, 0))
  upper : ∀ b, C.readNext (.inr (b, 0)) (nextDigit hp b) = .inl (labels (b, 1))
  terminal : ∀ b e, C.action (.inl (labels (b, e))) = .halt

/-- Exterior rows and their outputs are retained. The shared chain stores
no branch; its physical read chooses a charged branch wait and branch read.
Unused digit rows go to a pre-existing terminal label. -/
def table (hp : 2 ≤ p) (hd : 0 < d) (C : Controller p P Old)
    (labels : Fin p × Fin 2 → E) : Controller p P New where
  initial := redirect hd C.initial
  action
    | .inl e => C.action (.inl e)
    | .inr (.inl i) => if i.val = 0 then .read else .wait
    | .inr (.inr (_, e)) => if e = 0 then .wait else .read
  waitNext
    | .inl e => redirect hd (C.waitNext (.inl e))
    | .inr (.inl i) => .inr (.inl ⟨i.val - 1, by omega⟩)
    | .inr (.inr (b, _)) => .inr (.inr (b, 1))
  readNext
    | .inl e, b => redirect hd (C.readNext (.inl e) b)
    | .inr (.inl _), b => .inr (.inr (b, 0))
    | .inr (.inr (b, _)), a =>
        .inl (labels (b, if a = b then 0 else if a = nextDigit hp b then 1 else 0))
  output
    | .inl e => C.output (.inl e)
    | .inr _ => C.output (.inl (labels (⟨0, by omega⟩, 0)))

end D5.S3.ObserverMemory.Algorithms.DedicatedPairReplacement
