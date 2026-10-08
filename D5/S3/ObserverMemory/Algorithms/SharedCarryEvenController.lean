/- GID: D5/S3/ObserverMemory/Algorithms/SharedCarryEvenController
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/SharedCarryEvenController
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Even-base first-carry acquisition shares two read and wait controls per positive time. -/

import D5.S3.ObserverMemory.Algorithms.ActualControlSlots
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.SharedCarryEvenController

open ActualControlSlots

/-- One initial read, one wait/read pair per color, and all original labels. -/
def State (p P : Nat) :=
  Unit ⊕ (((Fin (P - 1) × Fin 2) × Bool) ⊕ ZMod (p * P))

local notation "Root" => (Sum.inl () : State _ _)
local notation "W(" c ")" => Sum.inr (Sum.inl (c, false))
local notation "R(" c ")" => Sum.inr (Sum.inl (c, true))
local notation "H(" x ")" => Sum.inr (Sum.inr x)

/-- The time index is t-1; the second component is the initial digit's parity. -/
def color {p P : Nat} (b : Fin p) (t : Fin (P - 1)) : Fin (P - 1) × Fin 2 :=
  (t, ⟨b.val % 2, Nat.mod_lt _ (by decide)⟩)

/-- A total table: each row uses only its own color, index, and supplied digit. -/
def table (p P : Nat) : Controller p P (State p P) where
  initial := Root
  action := fun q => match q with
    | .inl _ => .read
    | .inr (.inl (_, false)) => .wait
    | .inr (.inl (_, true)) => .read
    | .inr (.inr _) => .halt
  waitNext := fun q => match q with
    | .inr (.inl (c, false)) => R(c)
    | _ => q
  readNext := fun q d => match q with
    | .inl _ =>
        if h : 1 < P then W(color d ⟨0, by omega⟩)
        else H((d.val : Nat))
    | .inr (.inl (c, true)) =>
        if d.val % 2 = c.2.val then
          if h : c.1.val + 2 < P then W(color d ⟨c.1.val + 1, by omega⟩)
          else H((d.val * P : Nat))
        else H(((if d.val = 0 then p - 1 else d.val - 1) * P +
          (P - (c.1.val + 1)) : Nat))
    | _ => q
  output := fun q => match q with
    | .inr (.inr x) => x
    | _ => 0

/-- The number of waits before the first carry, capped at the last scan. -/
def waits {p P : Nat} (x : ZMod (p * P)) : Nat :=
  if x.val % P = 0 then P - 1 else P - x.val % P

end D5.S3.ObserverMemory.Algorithms.SharedCarryEvenController
