/- GID: D5/S3/Arith/FibonacciAtomic/Scale38LeafFrontierResponse
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Complete labelled frontiers and all target-leaf responses in nested compensation families. -/

import D5.S3.Arith.FibonacciAtomic.Scale38NestedCompensation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale38LeafFrontierResponse

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualImageSevenLeafSeparation (A C E leafLabel)
open FourExitRawEndpointSpectrum (comb comb_slot_readout comb_tail_readout)
open Scale38NestedCompensation (family)

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)
local notation "B" => FourExitRawEndpointSpectrum.B
local notation "H" => fun r : Nat => comb r (fun _ => A) C
local notation "G" => fun k : Nat => fun j : Fin k => comb k (fun l => ite (l = j) B A) C
local notation "label" => fun b : Bool => Bool.rec Reply.beta Reply.alpha b

/-- Actual leaf addresses paired with their actual Boolean labels. -/
def labelledFrontier (T : Source) : Set (Address × Bool) :=
  {p | leafLabel T p.1 = some p.2}

/-- Prefixing an entire labelled block preserves each leaf label. -/
def prefixed (w : Address) (F : Set (Address × Bool)) : Set (Address × Bool) :=
  (fun p => (w ++ p.1, p.2)) '' F

/-- A comb has one block at each left slot and one block at its right tail. -/
def combBlock (n : Nat) (f : Fin n → Source) (q : Source) (i : Fin (n+1)) :
    Set (Address × Bool) :=
  if h : i.val < n then prefixed (List.replicate i.val true ++ [false])
    (labelledFrontier (f ⟨i.val,h⟩))
  else prefixed (List.replicate n true) (labelledFrontier q)

/-- The thirteen types of target-leaf groups, with zero-based slot indices. -/
inductive LeafRow (k : Nat)
  | pSlot (t : Fin k)
  | pTail
  | pOuter (right : Bool)
  | pInner
  | xSlot (j t : Fin k) (different : t ≠ j)
  | xExceptional (j : Fin k)
  | xTail (j : Fin k)
  | xRight (j : Fin k)
  | ySlot (i : Fin k) (t : Fin (i.val+1))
  | yLeftTail (i : Fin k)
  | yRightSlot (i : Fin k) (h : Fin (k-i.val+1))
  | yRightTail (i : Fin k)
  | yRightA (i : Fin k)

/-- The family member whose leaves constitute this row. -/
def LeafRow.target {k : Nat} : LeafRow k → Index k
  | .pSlot _ | .pTail | .pOuter _ | .pInner => .inl ()
  | .xSlot j _ _ | .xExceptional j | .xTail j | .xRight j => .inr (.inl j)
  | .ySlot i _ | .yLeftTail i | .yRightSlot i _ | .yRightTail i | .yRightA i =>
    .inr (.inr i)

/-- The complete labelled block in each row of the response table. -/
def LeafRow.block {k : Nat} : LeafRow k → Set (Address × Bool)
  | .pSlot t => prefixed (false :: (List.replicate t.val true ++ [false])) (labelledFrontier A)
  | .pTail => prefixed (false :: List.replicate k true) (labelledFrontier C)
  | .pOuter right => prefixed (if right then [true,true] else [true,false,false])
      (labelledFrontier A)
  | .pInner => prefixed [true,false,true] (labelledFrontier E)
  | .xSlot _ t _ => prefixed (false :: (List.replicate t.val true ++ [false])) (labelledFrontier A)
  | .xExceptional j => prefixed (false :: (List.replicate j.val true ++ [false])) (labelledFrontier B)
  | .xTail _ => prefixed (false :: List.replicate k true) (labelledFrontier C)
  | .xRight _ => prefixed [true] (labelledFrontier A)
  | .ySlot _ t => prefixed (false :: (List.replicate t.val true ++ [false])) (labelledFrontier A)
  | .yLeftTail i => prefixed (false :: List.replicate (i.val+1) true) (labelledFrontier E)
  | .yRightSlot _ h => prefixed (true :: false :: (List.replicate h.val true ++ [false]))
      (labelledFrontier A)
  | .yRightTail i => prefixed (true :: false :: List.replicate (k-i.val+1) true)
      (labelledFrontier E)
  | .yRightA _ => prefixed [true,true] (labelledFrontier A)

/-- The table's branch, absent, and matching replies for every competitor. -/
def LeafRow.reply {k : Nat} (r : LeafRow k) (U : Index k) (b : Bool) : Reply :=
  match r, U with
  | .pSlot t, .inr (.inl j) | .xSlot _ t _, .inr (.inl j)
    | .ySlot _ t, .inr (.inl j) => if j.val = t.val then .branch else label b
  | .pSlot t, .inr (.inr i) | .xSlot _ t _, .inr (.inr i)
    | .ySlot _ t, .inr (.inr i) => if i.val < t.val then .absent else label b
  | .pTail, .inr (.inr _) | .xTail _, .inr (.inr _) => .absent
  | .pOuter _, .inr (.inl _) => .absent
  | .pInner, .inr (.inl _) => .absent
  | .pInner, .inr (.inr _) => .branch
  | .xExceptional _, _ => .absent
  | .xRight _, .inl _ | .xRight _, .inr (.inr _) => .branch
  | .yLeftTail _, .inl _ | .yLeftTail _, .inr (.inl _) => .branch
  | .yLeftTail i, .inr (.inr j) =>
    if i.val < j.val then .branch else if j.val < i.val then .absent else label b
  | .yRightSlot _ h, .inl _ => if 0 < h.val then .absent else label b
  | .yRightSlot _ _, .inr (.inl _) => .absent
  | .yRightSlot _ h, .inr (.inr j) => if k-j.val < h.val then .absent else label b
  | .yRightTail _, .inl _ | .yRightTail _, .inr (.inl _) => .absent
  | .yRightTail i, .inr (.inr j) =>
    if j.val < i.val then .branch else if i.val < j.val then .absent else label b
  | .yRightA _, .inr (.inl _) => .absent
  | _, _ => label b

end D5.S3.Arith.FibonacciAtomic.Scale38LeafFrontierResponse
