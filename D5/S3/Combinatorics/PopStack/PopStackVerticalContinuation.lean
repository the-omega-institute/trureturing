/- GID: D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackVerticalContinuation
   mirror-E: none(waiver:augmented-vertical-continuation-bijection)
   anchors: []
   utility: none
   digest: Vertical continuation operations include the exceptional parallel and odd families. -/

import D5.S3.Combinatorics.PopStack.PopStackMaximumInsertion
import D5.S3.Combinatorics.PopStack.PopStackMaximumDeletion
import D5.S3.Combinatorics.PopStack.PopStackContinuation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackVerticalContinuation

open PopStackDefs PopStackParallel PopStackExtra PopStackContinuation
open PopStackMaximumShape PopStackMaximumIntervals
open PopStackMaximumInsertion PopStackMaximumDeletion

def augmented (size : ℕ) : Set (List ℕ) :=
  simples size ∪ if size % 2 = 1 ∧ 3 ≤ size then {E (size / 2)} else ∅

noncomputable def V (permutation : List ℕ) : List ℕ :=
  if permutation = P (permutation.length / 2) then E (permutation.length / 2)
  else if permutation = E (permutation.length / 2) then
    let rank := (permutation.length + 3) / 2
    permutation.map (fun entry => if rank ≤ entry then entry + 1 else entry) ++ [rank]
  else if permutation.getD 1 0 < permutation.length then W permutation
  else
    let cut := permutation.idxOf 1
    let rank := if cut % 2 = 0 then permutation.getD 0 0 - cut / 2 + 1
      else permutation.length - (cut - 1) / 2 + 1
    (permutation.map (fun entry => if rank ≤ entry then entry + 1 else entry)).insertIdx
      cut rank

noncomputable def undoV (permutation : List ℕ) : List ℕ :=
  if permutation = E (permutation.length / 2) then P (permutation.length / 2)
  else if permutation = P (permutation.length / 2) then E (permutation.length / 2 - 1)
  else if permutation.getD 1 0 < permutation.length then
    (permutation.drop 1).map
      (fun entry => if permutation.getD 0 0 < entry then entry - 1 else entry)
  else
    let cut := permutation.idxOf 1 - 1
    let rank := permutation.getD cut 0
    (permutation.eraseIdx cut).map (fun entry => if rank < entry then entry - 1 else entry)

end D5.S3.Combinatorics.PopStack.PopStackVerticalContinuation
