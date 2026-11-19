/- GID: D5/S0/Diagonal/RecursivePageTable
   generality: G
   mirror-B: D5/B/S0/Diagonal/RecursivePageTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite recursive page walk returns ordinary data, exposes a leaf through a self-map slot, and closes at the root on every repeated self-map index. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Diagonal.RecursivePageTable

universe u

variable {Address : Type u} {N : Nat}

/- A page walk consumes one table index at each step. -/
def pageWalk (lookup : Address -> Fin N -> Address) : Address -> List (Fin N) -> Address
  | address, [] => address
  | address, index :: rest => pageWalk lookup (lookup address index) rest

/- A self-map slot gives the three finite dereference patterns used by the
   recursive page-table model: ordinary data, leaf introspection, and root
   closure at any repeated self-map depth. -/
theorem recursive_page_table_walk
    (lookup : Address -> Fin N -> Address)
    (root leaf data : Address)
    (selfSlot i j : Fin N)
    (hself : lookup root selfSlot = root)
    (hroot : lookup root i = leaf)
    (hleaf : lookup leaf j = data) :
    pageWalk lookup root [i, j] = data /\
      pageWalk lookup root [selfSlot, i] = leaf /\
      forall depth : Nat,
        pageWalk lookup root (List.replicate depth selfSlot) = root := by
  constructor
  · simp [pageWalk, hroot, hleaf]
  constructor
  · simp [pageWalk, hself, hroot]
  · intro depth
    induction depth with
    | zero => rfl
    | succ depth ih =>
        rw [List.replicate_succ]
        simp [pageWalk, hself, ih]

end D5.S0.Diagonal.RecursivePageTable
