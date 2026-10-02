/- GID: D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackThreeDefs
   mirror-E: none(waiver:fixed-three-312-stack-sorting-class-definitions)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: The stacks avoiding 312, 31-2 and 3-12 and Zhao's conjecture that they sort alike. -/

import D5.S3.Combinatorics.VincularStack.VincularStackDefs
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackThreeDefs

open D5.S3.Combinatorics.VincularStack.VincularStackDefs (Contains231)

/-! Fixed public statement: Zhao, *Stack-sorting with Stacks Avoiding Vincular Patterns*,
    arXiv:2410.17057v1, §5, Conjecture 5.1.  Stack words are read from top to bottom;
    positions are numbered from 0 in Lean. -/

/-- A stack word contains `312`: `i < j < k` with `s_j < s_k < s_i`; with `adj31` the entries
    playing `3` and `1` are adjacent (`j = i + 1`), with `adj12` the entries playing `1` and `2`
    are adjacent (`k = j + 1`). -/
def Contains312 (adj31 adj12 : Bool) (s : List ℕ) : Prop :=
  ∃ i < s.length, ∃ j < s.length, ∃ k < s.length,
    i < j ∧ j < k ∧ s.getD j 0 < s.getD k 0 ∧ s.getD k 0 < s.getD i 0 ∧
      (adj31 = true → j = i + 1) ∧ (adj12 = true → k = j + 1)

instance (adj31 adj12 : Bool) (s : List ℕ) : Decidable (Contains312 adj31 adj12 s) := by
  unfold Contains312
  infer_instance

/-- Push `x` if the proposed stack avoids the pattern; otherwise pop the top to the output and
    retry.  Returns the popped entries in output order and the new stack (top first). -/
def Push (adj31 adj12 : Bool) (x : ℕ) : List ℕ → List ℕ × List ℕ
  | [] => ([], [x])
  | a :: s =>
    if Contains312 adj31 adj12 (x :: a :: s) then
      let r := Push adj31 adj12 x s
      (a :: r.1, r.2)
    else ([], x :: a :: s)

/-- Process the input from left to right, then pop the remaining stack. -/
def Process (adj31 adj12 : Bool) : List ℕ → List ℕ → List ℕ
  | [], s => s
  | x :: xs, s =>
    let r := Push adj31 adj12 x s
    r.1 ++ Process adj31 adj12 xs r.2

/-- The right-greedy map `SC_σ`: classical `312` is `(false, false)`, `31-2` with the entries
    playing `3` and `1` adjacent is `(true, false)`, and `3-12` with the entries playing `1` and
    `2` adjacent is `(false, true)`. -/
def SC (adj31 adj12 : Bool) (p : List ℕ) : List ℕ := Process adj31 adj12 p []

/-- `Sort_n(SC_σ)`: permutations of `[n]` whose image avoids 231. -/
def sortable (adj31 adj12 : Bool) (n : ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ ¬ Contains231 (SC adj31 adj12 p)}

/-- Conjecture 5.1: for `n ≥ 1` the three sorting classes coincide, and the three maps agree on
    the common class. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    sortable false false n = sortable true false n ∧
    sortable false false n = sortable false true n ∧
    ∀ p ∈ sortable false false n,
      SC false false p = SC true false p ∧ SC false false p = SC false true p

end D5.S3.Combinatorics.VincularStack.VincularStackThreeDefs
