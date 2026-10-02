/- GID: D5/S3/Combinatorics/VincularStack/VincularStackDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackDefs
   mirror-E: none(waiver:fixed-vincular-stack-sorting-class-definitions)
   anchors: [mathlib/module/Mathlib.Data.Set.Card, mathlib/module/Mathlib.Combinatorics.Enumerative.Schroder]
   utility: none
   digest: Zhao's Schröder enumeration of the sorting class of the stack avoiding 23-1. -/

import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Enumerative.Schroder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackDefs

/-! Fixed public statement: Zhao, *Stack-sorting with Stacks Avoiding Vincular Patterns*,
    arXiv:2410.17057v1, §3.2, Conjecture 3.30: `|Sort_n(SC_{23̲1})| = S_{n-1}`.  Stack words are
    read from top to bottom; positions are numbered from 0 in Lean. -/

/-- A stack word contains the vincular pattern `23̲-1`: adjacent `i, i + 1` with
    `s_i < s_{i+1}`, and a later `k > i + 1` with `s_k < s_i`. -/
def ContainsV (s : List ℕ) : Prop :=
  ∃ i < s.length, ∃ k < s.length,
    i + 1 < k ∧ s.getD i 0 < s.getD (i + 1) 0 ∧ s.getD k 0 < s.getD i 0

instance (s : List ℕ) : Decidable (ContainsV s) := by
  unfold ContainsV
  infer_instance

/-- Push `x` if the proposed stack avoids the pattern; otherwise pop the top to the output and
    retry.  Returns the popped entries in output order and the new stack (top first). -/
def Push (x : ℕ) : List ℕ → List ℕ × List ℕ
  | [] => ([], [x])
  | a :: s =>
    if ContainsV (x :: a :: s) then
      let r := Push x s
      (a :: r.1, r.2)
    else ([], x :: a :: s)

/-- Process the input from left to right, then pop the remaining stack. -/
def Process : List ℕ → List ℕ → List ℕ
  | [], s => s
  | x :: xs, s =>
    let r := Push x s
    r.1 ++ Process xs r.2

/-- Zhao's right-greedy map `SC_{23̲1}`. -/
def SC (p : List ℕ) : List ℕ := Process p []

/-- `w` contains the classical pattern 231. -/
def Contains231 (w : List ℕ) : Prop :=
  ∃ i j k, i < j ∧ j < k ∧ k < w.length ∧
    w.getD k 0 < w.getD i 0 ∧ w.getD i 0 < w.getD j 0

/-- `Sort_n(SC_{23̲1})`: permutations of `[n]` whose image avoids 231. -/
def sortable (n : ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ ¬ Contains231 (SC p)}

/-- Conjecture 3.30: `|Sort_n(SC_{23̲1})| = S_{n-1}` (large Schröder numbers) for `n ≥ 1`. -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n → (sortable n).ncard = Nat.largeSchroder (n - 1)

end D5.S3.Combinatorics.VincularStack.VincularStackDefs
