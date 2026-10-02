/- GID: D5/S3/Combinatorics/PopStack/PopStackDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackDefs
   mirror-E: none(waiver:fixed-pop-stack-simple-permutation-definitions)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Simple permutations in the two-parallel-pop-stack-with-bypass class and their count. -/

import D5.S3.Combinatorics.ArrowWilfDefs
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackDefs

/-! Fixed public statement: Cioni–Ferrari–Smith, arXiv:2503.08285v1, §9.2 conjecture on simple
    permutations sortable by two pop stacks in parallel with bypass.  Permutations of `[n]` are
    lists in one-line notation; positions are numbered from 0 in Lean. -/

/-- Classical containment of the pattern `σ` (a permutation of `[σ.length]`) in `p`. -/
def Occurs (σ p : List ℕ) : Prop := ArrowWilfDefs.Contains σ [] σ.length p

/-- The basis of the sortable class (§9, Proposition 8.2 of the source). -/
def basis : List (List ℕ) :=
  [[2, 3, 4, 1], [2, 5, 3, 1, 4], [4, 2, 5, 1, 3], [4, 2, 5, 3, 1], [4, 5, 2, 1, 3],
    [4, 5, 2, 3, 1], [5, 2, 3, 1, 4], [6, 4, 2, 1, 3, 5], [6, 4, 2, 1, 5, 3]]

/-- Membership in `C = Av(2341, 25314, 42513, 42531, 45213, 45231, 52314, 642135, 642153)`. -/
def InC (p : List ℕ) : Prop := ∀ σ ∈ basis, ¬ Occurs σ p

/-- `p` is simple: no block of `len` consecutive positions with `2 ≤ len < p.length` carries a set
    of `len` consecutive values. -/
def IsSimple (p : List ℕ) : Prop :=
  ∀ i len m, 2 ≤ len → len < p.length → i + len ≤ p.length →
    ¬ ((p.drop i).take len).Perm (List.range' m len)

/-- Simple permutations of `[n]` in `C`. -/
def simples (n : ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ InC p ∧ IsSimple p}

/-- The §9.2 conjecture: `a_0 = a_1 = 1`, `a_2 = 2`, and for `n ≥ 3`,
    `a_n = F_{2n-5} - 1` for odd `n` and `a_n = F_{2n-5}` for even `n`. -/
def claim : Prop :=
  (simples 0).ncard = 1 ∧ (simples 1).ncard = 1 ∧ (simples 2).ncard = 2 ∧
    ∀ n : ℕ, 3 ≤ n → (simples n).ncard = Nat.fib (2 * n - 5) - n % 2

end D5.S3.Combinatorics.PopStack.PopStackDefs
