/- GID: D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LevelSequence/LevelSequenceDefs
   mirror-E: none(waiver:fixed-level-sequence-101-102-avoidance-definitions)
   anchors: [mathlib/module/Mathlib.Data.Set.Card, mathlib/module/Mathlib.Combinatorics.Enumerative.Catalan.Basic]
   utility: none
   digest: Level sequences avoiding 101 and 102 and Mansour's Catalan enumeration problem. -/

import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LevelSequence.LevelSequenceDefs

/-! Fixed public statement: Mansour, *Wilf Classes for Level Sequences Avoiding Patterns of
    Length Three*, Mathematics 14(11), 1983 (2026), §4, Problem 1:
    `F_{101,102}(x) = (1 - √(1 - 4x))/(2x) - 1`.  Positions are numbered from 0 in Lean. -/

/-- Number of levels: positions `j` with `e_j = e_{j+1}`. -/
def lev (e : List ℕ) : ℕ := ((e.zip e.tail).filter fun q => q.1 = q.2).length

/-- Level sequence: `e_0 = 0` and `e_i ≤ 1 + lev (e_0 ⋯ e_{i-1})` for `i ≥ 1`. -/
def IsLevel (e : List ℕ) : Prop :=
  ∀ i < e.length, e.getD i 0 ≤ if i = 0 then 0 else 1 + lev (e.take i)

/-- `e` contains the pattern 101: `i < j < k` with `e_j < e_i = e_k`. -/
def Contains101 (e : List ℕ) : Prop :=
  ∃ i j k, i < j ∧ j < k ∧ k < e.length ∧
    e.getD j 0 < e.getD i 0 ∧ e.getD k 0 = e.getD i 0

/-- `e` contains the pattern 102: `i < j < k` with `e_j < e_i < e_k`. -/
def Contains102 (e : List ℕ) : Prop :=
  ∃ i j k, i < j ∧ j < k ∧ k < e.length ∧
    e.getD j 0 < e.getD i 0 ∧ e.getD i 0 < e.getD k 0

/-- `LS_n(101, 102)`. -/
def avoiders (n : ℕ) : Set (List ℕ) :=
  {e | e.length = n ∧ IsLevel e ∧ ¬ Contains101 e ∧ ¬ Contains102 e}

/-- Problem 1: `|LS_n(101, 102)| = C_n` for every `n ≥ 1`. -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n → (avoiders n).ncard = catalan n

end D5.S3.Combinatorics.LevelSequence.LevelSequenceDefs
