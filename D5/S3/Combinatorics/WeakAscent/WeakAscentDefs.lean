/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentDefs
   mirror-E: none(waiver:fixed-weak-ascent-210-avoidance-definitions)
   anchors: [mathlib/module/Mathlib.Data.Set.Card, mathlib/module/Mathlib.Data.List.GetD]
   utility: none
   digest: 210-avoiding weak ascent sequences and 2-41-3-avoiding permutations. -/

import Mathlib.Data.Set.Card
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentDefs

/-! Fixed public statement: Bényi–Mansour–Ramírez, arXiv:2309.06518v4 (DMTCS 26:1, 2024), §3,
    Conjecture 3.1: the 210-avoiding weak ascent sequences are counted by A117106, which enumerates
    permutations avoiding the vincular pattern 2-41-3.  Positions are numbered from 0 in Lean. -/

/-- Number of weak ascents: positions `j` with `e_j ≤ e_{j+1}`. -/
def wasc (e : List ℕ) : ℕ := ((e.zip e.tail).filter fun q => q.1 ≤ q.2).length

/-- Weak ascent sequence: `e_0 = 0` and `e_i ≤ 1 + wasc (e_0 ⋯ e_{i-1})` for `i ≥ 1`. -/
def IsWeakAscent (e : List ℕ) : Prop :=
  ∀ i < e.length, e.getD i 0 ≤ if i = 0 then 0 else 1 + wasc (e.take i)

/-- `e` contains the classical pattern 210. -/
def Contains210 (e : List ℕ) : Prop :=
  ∃ i j k, i < j ∧ j < k ∧ k < e.length ∧
    e.getD k 0 < e.getD j 0 ∧ e.getD j 0 < e.getD i 0

/-- `p` contains the vincular pattern 2-41-3: `i < j`, `j + 1 < k`, `p_{j+1} < p_i < p_k < p_j`. -/
def ContainsV2413 (p : List ℕ) : Prop :=
  ∃ i j k, i < j ∧ j + 1 < k ∧ k < p.length ∧
    p.getD (j + 1) 0 < p.getD i 0 ∧ p.getD i 0 < p.getD k 0 ∧ p.getD k 0 < p.getD j 0

/-- `W_n(210)`. -/
def weakAvoiders (n : ℕ) : Set (List ℕ) :=
  {e | e.length = n ∧ IsWeakAscent e ∧ ¬ Contains210 e}

/-- Permutations of `[n]` avoiding 2-41-3. -/
def permAvoiders (n : ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ ¬ ContainsV2413 p}

/-- Conjecture 3.1: `|W_n(210)| = |S_n(2-41-3)|` for every `n`. -/
def claim : Prop := ∀ n : ℕ, (weakAvoiders n).ncard = (permAvoiders n).ncard

end D5.S3.Combinatorics.WeakAscent.WeakAscentDefs
