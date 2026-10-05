/- GID: D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RegularInduced/DysonMcKayDefs
   mirror-E: none(waiver:dyson-mckay-optimality-statement-definition)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Basic, mathlib/module/Mathlib.Data.Finset.Card, mathlib/module/Mathlib.Data.Nat.Prime.Defs]
   utility: none
   digest: Dyson and McKay's optimality assertion for cycle-clique unions without induced regular subgraphs of prime order. -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RegularInduced.DysonMcKayDefs

/-! Fixed public statement: P. W. Dyson and B. D. McKay, *Ramsey numbers for regular induced
    subgraphs*, arXiv:2604.08215v3, Section 4.  For `r ≥ 3` and `s ≥ 1` the lexicographic product
    `C_r[K_s]` replaces each vertex of the cycle `C_r` by a clique `K_s`, two bags being completely
    joined when their cycle vertices are adjacent (`C_3[K_s]` is the clique `K_{3s}`).  Theorem 4.2
    gives, for each prime `p ≥ 5`, a disjoint union `G_p` of such products with no induced regular
    subgraph on `p` vertices, of order `9(p−1)²/8` for `p ≡ 1, 5 (mod 12)`, `(p−1)(9p−7)/8` for
    `p ≡ 7 (mod 12)` and `(p−1)(9p−11)/8` for `p ≡ 11 (mod 12)`.  The authors state: "Although we
    won't prove it, we believe the graphs in Theorem 4.2 are optimal for p ≥ 13 within the class
    of disjoint unions of lexicographic products of cycles and cliques."  A union is given by the
    list of its component parameters `(r, s)`. -/

/-- Vertices of the disjoint union of the products `C_r[K_s]` listed in `comps`. -/
abbrev Vert (comps : List (ℕ × ℕ)) : Type :=
  Σ i : Fin comps.length, Fin (comps.get i).1 × Fin (comps.get i).2

/-- Two cycle positions modulo `r` are equal or adjacent. -/
def CycleClose (r a b : ℕ) : Prop :=
  a = b ∨ (a + 1) % r = b ∨ (b + 1) % r = a

/-- The disjoint union of the lexicographic products `C_r[K_s]` for `(r, s) ∈ comps`: distinct
    vertices are adjacent when they lie in the same component and in equal or adjacent bags. -/
def unionGraph (comps : List (ℕ × ℕ)) : SimpleGraph (Vert comps) :=
  SimpleGraph.fromRel fun u v =>
    ∃ _ : u.1 = v.1, CycleClose (comps.get u.1).1 u.2.1.val v.2.1.val

open Classical in
/-- The union has an induced regular subgraph on exactly `p` vertices (of some degree): a vertex
    set of size `p` in which every vertex has the same number `d` of neighbours. -/
def HasRegularInduced (comps : List (ℕ × ℕ)) (p : ℕ) : Prop :=
  ∃ S : Finset (Vert comps), S.card = p ∧ ∃ d : ℕ,
    ∀ v ∈ S, (S.filter fun w => (unionGraph comps).Adj v w).card = d

/-- Admissible unions: every component is `C_r[K_s]` with `r ≥ 3` and `s ≥ 1`. -/
def Admissible (comps : List (ℕ × ℕ)) : Prop :=
  ∀ c ∈ comps, 3 ≤ c.1 ∧ 1 ≤ c.2

/-- The number of vertices of the union. -/
def order (comps : List (ℕ × ℕ)) : ℕ :=
  (comps.map fun c => c.1 * c.2).sum

/-- The order of the Theorem 4.2 graph `G_p`. -/
def bound (p : ℕ) : ℕ :=
  if p % 12 = 1 ∨ p % 12 = 5 then 9 * (p - 1) ^ 2 / 8
  else if p % 12 = 7 then (p - 1) * (9 * p - 7) / 8
  else (p - 1) * (9 * p - 11) / 8

/-- The optimality assertion for every prime `p ≥ 13`: every admissible union without an induced
    regular subgraph on `p` vertices has at most `bound p` vertices, and the bound is attained. -/
def claim : Prop :=
  ∀ p : ℕ, p.Prime → 13 ≤ p →
    (∀ comps : List (ℕ × ℕ), Admissible comps → ¬ HasRegularInduced comps p →
      order comps ≤ bound p) ∧
    ∃ comps : List (ℕ × ℕ), Admissible comps ∧ ¬ HasRegularInduced comps p ∧
      order comps = bound p

end D5.S3.Combinatorics.RegularInduced.DysonMcKayDefs
