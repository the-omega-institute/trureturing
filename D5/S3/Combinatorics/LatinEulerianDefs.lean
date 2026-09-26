/- GID: D5/S3/Combinatorics/LatinEulerianDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatinEulerianDefs
   mirror-E: none(waiver:fixed-public-formalization-of-Latin-Eulerian-remark)
   anchors: [mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: An interior multiple of the order is specified as a Latin-square column-ascent total. -/

import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinEulerianMultiples

/-! Fixed public statement: Mirzavaziri–Yaqubi, "Latin Eulerian Numbers", arXiv:2609.25100v1, Remark 4.16(i):
    every multiple of `n` strictly between `n` and `(n − 1)^2 − 1 = n(n − 2)` is the total column-ascent count of some
    order-`n` Latin square. Symbols are `Fin n` (order-isomorphic to the paper's `[n]`; ascents depend only on order). -/

/-- An order-`n` Latin square: every row and every column is a permutation of the symbols. -/
def IsLatin (n : ℕ) (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ (∀ c, Function.Bijective (fun i => L i c))

/-- `k_c(L)`: the number of ascents of column `c` read top to bottom, i.e. rows `j` with `L j c < L (j+1) c`. -/
def colAscents (n : ℕ) (L : Fin n → Fin n → Fin n) (c : Fin n) : ℕ :=
  ((Finset.range n).filter (fun j => ∃ (h : j + 1 < n), L ⟨j, by omega⟩ c < L ⟨j + 1, h⟩ c)).card

/-- `Σ(L) = Σ_c k_c(L)`. -/
def totalAscents (n : ℕ) (L : Fin n → Fin n → Fin n) : ℕ := ∑ c, colAscents n L c

/-- Remark 4.16(i): for `n ≥ 5` and `2 ≤ k ≤ n − 3`, some Latin square has `Σ(L) = k n`. -/
def claim : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ k : ℕ, 2 ≤ k → k ≤ n - 3 →
    ∃ L : Fin n → Fin n → Fin n, IsLatin n L ∧ totalAscents n L = k * n

end D5.S3.Combinatorics.LatinEulerianMultiples
