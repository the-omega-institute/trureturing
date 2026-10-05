/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleDefs
   mirror-E: none(waiver:propp-problem-thirty-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Finite.Prod, mathlib/module/Mathlib.Data.Fintype.Card]
   utility: none
   digest: Blum's exact two-adic valuation clause of Propp's Problem 30 for the isosceles right triangle graph with extra edges. -/

import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleDefs

/-! Fixed public statement: J. Propp, *Enumeration of Matchings: Problems and Progress*, MSRI
    Publications 38 (1999), arXiv:math/9904150v2, Problem 30 (conjectured by Matt Blum): "Show
    that for the isosceles right triangle graph with extra edges, the number of matchings is always a
    multiple of 3. Furthermore, show that the exact power of 2 dividing the number of matchings is
    2^{n/4} when n is 0 modulo 4, and 2^0 (= 1) when n is 3 modulo 4."  A. Dunkelberg,
    *One and Seven-Eighths Divisibility Problems of Propp*, arXiv:2609.38493v1, proves every part
    except that no power of 2 above 2^{n/4} divides the count when n ≡ 0 (mod 4) (Remark 1).

    The graph `T n` (Propp's Figure 14, Dunkelberg's Figures 1 and 3) has the vertices `(r, x)`
    with `0 ≤ r < n`, `r ≤ x ≤ 2(n − 1) − r` and `x ≡ r (mod 2)`: row `r` holds `n − r` vertices,
    so each side of the triangle has `n` vertices.  Its edges join `(r, x)` to `(r + 1, x ± 1)`,
    and, for even `r`, `(r, x)` to `(r, x + 2)` and to `(r + 2, x)`.  A perfect matching is a
    fixed-point-free involution `σ` with every `v` adjacent to `σ v`. -/

/-- Vertices of `T n`: a row `r < n` and a position `x < 2n` with `r ≤ x`, `x + r ≤ 2(n − 1)` and
    `x ≡ r (mod 2)`. -/
abbrev Vertex (n : ℕ) : Type :=
  { p : Fin n × Fin (2 * n) //
    (p.1 : ℕ) ≤ p.2 ∧ (p.2 : ℕ) + p.1 ≤ 2 * (n - 1) ∧ (p.1 : ℕ) % 2 = (p.2 : ℕ) % 2 }

/-- The directed generating steps of the edge set. -/
def Step {n : ℕ} (v w : Vertex n) : Prop :=
  ((w.1.1 : ℕ) = v.1.1 + 1 ∧ ((w.1.2 : ℕ) = v.1.2 + 1 ∨ (w.1.2 : ℕ) + 1 = v.1.2)) ∨
    ((v.1.1 : ℕ) % 2 = 0 ∧
      (((w.1.1 : ℕ) = v.1.1 ∧ (w.1.2 : ℕ) = v.1.2 + 2) ∨
        ((w.1.1 : ℕ) = v.1.1 + 2 ∧ (w.1.2 : ℕ) = v.1.2)))

/-- Adjacency in `T n`. -/
def Adj {n : ℕ} (v w : Vertex n) : Prop := Step v w ∨ Step w v

/-- Perfect matchings of `T n`. -/
abbrev PerfectMatching (n : ℕ) : Type :=
  { σ : Vertex n → Vertex n // ∀ v, σ (σ v) = v ∧ σ v ≠ v ∧ Adj v (σ v) }

noncomputable instance (n : ℕ) : Fintype (PerfectMatching n) := Fintype.ofFinite _

/-- The number `M(T n)` of perfect matchings. -/
noncomputable def M (n : ℕ) : ℕ := Fintype.card (PerfectMatching n)

/-- Blum's clause for `n = 4k`: exactly `2^k` divides `M(T_{4k})`. -/
def claim : Prop := ∀ k : ℕ, 1 ≤ k → 2 ^ k ∣ M (4 * k) ∧ ¬ 2 ^ (k + 1) ∣ M (4 * k)

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleDefs
