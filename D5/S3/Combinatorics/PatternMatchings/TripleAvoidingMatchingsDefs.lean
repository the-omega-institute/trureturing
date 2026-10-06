/- GID: D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs
   mirror-E: none(waiver:biswas-shankar-sivasubramanian-p1-statement-definition)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Catalan.Basic, mathlib/module/Mathlib.Data.Nat.Fib.Basic, mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Biswas, Shankar and Sivasubramanian's enumeration question for perfect matchings avoiding the pattern set {123, 132, 213}. -/

import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsDefs

open PowerSeries

/-! Fixed public statement: S. Biswas, U. Shankar and S. Sivasubramanian, *Matchings and
    shape-Wilf-Equivalence of sets of patterns of length three I: Triples*, arXiv:2609.08562v1,
    Section 6, Question 1: "Can we enumerate the matchings that avoid the set of patterns
    P1 = {123, 132, 213} and P13 = {132, 213, 321}?"  This file states the `P1` clause.

    A perfect matching of `[2n]` is a fixed-point-free involution of `Fin (2 * n)`.  Following
    Section 4 and Figure 1 of the paper (the Bloom–Elizalde correspondence with Ferrers-board
    transversals), three arcs form an occurrence of a pattern of length three only when their three
    left endpoints all precede their three right endpoints.  Numbering the arcs by increasing left
    endpoint, the label `p` records the complement of the order of the right endpoints: in Figure 1
    the pattern `321` is the matching `(1,4),(2,5),(3,6)` and `123` is `(1,6),(2,5),(3,4)`.
    Patterns are written zero-based, so `123` is `![0, 1, 2]`. -/

/-- Perfect matchings of `Fin (2 * n)`, as fixed-point-free involutions. -/
abbrev Matching (n : ℕ) : Type :=
  { σ : Fin (2 * n) → Fin (2 * n) // ∀ v, σ (σ v) = v ∧ σ v ≠ v }

noncomputable instance (n : ℕ) : Fintype (Matching n) := Fintype.ofFinite _

/-- The matching `m` contains the pattern `p`: three arcs with left endpoints `l 0 < l 1 < l 2`,
    all before every right endpoint, whose right endpoints are ordered oppositely to the labels. -/
def Occurs {n : ℕ} (m : Matching n) (p : Fin 3 → Fin 3) : Prop :=
  ∃ l : Fin 3 → Fin (2 * n), StrictMono l ∧ (∀ i, l 2 < m.1 (l i)) ∧
    ∀ i j, m.1 (l i) < m.1 (l j) ↔ p j < p i

/-- The pattern set `P1 = {123, 132, 213}`. -/
def P1 : Set (Fin 3 → Fin 3) := {![0, 1, 2], ![0, 2, 1], ![1, 0, 2]}

/-- The matching avoids every pattern of `P1`. -/
def AvoidsP1 {n : ℕ} (m : Matching n) : Prop := ∀ p ∈ P1, ¬ Occurs m p

open Classical in
/-- The number `a_n` of perfect matchings of `[2n]` avoiding `P1`. -/
noncomputable def a (n : ℕ) : ℕ := (Finset.univ.filter fun m : Matching n => AvoidsP1 m).card

/-- The generating function `Σ a_n z^n`. -/
noncomputable def aSeries : PowerSeries ℤ := mk fun n => (a n : ℤ)

/-- `H(z) = Σ_k Cat_k F_{k+3} z^k`. -/
noncomputable def hSeries : PowerSeries ℤ := mk fun k => ((catalan k * Nat.fib (k + 3) : ℕ) : ℤ)

/-- The enumeration: `Σ a_n z^n = (1 − zH) / (1 − z − zH)`, written as the equivalent
    cross-multiplied identity (the denominator has constant coefficient `1`). -/
def claim : Prop := (1 - X - X * hSeries) * aSeries = 1 - X * hSeries

end D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsDefs
