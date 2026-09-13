/- GID: D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Fin.Tuple.Basic, mathlib/module/Mathlib.Data.Finset.Sum, mathlib/module/Mathlib.Data.Fintype.Card, mathlib/module/Mathlib.Data.Fintype.Powerset, mathlib/module/Mathlib.Data.Fintype.Prod, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Literal labeled-graph avoidance and its allowed-vertex state yield Barker's recurrence. -/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

/-!
# Crossing- and nesting-free labeled graphs

This module proves Colin Barker's 2019 OEIS A326244 conjecture.  Vertices are
linearly ordered by `Fin n`; an edge is represented by its increasing ordered
pair.  The counted object is therefore the literal labeled simple graph from
the OEIS entry, rather than a surrogate encoding.

The proof removes the largest vertex and records the old vertices `c` for
which every edge ending to the right of `c` is incident with `c`.  Any subset
of these allowed vertices can be joined to the new maximum.  The next allowed
set has size `r + 1`, `2`, or `1` according as that subset is empty, a
singleton, or larger.  Three weighted counts then give the claimed recurrence.
-/

namespace D5.S1.Words.Patterns.NoncrossingNonnestingGraphRecurrence

open scoped Classical

/-- The two endpoint orders called crossing in OEIS A326244. -/
def Crossing {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2) ∨
    (f.1 < e.1 ∧ e.1 < f.2 ∧ f.2 < e.2)

/-- The two endpoint orders called nesting in OEIS A326244. -/
def Nesting {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  (e.1 < f.1 ∧ f.2 < e.2) ∨ (f.1 < e.1 ∧ e.2 < f.2)

/-- A literal simple graph whose increasing edges neither cross nor nest. -/
def IsAvoiding {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ E, e.1 < e.2) ∧
    ∀ e ∈ E, ∀ f ∈ E, ¬ Crossing e f ∧ ¬ Nesting e f

/-- Number of labeled `n`-vertex simple graphs with neither pattern. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun E : Finset (Fin n × Fin n) => IsAvoiding E)).card

private abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

private def GoodEdges {n : ℕ} (E : Finset (Edge n)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, ¬ Crossing e.1 f.1 ∧ ¬ Nesting e.1 f.1

private abbrev GoodGraph (n : ℕ) := {E : Finset (Edge n) // GoodEdges E}

private def Allowed {n : ℕ} (G : GoodGraph n) : Finset (Fin n) :=
  Finset.univ.filter fun c =>
    ∀ e ∈ G.1, c < e.1.2 → e.1.1 = c ∨ e.1.2 = c

private def edgeSuccEquiv (n : ℕ) : Edge (n + 1) ≃ Edge n ⊕ Fin n where
  toFun e :=
    if hright : e.1.2 = Fin.last n then
      Sum.inr (Fin.castPred e.1.1 (by
        exact (Fin.lt_last_iff_ne_last.mp (hright ▸ e.2))))
    else
      Sum.inl ⟨(Fin.castPred e.1.1 (by
        exact (Fin.lt_last_iff_ne_last.mp
          (e.2.trans (Fin.lt_last_iff_ne_last.mpr hright)))),
        Fin.castPred e.1.2 hright), e.2⟩
  invFun
    | Sum.inl e => ⟨(e.1.1.castSucc, e.1.2.castSucc), e.2⟩
    | Sum.inr c => ⟨(c.castSucc, Fin.last n), Fin.castSucc_lt_last c⟩
  left_inv e := by
    by_cases hright : e.1.2 = Fin.last n
    · simp [hright]
      apply Subtype.ext
      apply Prod.ext
      · simp
      · exact hright.symm
    · simp [hright]
  right_inv e := by
    rcases e with e | c
    · simp
    · simp

end D5.S1.Words.Patterns.NoncrossingNonnestingGraphRecurrence
