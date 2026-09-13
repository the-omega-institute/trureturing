/- GID: D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/GridNoLeafSubgraphRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lean/module/Lean.Elab.Tactic.Omega, mathlib/module/Mathlib.Data.Fin.Tuple.Finset, mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.Fintype.BigOperators, mathlib/module/Mathlib.Data.Fintype.Prod, mathlib/module/Mathlib.Data.Fintype.Sigma, mathlib/module/Mathlib.Data.Int.ModEq, mathlib/module/Mathlib.Tactic.FinCases, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: No-leaf edge subgraphs of the three-by-n grid satisfy Barker's recurrence and Kagey's congruence. -/

import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# No-leaf edge subgraphs of the three-by-n grid

An edge is represented by its left or lower column together with one of five
labels.  Labels zero and one are the two vertical edges in that column; labels
two through four are the horizontal edges in rows zero through two.  The
validity proof removes the three horizontal labels in the final column.  Thus
`Edge n` is a canonical oriented representation of the unordered nearest-
neighbour edges of the `3 x n` grid.

The proof splits an edge set into columns.  The incoming and outgoing
horizontal masks have eight possibilities and the vertical mask has four.
The resulting finite transfer certificate yields Barker's recurrence; an
induction modulo ten then yields Kagey's pattern.
-/

namespace D5.S1.Words.Patterns.GridNoLeafSubgraphRecurrence

open scoped Classical
noncomputable section

/-- Canonical labels for the unordered nearest-neighbour edges of a `3 x n` grid. -/
def Edge (n : ℕ) :=
  {p : Fin n × Fin 5 // p.2.val < 2 ∨ p.1.val + 1 < n}
  deriving DecidableEq

instance (n : ℕ) : Fintype (Edge n) :=
  Fintype.ofFinset (p := {p : Fin n × Fin 5 | p.2.val < 2 ∨ p.1.val + 1 < n})
    ((Finset.univ : Finset (Fin n × Fin 5)).filter
      (fun p ↦ p.2.val < 2 ∨ p.1.val + 1 < n))
    (by intro p; simp)

/-- Every canonical grid-edge label occurs exactly once. -/
def gridEdges (n : ℕ) : Finset (Edge n) := Finset.univ

private def edgeBit {n : ℕ} (H : Finset (Edge n)) (c : Fin n) (k : Fin 5) : Bool :=
  if h : k.val < 2 ∨ c.val + 1 < n then decide (⟨(c, k), h⟩ ∈ H) else false

private abbrev VerticalMask := Fin 2 → Bool
private abbrev HorizontalMask := Fin 3 → Bool
private abbrev Column := VerticalMask × HorizontalMask

private def zeroHorizontal : HorizontalMask := fun _ ↦ false

private def verticalMask {n : ℕ} (H : Finset (Edge n)) (c : Fin n) : VerticalMask :=
  fun r ↦ edgeBit H c ⟨r.val, by omega⟩

private def outgoingMask {n : ℕ} (H : Finset (Edge n)) (c : Fin n) : HorizontalMask :=
  fun r ↦ edgeBit H c ⟨r.val + 2, by omega⟩

private def incomingMask {n : ℕ} (H : Finset (Edge n)) (c : Fin n) : HorizontalMask :=
  if hc : 0 < c.val then
    outgoingMask H ⟨c.val - 1, by omega⟩
  else
    zeroHorizontal

private def localDegree
    (i : HorizontalMask) (v : VerticalMask) (o : HorizontalMask) (r : Fin 3) : ℕ :=
  Bool.toNat (i r) + Bool.toNat (o r) +
    (if hr : 0 < r.val then Bool.toNat (v ⟨r.val - 1, by omega⟩) else 0) +
    (if hr : r.val < 2 then Bool.toNat (v ⟨r.val, hr⟩) else 0)

/-- The number of selected grid edges incident to a vertex. -/
def degree {n : ℕ} (H : Finset (Edge n)) (x : Fin 3 × Fin n) : ℕ :=
  localDegree (incomingMask H x.2) (verticalMask H x.2) (outgoingMask H x.2) x.1

/-- A spanning edge-subgraph has no leaf; isolated vertices are allowed. -/
def NoLeaf {n : ℕ} (H : Finset (Edge n)) : Prop :=
  ∀ x : Fin 3 × Fin n, degree H x ≠ 1

/-- The literal number of no-leaf spanning edge-subgraphs of the `3 x n` grid. -/
def a (n : ℕ) : ℕ :=
  ((gridEdges n).powerset.filter (NoLeaf (n := n))).card

private def Good (i : HorizontalMask) (v : VerticalMask) (o : HorizontalMask) : Prop :=
  ∀ r : Fin 3, localDegree i v o r ≠ 1

private def encode {n : ℕ} (H : Finset (Edge n)) : Fin n → Column :=
  fun c ↦ (verticalMask H c, outgoingMask H c)

private def PathGood : {n : ℕ} → HorizontalMask → (Fin n → Column) → Prop
  | 0, i, _ => i = zeroHorizontal
  | _ + 1, i, f => Good i (f 0).1 (f 0).2 ∧ PathGood (f 0).2 (Fin.tail f)

private def transition (i o : HorizontalMask) : ℕ :=
  (Finset.univ.filter fun v : VerticalMask ↦ Good i v o).card

private def stateCount : ℕ → HorizontalMask → ℕ
  | 0, i => if i = zeroHorizontal then 1 else 0
  | n + 1, i => ∑ o : HorizontalMask, transition i o * stateCount n o

private def pathConsEquiv (n : ℕ) (i : HorizontalMask) :
    {f : Fin (n + 1) → Column // PathGood i f} ≃
      {p : Column × (Fin n → Column) //
        Good i p.1.1 p.1.2 ∧ PathGood p.1.2 p.2} where
  toFun f := ⟨(f.1 0, Fin.tail f.1), f.2⟩
  invFun p := ⟨Fin.cons p.1.1 p.1.2, by simpa [PathGood] using p.2⟩
  left_inv f := by
    apply Subtype.ext
    funext j
    exact Fin.cases (by simp) (fun k ↦ by change f.1 k.succ = f.1 k.succ; rfl) j
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · funext j
      simp

private def pathSigmaEquiv (n : ℕ) (i : HorizontalMask) :
    {p : Column × (Fin n → Column) //
      Good i p.1.1 p.1.2 ∧ PathGood p.1.2 p.2} ≃
      Σ o : HorizontalMask,
        ({v : VerticalMask // Good i v o} ×
          {tail : Fin n → Column // PathGood o tail}) where
  toFun p := ⟨p.1.1.2, ⟨⟨p.1.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩⟩
  invFun p := ⟨((p.2.1.1, p.1), p.2.2.1), p.2.1.2, p.2.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

private theorem card_paths (n : ℕ) (i : HorizontalMask) :
    Fintype.card {f : Fin n → Column // PathGood i f} = stateCount n i := by
  induction n generalizing i with
  | zero =>
      by_cases hi : i = zeroHorizontal
      · simpa [PathGood, stateCount, hi] using Fintype.card_unique
      · have hempty : IsEmpty {f : Fin 0 → Column // PathGood i f} :=
          ⟨fun f ↦ hi f.2⟩
        simp [stateCount, hi]
  | succ n ih =>
      rw [Fintype.card_congr (pathConsEquiv n i)]
      rw [Fintype.card_congr (pathSigmaEquiv n i)]
      simp only [Fintype.card_sigma, Fintype.card_prod]
      apply Finset.sum_congr rfl
      intro o _
      rw [ih]
      rw [Fintype.card_subtype]
      rfl

end
end D5.S1.Words.Patterns.GridNoLeafSubgraphRecurrence
