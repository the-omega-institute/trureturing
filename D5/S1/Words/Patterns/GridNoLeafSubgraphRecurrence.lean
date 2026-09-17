/- GID: D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/GridNoLeafSubgraphRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset, mathlib/module/Mathlib.Data.Fintype.BigOperators, mathlib/module/Mathlib.Data.Int.ModEq, mathlib/module/Mathlib.Tactic.FinCases, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: No-leaf edge subgraphs of the three-by-n grid satisfy Barker's recurrence and Kagey's congruence. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
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
abbrev Edge (n : ℕ) :=
  {p : Fin n × Fin 5 // p.2.val < 2 ∨ p.1.val + 1 < n}

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

private def incident {n : ℕ} (x : Fin 3 × Fin n) (e : Edge n) : Prop :=
  if hk : e.1.2.val < 2 then
    x = (⟨e.1.2.val, by omega⟩, e.1.1) ∨
      x = (⟨e.1.2.val + 1, by omega⟩, e.1.1)
  else
    x = (⟨e.1.2.val - 2, by omega⟩, e.1.1) ∨
      x = (⟨e.1.2.val - 2, by omega⟩, ⟨e.1.1.val + 1, by omega⟩)

/-- The number of selected grid edges incident to a vertex. -/
def degree {n : ℕ} (H : Finset (Edge n)) (x : Fin 3 × Fin n) : ℕ :=
  (H.filter fun e ↦
    if hk : e.1.2.val < 2 then
      x = (⟨e.1.2.val, by omega⟩, e.1.1) ∨
        x = (⟨e.1.2.val + 1, by omega⟩, e.1.1)
    else
      x = (⟨e.1.2.val - 2, by omega⟩, e.1.1) ∨
        x = (⟨e.1.2.val - 2, by omega⟩, ⟨e.1.1.val + 1, by omega⟩)).card

private def verticalEdge {n : ℕ} (c : Fin n) (r : Fin 2) : Edge n :=
  ⟨(c, ⟨r.val, by omega⟩), Or.inl r.isLt⟩

private def horizontalEdge {n : ℕ} (c : Fin n) (r : Fin 3) (hc : c.val + 1 < n) : Edge n :=
  ⟨(c, ⟨r.val + 2, by omega⟩), Or.inr hc⟩

@[simp] private theorem verticalEdge_eq_verticalEdge {n : ℕ}
    (c d : Fin n) (r s : Fin 2) :
    verticalEdge c r = verticalEdge d s ↔ c = d ∧ r = s := by
  constructor
  · intro h
    have hp := congrArg (fun e : Edge n ↦ e.1) h
    exact ⟨congrArg Prod.fst hp, Fin.ext (congrArg (fun p ↦ p.2.val) hp)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] private theorem horizontalEdge_eq_horizontalEdge {n : ℕ}
    (c d : Fin n) (r s : Fin 3) (hc : c.val + 1 < n) (hd : d.val + 1 < n) :
    horizontalEdge c r hc = horizontalEdge d s hd ↔ c = d ∧ r = s := by
  constructor
  · intro h
    have hp := congrArg (fun e : Edge n ↦ e.1) h
    refine ⟨congrArg Prod.fst hp, Fin.ext ?_⟩
    have hk : r.val + 2 = s.val + 2 := by
      simpa [horizontalEdge] using congrArg (fun p ↦ p.2.val) hp
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] private theorem verticalEdge_ne_horizontalEdge {n : ℕ}
    (c d : Fin n) (r : Fin 2) (s : Fin 3) (hd : d.val + 1 < n) :
    verticalEdge c r ≠ horizontalEdge d s hd := by
  intro h
  have hp := congrArg (fun e : Edge n ↦ e.1) h
  have hk : r.val = s.val + 2 := by
    simpa [verticalEdge, horizontalEdge] using congrArg (fun p ↦ p.2.val) hp
  omega

@[simp] private theorem horizontalEdge_ne_verticalEdge {n : ℕ}
    (c d : Fin n) (r : Fin 3) (s : Fin 2) (hc : c.val + 1 < n) :
    horizontalEdge c r hc ≠ verticalEdge d s := by
  exact Ne.symm (verticalEdge_ne_horizontalEdge d c s r hc)

@[simp] private theorem incident_verticalEdge {n : ℕ} (x : Fin 3 × Fin n)
    (c : Fin n) (r : Fin 2) :
    incident x (verticalEdge c r) ↔
      x = (⟨r.val, by omega⟩, c) ∨ x = (⟨r.val + 1, by omega⟩, c) := by
  simp [incident, verticalEdge]

@[simp] private theorem incident_horizontalEdge {n : ℕ} (x : Fin 3 × Fin n)
    (c : Fin n) (r : Fin 3) (hc : c.val + 1 < n) :
    incident x (horizontalEdge c r hc) ↔
      x = (r, c) ∨ x = (r, ⟨c.val + 1, hc⟩) := by
  simp [incident, horizontalEdge]

@[simp] private theorem verticalMask_apply {n : ℕ} (H : Finset (Edge n))
    (c : Fin n) (r : Fin 2) :
    verticalMask H c r = decide (verticalEdge c r ∈ H) := by
  have he :
      (⟨(c, ⟨r.val, by omega⟩), Or.inl r.isLt⟩ : Edge n) = verticalEdge c r := by
    apply Subtype.ext
    rfl
  simp [verticalMask, edgeBit, he]

private theorem outgoingMask_apply_of_lt {n : ℕ} (H : Finset (Edge n))
    (c : Fin n) (r : Fin 3) (hc : c.val + 1 < n) :
    outgoingMask H c r = decide (horizontalEdge c r hc ∈ H) := by
  have he :
      (⟨(c, ⟨r.val + 2, by omega⟩), Or.inr hc⟩ : Edge n) = horizontalEdge c r hc := by
    apply Subtype.ext
    rfl
  simp [outgoingMask, edgeBit, hc, he]

private theorem outgoingMask_apply_of_not_lt {n : ℕ} (H : Finset (Edge n))
    (c : Fin n) (r : Fin 3) (hc : ¬ c.val + 1 < n) :
    outgoingMask H c r = false := by
  simp [outgoingMask, edgeBit, hc]

private theorem finPred_ne {n : ℕ} (c : Fin n) (hc : 0 < c.val) :
    (⟨c.val - 1, by omega⟩ : Fin n) ≠ c := by
  intro h
  have := congrArg Fin.val h
  change c.val - 1 = c.val at this
  omega

private theorem fin_ne_finPred {n : ℕ} (c : Fin n) (hc : 0 < c.val) :
    c ≠ (⟨c.val - 1, by omega⟩ : Fin n) :=
  Ne.symm (finPred_ne c hc)

private theorem finSucc_ne {n : ℕ} (c : Fin n) (hc : c.val + 1 < n) :
    (⟨c.val + 1, hc⟩ : Fin n) ≠ c := by
  intro h
  have := congrArg Fin.val h
  change c.val + 1 = c.val at this
  omega

private theorem fin_ne_finSucc {n : ℕ} (c : Fin n) (hc : c.val + 1 < n) :
    c ≠ (⟨c.val + 1, hc⟩ : Fin n) :=
  Ne.symm (finSucc_ne c hc)

@[simp] private theorem boolToNat_decide (p : Prop) [Decidable p] :
    Bool.toNat (decide p) = if p then 1 else 0 := by
  by_cases hp : p <;> simp [hp]

@[simp] private theorem outgoingMask_toNat {n : ℕ} (H : Finset (Edge n))
    (c : Fin n) (r : Fin 3) :
    Bool.toNat (outgoingMask H c r) =
      if hc : c.val + 1 < n then if horizontalEdge c r hc ∈ H then 1 else 0 else 0 := by
  by_cases hc : c.val + 1 < n
  · rw [outgoingMask_apply_of_lt H c r hc]
    rw [dif_pos hc]
    simp
  · rw [outgoingMask_apply_of_not_lt H c r hc]
    rw [dif_neg hc]
    rfl

@[simp] private theorem incomingMask_toNat {n : ℕ} (H : Finset (Edge n))
    (c : Fin n) (r : Fin 3) :
    Bool.toNat (incomingMask H c r) =
      if hc : 0 < c.val then
        if horizontalEdge ⟨c.val - 1, by omega⟩ r (by
          change (c.val - 1) + 1 < n
          have hcLt := c.isLt
          omega) ∈ H then 1 else 0
      else 0 := by
  by_cases hc : 0 < c.val
  · have hp : (c.val - 1) + 1 < n := by omega
    rw [incomingMask, dif_pos hc, outgoingMask_apply_of_lt H _ r hp]
    rw [dif_pos hc]
    simp
  · rw [incomingMask, dif_neg hc, dif_neg hc]
    rfl

private def incidentEdges {n : ℕ} (x : Fin 3 × Fin n) : Finset (Edge n) :=
  (if hc : 0 < x.2.val then
      {horizontalEdge ⟨x.2.val - 1, by omega⟩ x.1 (by
        change (x.2.val - 1) + 1 < n
        omega)}
    else ∅) ∪
  (if hc : x.2.val + 1 < n then {horizontalEdge x.2 x.1 hc} else ∅) ∪
  (if hr : 0 < x.1.val then {verticalEdge x.2 ⟨x.1.val - 1, by omega⟩} else ∅) ∪
  (if hr : x.1.val < 2 then {verticalEdge x.2 ⟨x.1.val, hr⟩} else ∅)

private theorem verticalEdge_mem_incidentEdges_iff {n : ℕ}
    (x : Fin 3 × Fin n) (c : Fin n) (r : Fin 2) :
    verticalEdge c r ∈ incidentEdges x ↔ incident x (verticalEdge c r) := by
  rcases x with ⟨xrow, xcol⟩
  fin_cases xrow <;> fin_cases r <;>
    simp [incidentEdges, Prod.ext_iff, Fin.ext_iff] <;>
    split_ifs <;> simp [Fin.ext_iff] <;> omega

private theorem horizontalEdge_mem_incidentEdges_iff {n : ℕ}
    (x : Fin 3 × Fin n) (c : Fin n) (r : Fin 3) (hc : c.val + 1 < n) :
    horizontalEdge c r hc ∈ incidentEdges x ↔ incident x (horizontalEdge c r hc) := by
  rcases x with ⟨xrow, xcol⟩
  fin_cases xrow <;> fin_cases r <;>
    simp [incidentEdges, Prod.ext_iff, Fin.ext_iff] <;>
    split_ifs <;> simp [Fin.ext_iff] <;> omega

private theorem incidentEdges_eq {n : ℕ} (x : Fin 3 × Fin n) :
    incidentEdges x = (Finset.univ.filter (incident x) : Finset (Edge n)) := by
  rcases x with ⟨xrow, xcol⟩
  ext e
  rcases e with ⟨⟨c, k⟩, hk⟩
  by_cases hvertical : k.val < 2
  · let r : Fin 2 := ⟨k.val, hvertical⟩
    have he : (⟨(c, k), hk⟩ : Edge n) = verticalEdge c r := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact Fin.ext (by simp [r, verticalEdge])
    have hclean :
        verticalEdge c r ∈ incidentEdges (xrow, xcol) ↔
          verticalEdge c r ∈
            (Finset.univ.filter (incident (xrow, xcol)) : Finset (Edge n)) := by
      simpa using verticalEdge_mem_incidentEdges_iff (xrow, xcol) c r
    exact he.symm ▸ hclean
  · have hc : c.val + 1 < n := hk.resolve_left hvertical
    let r : Fin 3 := ⟨k.val - 2, by omega⟩
    have he : (⟨(c, k), hk⟩ : Edge n) = horizontalEdge c r hc := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        dsimp [r, horizontalEdge]
        omega
    have hclean :
        horizontalEdge c r hc ∈ incidentEdges (xrow, xcol) ↔
          horizontalEdge c r hc ∈
            (Finset.univ.filter (incident (xrow, xcol)) : Finset (Edge n)) := by
      simpa using horizontalEdge_mem_incidentEdges_iff (xrow, xcol) c r hc
    exact he.symm ▸ hclean

private theorem card_filter_one {n : ℕ} (H : Finset (Edge n)) (e₁ : Edge n) :
    (({e₁} : Finset (Edge n)).filter fun e ↦ e ∈ H).card =
      if e₁ ∈ H then 1 else 0 := by
  rw [Finset.filter_singleton]
  by_cases h₁ : e₁ ∈ H <;> simp [h₁]

private theorem card_filter_two {n : ℕ} (H : Finset (Edge n)) (e₁ e₂ : Edge n)
    (h₁₂ : e₁ ≠ e₂) :
    (({e₁, e₂} : Finset (Edge n)).filter fun e ↦ e ∈ H).card =
      (if e₁ ∈ H then 1 else 0) + if e₂ ∈ H then 1 else 0 := by
  rw [Finset.filter_insert, Finset.filter_singleton]
  by_cases h₁ : e₁ ∈ H <;> by_cases h₂ : e₂ ∈ H <;> simp [h₁, h₂, h₁₂]

private theorem card_filter_three {n : ℕ} (H : Finset (Edge n)) (e₁ e₂ e₃ : Edge n)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    (({e₁, e₂, e₃} : Finset (Edge n)).filter fun e ↦ e ∈ H).card =
      ((if e₁ ∈ H then 1 else 0) + if e₂ ∈ H then 1 else 0) +
        if e₃ ∈ H then 1 else 0 := by
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
  by_cases h₁ : e₁ ∈ H <;> by_cases h₂ : e₂ ∈ H <;> by_cases h₃ : e₃ ∈ H <;>
    simp [h₁, h₂, h₃, h₁₂, h₁₃, h₂₃]

private theorem card_filter_four {n : ℕ} (H : Finset (Edge n)) (e₁ e₂ e₃ e₄ : Edge n)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₁₄ : e₁ ≠ e₄)
    (h₂₃ : e₂ ≠ e₃) (h₂₄ : e₂ ≠ e₄) (h₃₄ : e₃ ≠ e₄) :
    (({e₁, e₂, e₃, e₄} : Finset (Edge n)).filter fun e ↦ e ∈ H).card =
      (((if e₁ ∈ H then 1 else 0) + if e₂ ∈ H then 1 else 0) +
        if e₃ ∈ H then 1 else 0) + if e₄ ∈ H then 1 else 0 := by
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
  by_cases h₁ : e₁ ∈ H <;> by_cases h₂ : e₂ ∈ H <;> by_cases h₃ : e₃ ∈ H <;>
    by_cases h₄ : e₄ ∈ H <;>
    simp [h₁, h₂, h₃, h₄, h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄]

set_option maxHeartbeats 1000000 in
private theorem degree_eq_localDegree {n : ℕ} (H : Finset (Edge n))
    (x : Fin 3 × Fin n) :
    degree H x =
      localDegree (incomingMask H x.2) (verticalMask H x.2) (outgoingMask H x.2) x.1 := by
  have hdegree : degree H x = (H.filter (incident x)).card := by
    apply congrArg Finset.card
    ext e
    simp [degree, incident]
  have hfilter :
      H.filter (incident x) = (incidentEdges x).filter (fun e ↦ e ∈ H) := by
    rw [incidentEdges_eq]
    ext e
    simp [and_comm]
  rw [hdegree, hfilter]
  rcases x with ⟨r, xcol⟩
  by_cases hprev : 0 < xcol.val <;> by_cases hnext : xcol.val + 1 < n <;>
    fin_cases r <;>
    simp [incidentEdges, hprev, hnext, localDegree] <;>
    first
    | simpa using card_filter_one H _
    | simpa using card_filter_two H _ _ (by simp)
    | simpa using card_filter_three H _ _ _ (by simpa using finPred_ne xcol hprev)
        (by simp) (by simp)
    | simpa using card_filter_three H _ _ _ (by simp) (by simp) (by simp)
    | simpa using card_filter_four H _ _ _ _
        (by simp [Fin.ext_iff]; omega) (by simp) (by simp) (by simp) (by simp) (by simp)

/-- A spanning edge-subgraph has no leaf; isolated vertices are allowed. -/
def NoLeaf {n : ℕ} (H : Finset (Edge n)) : Prop :=
  ∀ x : Fin 3 × Fin n, degree H x ≠ 1

/-- The literal number of no-leaf spanning edge-subgraphs of the `3 x n` grid. -/
def a (n : ℕ) : ℕ :=
  ((gridEdges n).powerset.filter (NoLeaf (n := n))).card

private def good (i : HorizontalMask) (v : VerticalMask) (o : HorizontalMask) : Bool :=
  decide (localDegree i v o ⟨0, by omega⟩ ≠ 1) &&
    decide (localDegree i v o ⟨1, by omega⟩ ≠ 1) &&
      decide (localDegree i v o ⟨2, by omega⟩ ≠ 1)

private def Good (i : HorizontalMask) (v : VerticalMask) (o : HorizontalMask) : Prop :=
  good i v o = true

private instance goodDecidable (i : HorizontalMask) (v : VerticalMask) (o : HorizontalMask) :
    Decidable (Good i v o) := Bool.decEq (good i v o) true

private theorem good_eq_true_iff (i : HorizontalMask) (v : VerticalMask) (o : HorizontalMask) :
    Good i v o ↔ ∀ r : Fin 3, localDegree i v o r ≠ 1 := by
  constructor
  · intro h
    have hs :
        (localDegree i v o ⟨0, by omega⟩ ≠ 1 ∧
          localDegree i v o ⟨1, by omega⟩ ≠ 1) ∧
            localDegree i v o ⟨2, by omega⟩ ≠ 1 := by
      simpa only [Good, good, Bool.and_eq_true, decide_eq_true_eq] using h
    intro r
    fin_cases r
    · exact hs.1.1
    · exact hs.1.2
    · exact hs.2
  · intro h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    have h2 := h ⟨2, by omega⟩
    change good i v o = true
    simp only [good, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨h0, h1⟩, h2⟩

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

private def decode {n : ℕ} (f : Fin n → Column) : Finset (Edge n) :=
  Finset.univ.filter fun e ↦
    if hk : e.1.2.val < 2 then
      (f e.1.1).1 ⟨e.1.2.val, hk⟩ = true
    else
      (f e.1.1).2 ⟨e.1.2.val - 2, by omega⟩ = true

private theorem decode_encode {n : ℕ} (H : Finset (Edge n)) :
    decode (encode H) = H := by
  ext e
  rcases e with ⟨⟨c, k⟩, hk⟩
  by_cases hvertical : k.val < 2
  · simp only [decode, Edge, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dif_pos hvertical]
    change edgeBit H c ⟨k.val, by omega⟩ = true ↔ _
    rw [edgeBit, dif_pos (Or.inl hvertical)]
    simp only [decide_eq_true_eq]
  · have hcvalid : c.val + 1 < n := hk.resolve_left hvertical
    simp only [decode, Edge, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dif_neg hvertical]
    let r : Fin 3 := ⟨k.val - 2, by omega⟩
    change edgeBit H c ⟨r.val + 2, by omega⟩ = true ↔ _
    rw [edgeBit, dif_pos (Or.inr hcvalid)]
    simp only [decide_eq_true_eq]
    have hr : r.val + 2 = k.val := by dsimp [r]; omega
    have hkeq : (⟨r.val + 2, by omega⟩ : Fin 5) = k := Fin.ext hr
    rw [hkeq]

private def preceding {n : ℕ}
    (i : HorizontalMask) (f : Fin n → Column) (c : Fin n) : HorizontalMask :=
  if hc : 0 < c.val then (f ⟨c.val - 1, by omega⟩).2 else i

private def GloballyGood {n : ℕ} (i : HorizontalMask) (f : Fin n → Column) : Prop :=
  (∀ c : Fin n, Good (preceding i f c) (f c).1 (f c).2) ∧
    match n with
    | 0 => i = zeroHorizontal
    | m + 1 => (f (Fin.last m)).2 = zeroHorizontal

private theorem preceding_tail {n : ℕ} (i : HorizontalMask)
    (f : Fin (n + 1) → Column) (j : Fin n) :
    preceding (f 0).2 (Fin.tail f) j = preceding i f j.succ := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · simp [preceding, Fin.tail]
      · simp [preceding, Fin.tail]

private theorem pathGood_iff_globallyGood {n : ℕ}
    (i : HorizontalMask) (f : Fin n → Column) :
    PathGood i f ↔ GloballyGood i f := by
  induction n generalizing i with
  | zero => simp [PathGood, GloballyGood]
  | succ n ih =>
      rw [show PathGood i f =
        (Good i (f 0).1 (f 0).2 ∧ PathGood (f 0).2 (Fin.tail f)) by rfl]
      rw [ih]
      constructor
      · rintro ⟨hfirst, htail, hend⟩
        refine ⟨?_, ?_⟩
        · intro c
          refine Fin.cases ?_ (fun j ↦ ?_) c
          · simpa [preceding] using hfirst
          · rw [← preceding_tail i f j]
            exact htail j
        · cases n with
          | zero => simpa using hend
          | succ n => simpa [Fin.tail] using hend
      · rintro ⟨hall, hend⟩
        refine ⟨?_, ?_⟩
        · simpa [preceding] using hall 0
        · refine ⟨?_, ?_⟩
          · intro j
            rw [preceding_tail i f j]
            exact hall j.succ
          · cases n with
            | zero => simpa using hend
            | succ n => simpa [Fin.tail] using hend

private theorem preceding_encode {n : ℕ} (H : Finset (Edge n)) (c : Fin n) :
    preceding zeroHorizontal (encode H) c = incomingMask H c := by
  by_cases hc : 0 < c.val
  · simp [preceding, incomingMask, encode, hc]
  · simp [preceding, incomingMask, hc]

private theorem noLeaf_iff_local_columns {n : ℕ} (H : Finset (Edge n)) :
    NoLeaf H ↔
      ∀ c : Fin n,
        Good (preceding zeroHorizontal (encode H) c) (encode H c).1 (encode H c).2 := by
  constructor
  · intro h c
    apply (good_eq_true_iff _ _ _).mpr
    intro r
    have hr := h (r, c)
    rw [degree_eq_localDegree] at hr
    rw [preceding_encode H c]
    exact hr
  · intro h ⟨r, c⟩
    have hr := (good_eq_true_iff _ _ _).mp (h c) r
    rw [preceding_encode H c] at hr
    rw [degree_eq_localDegree]
    exact hr

private theorem encode_final_zero {n : ℕ} (H : Finset (Edge n)) :
    match n with
    | 0 => zeroHorizontal = zeroHorizontal
    | m + 1 => (encode H (Fin.last m)).2 = zeroHorizontal := by
  cases n with
  | zero => rfl
  | succ m =>
      funext r
      simp [encode, outgoingMask, edgeBit, zeroHorizontal]

private theorem noLeaf_iff_pathGood {n : ℕ} (H : Finset (Edge n)) :
    NoLeaf H ↔ PathGood zeroHorizontal (encode H) := by
  rw [pathGood_iff_globallyGood]
  constructor
  · intro h
    refine ⟨(noLeaf_iff_local_columns H).mp h, ?_⟩
    cases n with
    | zero => rfl
    | succ m => simpa using encode_final_zero H
  · intro h
    exact (noLeaf_iff_local_columns H).mpr h.1

private theorem encode_decode_of_pathGood {n : ℕ} (f : Fin n → Column)
    (hf : PathGood zeroHorizontal f) : encode (decode f) = f := by
  have hg := (pathGood_iff_globallyGood zeroHorizontal f).mp hf
  funext c
  apply Prod.ext
  · funext r
    simp [encode, verticalMask, edgeBit, decode]
  · funext r
    by_cases hc : c.val + 1 < n
    · simp [encode, outgoingMask, edgeBit, decode, hc]
    · have hbit : (f c).2 r = false := by
        cases n with
        | zero => exact Fin.elim0 c
        | succ m =>
            have hlast : c = Fin.last m := by
              apply Fin.ext
              simp
              omega
            rw [hlast]
            exact congrFun hg.2 r
      simp [encode, outgoingMask, edgeBit, decode, hc, hbit]

private def edgePathEquiv (n : ℕ) :
    {H : Finset (Edge n) // NoLeaf H} ≃
      {f : Fin n → Column // PathGood zeroHorizontal f} where
  toFun H := ⟨encode H.1, (noLeaf_iff_pathGood H.1).mp H.2⟩
  invFun f := ⟨decode f.1, (noLeaf_iff_pathGood (decode f.1)).mpr (by
    rw [encode_decode_of_pathGood f.1 f.2]
    exact f.2)⟩
  left_inv H := by
    apply Subtype.ext
    exact decode_encode H.1
  right_inv f := by
    apply Subtype.ext
    exact encode_decode_of_pathGood f.1 f.2

private theorem a_eq_stateCount (n : ℕ) : a n = stateCount n zeroHorizontal := by
  let s := (gridEdges n).powerset.filter (NoLeaf (n := n))
  let hmem : ∀ H : Finset (Edge n), H ∈ s ↔ H ∈ {H | NoLeaf H} := by
    intro H
    simp [s, gridEdges]
  letI : Fintype {H : Finset (Edge n) // NoLeaf H} := Fintype.ofFinset s hmem
  calc
    a n = s.card := rfl
    _ = Fintype.card {H : Finset (Edge n) // NoLeaf H} :=
      (Fintype.card_ofFinset s hmem).symm
    _ = Fintype.card {f : Fin n → Column // PathGood zeroHorizontal f} :=
      Fintype.card_congr (edgePathEquiv n)
    _ = stateCount n zeroHorizontal := card_paths n zeroHorizontal

private theorem transfer_certificate :
    ∀ i : HorizontalMask,
      (stateCount 5 i : ℤ) =
        12 * stateCount 4 i - 6 * stateCount 3 i -
          20 * stateCount 2 i - 5 * stateCount 1 i := by
  decide

private theorem stateCount_succ_int (n : ℕ) (i : HorizontalMask) :
    (stateCount (n + 1) i : ℤ) =
      ∑ o : HorizontalMask, (transition i o : ℤ) * stateCount n o := by
  rw [stateCount]
  simpa only [Nat.cast_sum, Nat.cast_mul]

private theorem stateCount_recurrence (n : ℕ) (i : HorizontalMask) :
    (stateCount (n + 5) i : ℤ) =
      12 * stateCount (n + 4) i - 6 * stateCount (n + 3) i -
        20 * stateCount (n + 2) i - 5 * stateCount (n + 1) i := by
  induction n generalizing i with
  | zero => simpa using transfer_certificate i
  | succ n ih =>
      have h5 : n.succ + 5 = (n + 5) + 1 := by omega
      have h4 : n.succ + 4 = (n + 4) + 1 := by omega
      have h3 : n.succ + 3 = (n + 3) + 1 := by omega
      have h2 : n.succ + 2 = (n + 2) + 1 := by omega
      have h1 : n.succ + 1 = (n + 1) + 1 := by omega
      rw [h5, h4, h3, h2, h1]
      rw [stateCount_succ_int (n + 5) i]
      rw [stateCount_succ_int (n + 4) i]
      rw [stateCount_succ_int (n + 3) i]
      rw [stateCount_succ_int (n + 2) i]
      rw [stateCount_succ_int (n + 1) i]
      have pull (c : ℤ) (g : HorizontalMask → ℤ) :
          (∑ o : HorizontalMask, (transition i o : ℤ) * (c * g o)) =
            c * ∑ o : HorizontalMask, (transition i o : ℤ) * g o := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro o _
        ring
      calc
        (∑ o : HorizontalMask, (transition i o : ℤ) * stateCount (n + 5) o) =
            ∑ o : HorizontalMask, (transition i o : ℤ) *
              (12 * stateCount (n + 4) o - 6 * stateCount (n + 3) o -
                20 * stateCount (n + 2) o - 5 * stateCount (n + 1) o) := by
          apply Finset.sum_congr rfl
          intro o _
          rw [ih o]
        _ = 12 * (∑ o : HorizontalMask, (transition i o : ℤ) * stateCount (n + 4) o) -
              6 * (∑ o : HorizontalMask, (transition i o : ℤ) * stateCount (n + 3) o) -
              20 * (∑ o : HorizontalMask, (transition i o : ℤ) * stateCount (n + 2) o) -
              5 * (∑ o : HorizontalMask, (transition i o : ℤ) * stateCount (n + 1) o) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          rw [pull, pull, pull, pull]

/-- Barker's conjectured order-four recurrence for the literal grid-subgraph count. -/
theorem barker_a301976 : ∀ n : ℕ, 4 < n →
    (a n : ℤ) =
      12 * a (n - 1) - 6 * a (n - 2) - 20 * a (n - 3) - 5 * a (n - 4) := by
  intro n hn
  rw [a_eq_stateCount n, a_eq_stateCount (n - 1), a_eq_stateCount (n - 2),
    a_eq_stateCount (n - 3), a_eq_stateCount (n - 4)]
  have h5 : n - 5 + 5 = n := by omega
  have h4 : n - 5 + 4 = n - 1 := by omega
  have h3 : n - 5 + 3 = n - 2 := by omega
  have h2 : n - 5 + 2 = n - 3 := by omega
  have h1 : n - 5 + 1 = n - 4 := by omega
  simpa only [h5, h4, h3, h2, h1] using
    stateCount_recurrence (n - 5) zeroHorizontal

private theorem initial_mod_ten :
    a 3 % 10 = 3 ∧ a 4 % 10 = 3 ∧ a 5 % 10 = 3 ∧ a 6 % 10 = 3 := by
  rw [a_eq_stateCount 3, a_eq_stateCount 4, a_eq_stateCount 5, a_eq_stateCount 6]
  decide

/-- Kagey's conjectured final-digit pattern for no-leaf grid subgraphs. -/
theorem kagey_a301976_mod10 : ∀ n : ℕ, 2 < n → a n % 10 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hsmall : n ≤ 6
      · rcases initial_mod_ten with ⟨h3, h4, h5, h6⟩
        have hn_cases : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
        rcases hn_cases with rfl | rfl | rfl | rfl <;> assumption
      · have hn7 : 7 ≤ n := by omega
        have hm1nat : Nat.ModEq 10 (a (n - 1)) 3 := by
          simpa [Nat.ModEq] using ih (n - 1) (by omega) (by omega)
        have hm2nat : Nat.ModEq 10 (a (n - 2)) 3 := by
          simpa [Nat.ModEq] using ih (n - 2) (by omega) (by omega)
        have hm4nat : Nat.ModEq 10 (a (n - 4)) 3 := by
          simpa [Nat.ModEq] using ih (n - 4) (by omega) (by omega)
        have hm1 : (a (n - 1) : ℤ) ≡ 3 [ZMOD 10] :=
          Int.natCast_modEq_iff.mpr hm1nat
        have hm2 : (a (n - 2) : ℤ) ≡ 3 [ZMOD 10] :=
          Int.natCast_modEq_iff.mpr hm2nat
        have hm4 : (a (n - 4) : ℤ) ≡ 3 [ZMOD 10] :=
          Int.natCast_modEq_iff.mpr hm4nat
        have hm3 : 20 * (a (n - 3) : ℤ) ≡ 20 * 3 [ZMOD 10] := by
          have hd : (10 : ℤ) ∣ 20 * (a (n - 3) : ℤ) :=
            dvd_mul_of_dvd_left (by norm_num) _
          rw [Int.ModEq, Int.emod_eq_zero_of_dvd hd]
          norm_num
        have hrec :
            (a n : ℤ) =
              12 * a (n - 1) - 6 * a (n - 2) -
                20 * a (n - 3) - 5 * a (n - 4) := barker_a301976 n (by omega)
        have hrecmod :
            (a n : ℤ) ≡
              12 * a (n - 1) - 6 * a (n - 2) -
                20 * a (n - 3) - 5 * a (n - 4) [ZMOD 10] := by
          rw [hrec]
        have hterms :
            12 * (a (n - 1) : ℤ) - 6 * a (n - 2) -
                20 * a (n - 3) - 5 * a (n - 4) ≡
              12 * 3 - 6 * 3 - 20 * 3 - 5 * 3 [ZMOD 10] :=
          (((hm1.mul_left 12).sub (hm2.mul_left 6)).sub hm3).sub (hm4.mul_left 5)
        have hnum : (12 * 3 - 6 * 3 - 20 * 3 - 5 * 3 : ℤ) ≡ 3 [ZMOD 10] := by
          norm_num [Int.ModEq]
        have hz : (a n : ℤ) ≡ 3 [ZMOD 10] := hrecmod.trans (hterms.trans hnum)
        have hnat : Nat.ModEq 10 (a n) 3 := Int.natCast_modEq_iff.mp hz
        simpa [Nat.ModEq] using hnat

#print axioms barker_a301976
#print axioms kagey_a301976_mod10

end
end D5.S1.Words.Patterns.GridNoLeafSubgraphRecurrence
