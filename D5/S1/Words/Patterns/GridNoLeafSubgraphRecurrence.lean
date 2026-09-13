/- GID: D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/GridNoLeafSubgraphRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lean/module/Lean.Elab.Tactic.Omega, mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset, mathlib/module/Mathlib.Data.Fin.Tuple.Finset, mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.Fintype.BigOperators, mathlib/module/Mathlib.Data.Fintype.Prod, mathlib/module/Mathlib.Data.Fintype.Sigma, mathlib/module/Mathlib.Data.Int.ModEq, mathlib/module/Mathlib.Tactic.FinCases, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: No-leaf edge subgraphs of the three-by-n grid satisfy Barker's recurrence and Kagey's congruence. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
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

/-- The number of selected grid edges incident to a vertex. -/
def degree {n : ℕ} (H : Finset (Edge n)) (x : Fin 3 × Fin n) : ℕ :=
  localDegree (incomingMask H x.2) (verticalMask H x.2) (outgoingMask H x.2) x.1

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
    rw [preceding_encode H c]
    exact hr
  · intro h ⟨r, c⟩
    have hr := (good_eq_true_iff _ _ _).mp (h c) r
    rw [preceding_encode H c] at hr
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

end
end D5.S1.Words.Patterns.GridNoLeafSubgraphRecurrence
