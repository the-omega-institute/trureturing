/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderThree
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A row- and column-injective array of order three has a transversal. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.LatinCore
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Std.Tactic.BVDecide

namespace MaLatin

private abbrev EqualityTable := ℕ → ℕ → Bool

private def orderedEq (e : EqualityTable) (i j : ℕ) : Bool :=
  if i = j then true else if i < j then e i j else e j i

private def cell {n : ℕ} (i j : Fin n) : ℕ := i.val * n + j.val

private def cellEq {n : ℕ} (e : EqualityTable) (i j k l : Fin n) : Bool :=
  orderedEq e (cell i j) (cell k l)

/-- The only nontrivial equivalence-relation axioms, stored for increasing triples. -/
private def consistent (n : ℕ) (e : EqualityTable) : Bool :=
  (List.range (n*n)).all fun i =>
    (List.range (n*n)).all fun j =>
      (List.range (n*n)).all fun k =>
        if i < j ∧ j < k then
          let a := e i j
          let b := e j k
          let c := e i k
          (!(a && b) || c) && (!(a && c) || b) && (!(b && c) || a)
        else true

private def latinB (n : ℕ) (e : EqualityTable) : Bool :=
  allFin (n := n) fun k => allFin fun i => allFin fun j =>
    if i < j then !cellEq e k i k j && !cellEq e i k j k else true

private def rainbowB {n : ℕ} (e : EqualityTable) (p : Fin n → Fin n) : Bool :=
  allFin fun i => allFin fun j => if i < j then !cellEq e i (p i) j (p j) else true

private def noRainbowB {n : ℕ} (ps : List (Fin n → Fin n)) (e : EqualityTable) : Bool :=
  ps.all fun p => !injectiveB p || !rainbowB e p

private def flatten {n : ℕ} (A : Fin n → Fin n → α) (i : ℕ) : Option α :=
  if h : i < n * n then
    let (r, c) := finProdFinEquiv.symm (⟨i, h⟩ : Fin (n*n))
    some (A r c)
  else none

private theorem flatten_cell {n : ℕ} (A : Fin n → Fin n → α) (i j : Fin n) :
    flatten A (cell i j) = some (A i j) := by
  let x : Fin (n*n) := finProdFinEquiv (i,j)
  have hx : x.val = cell i j := by
    change j.val + n * i.val = i.val * n + j.val
    ac_rfl
  unfold flatten
  split
  · next h =>
    have he : (⟨cell i j, h⟩ : Fin (n*n)) = x := Fin.ext hx.symm
    rw [he]
    simp [x]
  · next h => exact (h (hx ▸ x.isLt)).elim

/-- Boolean equality on the bounded set of row-major cell positions. -/
private def encode {n : ℕ} [DecidableEq α] (A : Fin n → Fin n → α) : EqualityTable :=
  fun i j => decide (flatten A i = flatten A j)

private theorem encode_cell {n : ℕ} [DecidableEq α] (A : Fin n → Fin n → α) (i j k l : Fin n) :
    cellEq (encode A) i j k l = true ↔ A i j = A k l := by
  have hm (p q : ℕ) : orderedEq (encode A) p q = true ↔ flatten A p = flatten A q := by
    by_cases h : p = q
    · simp [orderedEq, h]
    · by_cases hlt : p < q
      · simp [orderedEq, encode, h, hlt]
      · simp [orderedEq, encode, h, hlt, eq_comm]
  rw [cellEq, hm, flatten_cell, flatten_cell, Option.some.injEq]

private theorem encode_cell_not {n : ℕ} [DecidableEq α] (A : Fin n → Fin n → α)
    (i j k l : Fin n) : (!cellEq (encode A) i j k l) = true ↔ A i j ≠ A k l := by
  change (!cellEq (encode A) i j k l) = true ↔ ¬ (A i j = A k l)
  rw [← encode_cell A i j k l]
  cases cellEq (encode A) i j k l <;> decide

private theorem encode_consistent {n : ℕ} [DecidableEq α] (A : Fin n → Fin n → α) :
    consistent n (encode A) = true := by
  simp only [consistent, List.all_eq_true, List.mem_range]
  intro i _ j _ k _
  split
  · by_cases hab : flatten A i = flatten A j <;>
      by_cases hbc : flatten A j = flatten A k <;>
      by_cases hac : flatten A i = flatten A k <;>
      simp_all [encode]
  · rfl

private theorem encode_latin {n : ℕ} [DecidableEq α] (A : Fin n → Fin n → α) (h : Latin A) :
    latinB n (encode A) = true := by
  simp only [latinB, allFin_true]
  intro k i j
  split
  · rename_i hij
    simp only [Bool.and_eq_true, encode_cell_not]
    exact ⟨fun h' => (ne_of_lt hij) (h.1 k h'), fun h' => (ne_of_lt hij) (h.2 k h')⟩
  · rfl

private theorem injective_of_rainbowB {n : ℕ} [DecidableEq α] {A : Fin n → Fin n → α}
    {p : Fin n → Fin n} (hp : rainbowB (encode A) p = true) :
    Function.Injective fun i => A i (p i) := by
  simp only [rainbowB, allFin_true] at hp
  intro i j h
  rcases lt_trichotomy i j with hij | hij | hji
  · have hh := hp i j
    simp only [hij, ite_true, encode_cell_not] at hh
    exact (hh h).elim
  · exact hij
  · have hh := hp j i
    simp only [hji, ite_true, encode_cell_not] at hh
    exact (hh h.symm).elim

private theorem encode_noRainbow {n : ℕ} [DecidableEq α] (A : Fin n → Fin n → α)
    (ps : List (Fin n → Fin n)) (h : ¬ Rainbow A) :
    noRainbowB ps (encode A) = true := by
  rw [noRainbowB, List.all_eq_true]
  intro p _
  by_cases hp : injectiveB p = true
  · by_cases hr : rainbowB (encode A) p = true
    · exact (h ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.mp
        (injective_of_injectiveB hp)), injective_of_rainbowB hr⟩).elim
    · simp [hr]
  · simp [hp]


private def smallPerms3 : List (Fin 3 → Fin 3) := [![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]
private theorem boolNot (b : Bool) : (!b) = true ↔ ¬ (b = true) := by cases b <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem checked3 {α : Type*} [DecidableEq α] (A : Fin 3 → Fin 3 → α)
    (hl : latinB 3 (encode A) = true)
    (ht : noRainbowB smallPerms3 (encode A) = true) :
    False := by
  let e := encode A
  change (((((!(e 0 1) && !(e 0 3)) && ((!(e 0 2) && !(e 0 6)) && true)) && (((!(e 1 2) && !(e 3 6)) &&
    true) && true)) && ((((!(e 3 4) && !(e 1 4)) && ((!(e 3 5) && !(e 1 7)) && true)) && (((!(e 4 5) && !(e 4
    7)) && true) && true)) && ((((!(e 6 7) && !(e 2 5)) && ((!(e 6 8) && !(e 2 8)) && true)) && (((!(e 7 8)
    && !(e 5 8)) && true) && true)) && true)))) = true at hl
  change ((!((!(e 0 4) && (!(e 0 8) && true)) && ((!(e 4 8) && true) && true)) && (!((!(e 0 5) && (!(e 0 7)
    && true)) && ((!(e 5 7) && true) && true)) && (!((!(e 1 3) && (!(e 1 8) && true)) && ((!(e 3 8) && true)
    && true)) && (!((!(e 1 5) && (!(e 1 6) && true)) && ((!(e 5 6) && true) && true)) && (!((!(e 2 3) && (!(e
    2 7) && true)) && ((!(e 3 7) && true) && true)) && (!((!(e 2 4) && (!(e 2 6) && true)) && ((!(e 4 6) &&
    true) && true)) && true))))))) = true at ht
  simp only [e, encode, boolNot, decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true,
    eq_self, and_true, or_false] at hl ht ⊢
  grind (splits := 80) (ematch := 10)


theorem orderThree {α : Type*} (A : Fin 3 → Fin 3 → α) (h : Latin A) : Rainbow A := by
  classical
  by_contra hn
  exact checked3 A (encode_latin A h) (encode_noRainbow A smallPerms3 hn)

end MaLatin
