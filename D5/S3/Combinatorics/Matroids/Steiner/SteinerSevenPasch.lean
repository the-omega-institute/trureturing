/- GID: D5/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch.two_dimensional_claim; result=D5/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch.result; claim=D5/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch.two_dimensional_claim
   digest: A 19-point Steiner system has exactly the seven Pasches of one Fano subsystem. -/

import D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction
import Mathlib.Algebra.Group.Center
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Image
import Lean

/-! A finite Steiner loop for checking the dimension-two endpoint. -/

namespace D5.S3.Combinatorics.Matroids.Steiner.SteinerSevenPasch

abbrev Point := Fin 20

private def productTable : Vector (Vector Point 20) 20 :=
#v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
  #v[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18],
  #v[2, 3, 0, 1, 6, 7, 4, 5, 15, 16, 18, 17, 14, 19, 12, 8, 9, 11, 10, 13],
  #v[3, 2, 1, 0, 7, 6, 5, 4, 17, 18, 12, 19, 10, 15, 16, 13, 14, 8, 9, 11],
  #v[4, 5, 6, 7, 0, 1, 2, 3, 12, 14, 15, 18, 8, 16, 9, 10, 13, 19, 11, 17],
  #v[5, 4, 7, 6, 1, 0, 3, 2, 16, 11, 17, 9, 15, 18, 19, 12, 8, 10, 13, 14],
  #v[6, 7, 4, 5, 2, 3, 0, 1, 13, 17, 16, 15, 19, 8, 18, 11, 10, 9, 14, 12],
  #v[7, 6, 5, 4, 3, 2, 1, 0, 18, 12, 14, 13, 9, 11, 10, 17, 19, 15, 8, 16],
  #v[8, 9, 15, 17, 12, 16, 13, 18, 0, 1, 19, 14, 4, 6, 11, 2, 5, 3, 7, 10],
  #v[9, 8, 16, 18, 14, 11, 17, 12, 1, 0, 13, 5, 7, 10, 4, 19, 2, 6, 3, 15],
  #v[10, 11, 18, 12, 15, 17, 16, 14, 19, 13, 0, 1, 3, 9, 7, 4, 6, 5, 2, 8],
  #v[11, 10, 17, 19, 18, 9, 15, 13, 14, 5, 1, 0, 16, 7, 8, 6, 12, 2, 4, 3],
  #v[12, 13, 14, 10, 8, 15, 19, 9, 4, 7, 3, 16, 0, 1, 2, 5, 11, 18, 17, 6],
  #v[13, 12, 19, 15, 16, 18, 8, 11, 6, 10, 9, 7, 1, 0, 17, 3, 4, 14, 5, 2],
  #v[14, 15, 12, 16, 9, 19, 18, 10, 11, 4, 7, 8, 2, 17, 0, 1, 3, 13, 6, 5],
  #v[15, 14, 8, 13, 10, 12, 11, 17, 2, 19, 4, 6, 5, 3, 1, 0, 18, 7, 16, 9],
  #v[16, 17, 9, 14, 13, 8, 10, 19, 5, 2, 6, 12, 11, 4, 3, 18, 0, 1, 15, 7],
  #v[17, 16, 11, 8, 19, 10, 9, 15, 3, 6, 5, 2, 18, 14, 13, 7, 1, 0, 12, 4],
  #v[18, 19, 10, 9, 11, 13, 14, 8, 7, 3, 2, 4, 17, 5, 6, 16, 15, 12, 0, 1],
  #v[19, 18, 13, 11, 17, 14, 12, 16, 10, 15, 8, 3, 6, 2, 5, 9, 7, 4, 1, 0]]

private def pointProduct (x y : Point) : Point := productTable[x.val][y.val]

private def blockTable : Vector (Vector (Fin 57) 20) 20 :=
#v[
  #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #v[0, 0, 0, 0, 1, 1, 2, 2, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12],
  #v[0, 0, 0, 0, 3, 4, 3, 4, 13, 14, 15, 16, 17, 18, 17, 13, 14, 16, 15, 18],
  #v[0, 0, 0, 0, 5, 6, 6, 5, 19, 20, 21, 22, 21, 23, 24, 23, 24, 19, 20, 22],
  #v[0, 1, 3, 5, 0, 1, 3, 5, 25, 26, 27, 28, 25, 29, 26, 27, 29, 30, 28, 30],
  #v[0, 1, 4, 6, 1, 0, 6, 4, 31, 32, 33, 32, 34, 35, 36, 34, 31, 33, 35, 36],
  #v[0, 2, 3, 6, 3, 6, 0, 2, 37, 38, 39, 40, 41, 37, 42, 40, 39, 38, 42, 41],
  #v[0, 2, 4, 5, 5, 4, 2, 0, 43, 44, 45, 46, 44, 46, 45, 47, 48, 47, 43, 48],
  #v[0, 7, 13, 19, 25, 31, 37, 43, 0, 7, 49, 50, 25, 37, 50, 13, 31, 19, 43, 49],
  #v[0, 7, 14, 20, 26, 32, 38, 44, 7, 0, 51, 32, 44, 51, 26, 52, 14, 38, 20, 52],
  #v[0, 8, 15, 21, 27, 33, 39, 45, 49, 51, 0, 8, 21, 51, 45, 27, 39, 33, 15, 49],
  #v[0, 8, 16, 22, 28, 32, 40, 46, 50, 32, 8, 0, 53, 46, 50, 40, 53, 16, 28, 22],
  #v[0, 9, 17, 21, 25, 34, 41, 44, 25, 44, 21, 53, 0, 9, 17, 34, 53, 54, 54, 41],
  #v[0, 9, 18, 23, 29, 35, 37, 46, 37, 51, 51, 46, 9, 0, 55, 23, 29, 55, 35, 18],
  #v[0, 10, 17, 24, 26, 36, 42, 45, 50, 26, 45, 50, 17, 55, 0, 10, 24, 55, 42, 36],
  #v[0, 10, 13, 23, 27, 34, 40, 47, 13, 52, 27, 40, 34, 23, 10, 0, 56, 47, 56, 52],
  #v[0, 11, 14, 24, 29, 31, 39, 48, 31, 14, 39, 53, 53, 29, 24, 56, 0, 11, 56, 48],
  #v[0, 11, 16, 19, 30, 33, 38, 47, 19, 38, 33, 16, 54, 55, 55, 47, 11, 0, 54, 30],
  #v[0, 12, 15, 20, 28, 35, 42, 43, 43, 20, 15, 28, 54, 35, 42, 56, 56, 54, 0, 12],
  #v[0, 12, 18, 22, 30, 36, 41, 48, 49, 52, 49, 22, 41, 18, 36, 52, 48, 30, 12, 0]]

private def blockNumber (x y : Point) : Fin 57 := blockTable[x.val][y.val]

private def blocks : Vector (List Point) 57 :=
#v[
  [1, 2, 3],
  [1, 4, 5],
  [1, 6, 7],
  [2, 4, 6],
  [2, 5, 7],
  [3, 4, 7],
  [3, 5, 6],
  [1, 8, 9],
  [1, 10, 11],
  [1, 12, 13],
  [1, 14, 15],
  [1, 16, 17],
  [1, 18, 19],
  [2, 8, 15],
  [2, 9, 16],
  [2, 10, 18],
  [2, 11, 17],
  [2, 12, 14],
  [2, 13, 19],
  [3, 8, 17],
  [3, 9, 18],
  [3, 10, 12],
  [3, 11, 19],
  [3, 13, 15],
  [3, 14, 16],
  [4, 8, 12],
  [4, 9, 14],
  [4, 10, 15],
  [4, 11, 18],
  [4, 13, 16],
  [4, 17, 19],
  [5, 8, 16],
  [5, 9, 11],
  [5, 10, 17],
  [5, 12, 15],
  [5, 13, 18],
  [5, 14, 19],
  [6, 8, 13],
  [6, 9, 17],
  [6, 10, 16],
  [6, 11, 15],
  [6, 12, 19],
  [6, 14, 18],
  [7, 8, 18],
  [7, 9, 12],
  [7, 10, 14],
  [7, 11, 13],
  [7, 15, 17],
  [7, 16, 19],
  [8, 10, 19],
  [8, 11, 14],
  [9, 10, 13],
  [9, 15, 19],
  [11, 12, 16],
  [12, 17, 18],
  [13, 14, 17],
  [15, 16, 18]]

private def paschRows : Vector (List (Fin 57)) 7 :=
#v[
  [0, 1, 3, 6],
  [0, 1, 4, 5],
  [0, 2, 3, 5],
  [0, 2, 4, 6],
  [1, 2, 3, 4],
  [1, 2, 5, 6],
  [3, 4, 5, 6]]

private def representatives : Vector (Point × Point × Point) 7 :=
#v[
  (1, 6, 2),
  (1, 7, 2),
  (1, 4, 2),
  (1, 5, 2),
  (1, 2, 4),
  (1, 3, 4),
  (2, 3, 4)]

private def edgeBlocks (p q a : Point) : List (Fin 57) :=
  let b := pointProduct q a
  let c := pointProduct p b
  let d := pointProduct q c
  [blockNumber q a, blockNumber p b, blockNumber q c, blockNumber p d]

private def IsStart (p q a : Point) : Prop :=
  let b := pointProduct q a
  let c := pointProduct p b
  let d := pointProduct q c
  [0, p, q, a, b, c, d].Nodup ∧ pointProduct p d = a

instance (p q a : Point) : Decidable (IsStart p q a) := by
  unfold IsStart
  infer_instance

private theorem unit : ∀ x : Point, pointProduct 0 x = x := by decide
private theorem comm : ∀ x y : Point, pointProduct x y = pointProduct y x := by decide
private theorem invol : ∀ x y : Point, pointProduct x (pointProduct x y) = y := by decide

private theorem read_block :
    ∀ p q x : Point, p ≠ 0 → q ≠ 0 → p ≠ q →
      (x ∈ blocks[(blockNumber p q).val] ↔ x ∈ [p, q, pointProduct p q]) := by
  decide +kernel

private theorem covers_pasch :
    ∀ p q a : Point, IsStart p q a → ∃ i : Fin 7,
      ∀ j : Fin 57, j ∈ edgeBlocks p q a ↔ j ∈ paschRows[i.val] := by
  decide +kernel

private theorem read_pasch :
    ∀ i : Fin 7,
      let (p, q, a) := representatives[i.val]
      IsStart p q a ∧ ∀ j : Fin 57, j ∈ edgeBlocks p q a ↔ j ∈ paschRows[i.val] := by
  decide +kernel

private theorem associator : ∀ p : Point, p ≠ 0 →
    ∃ x y : Point, pointProduct (pointProduct p x) y ≠ pointProduct p (pointProduct x y) := by
  decide +kernel

private theorem fano_product :
    ∀ p q : Point, p.val < 8 → q.val < 8 →
      (pointProduct p q).val = p.val ^^^ q.val := by
  decide +kernel

private theorem fano_support :
    ∀ i : Fin 7, ∀ t : Fin 57, t ∈ paschRows[i.val] →
      ∀ x : Point, x ∈ blocks[t.val] → x.val < 8 := by
  decide +kernel

private theorem every_binary_plane_has_zero_combination (a b c : BitVec 2) :
    a = 0 ∨ b = 0 ∨ c = 0 ∨ a ^^^ b = 0 ∨ a ^^^ c = 0 ∨ b ^^^ c = 0 ∨
      a ^^^ b ^^^ c = 0 := by
  revert a b c
  decide

local instance : Mul Point := ⟨pointProduct⟩

private theorem centreless : Set.center Point = {0} := by
  ext p
  rw [Set.mem_center_iff, Set.mem_singleton_iff]
  constructor
  · intro central
    by_contra h
    obtain ⟨x, y, failure⟩ := associator p h
    exact failure (central.left_assoc x y).symm
  · rintro rfl
    have right (p : Point) : p * 0 = p := (comm p 0).trans (unit p)
    exact ⟨fun p => comm 0 p, fun x y => by simp only [show ∀ p : Point, 0 * p = p from unit],
      fun x y => by simp only [right]⟩

private def blockSet (i : Fin 57) : Set Point := {x | x ∈ blocks[i.val]}

private noncomputable def paschSet (i : Fin 7) : Finset (Set Point) := by
  classical
  exact (paschRows[i.val]).toFinset.image blockSet

private noncomputable def startPasch (p q a : Point) : Finset (Set Point) := by
  classical
  let b := q * a
  let c := p * b
  let d := q * c
  exact {{q, a, b}, {p, b, c}, {q, c, d}, {p, d, a}}

private theorem to_pasch_set {p q a : Point} {i : Fin 7} (h : IsStart p q a)
    (reads : ∀ j : Fin 57, j ∈ edgeBlocks p q a ↔ j ∈ paschRows[i.val]) :
    startPasch p q a = paschSet i := by
  classical
  let b := pointProduct q a
  let c := pointProduct p b
  let d := pointProduct q c
  have distinct : [0, p, q, a, b, c, d].Nodup := h.1
  have close : pointProduct p d = a := h.2
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
    not_false_eq_true, List.nodup_nil, and_true] at distinct
  have read {u v : Point} (hu : u ≠ 0) (hv : v ≠ 0) (hne : u ≠ v) :
      blockSet (blockNumber u v) = {u, v, pointProduct u v} := by
    ext x
    simpa [blockSet] using read_block u v x hu hv hne
  have one := read (u := q) (v := a) (by tauto) (by tauto) (by tauto)
  have two := read (u := p) (v := b) (by tauto) (by tauto) (by tauto)
  have three := read (u := q) (v := c) (by tauto) (by tauto) (by tauto)
  have four := read (u := p) (v := d) (by tauto) (by tauto) (by tauto)
  have codes : (edgeBlocks p q a).toFinset = (paschRows[i.val]).toFinset :=
    Finset.ext fun j => by simpa only [List.mem_toFinset] using reads j
  unfold paschSet
  rw [← codes]
  change startPasch p q a = ([blockNumber q a, blockNumber p b, blockNumber q c,
    blockNumber p d].toFinset).image blockSet
  change {{q, a, b}, {p, b, c}, {q, c, d}, {p, d, a}} = _
  rw [List.toFinset_cons, List.toFinset_cons, List.toFinset_cons, List.toFinset_cons,
    List.toFinset_nil, Finset.image_insert, Finset.image_insert, Finset.image_insert,
    Finset.image_insert, Finset.image_empty, one, two, three, four, close]
  rfl

private theorem represented (p q a : Point) (h : IsStart p q a) :
    ∃ i : Fin 7, startPasch p q a = paschSet i := by
  obtain ⟨i, hi⟩ := covers_pasch p q a h
  exact ⟨i, to_pasch_set h hi⟩

private abbrev Fibre := Fin 2 → ZMod 2

private theorem fibre_twice (v : Fibre) : v + v = 0 := by
  have twice : ∀ a : ZMod 2, a + a = 0 := by decide
  funext i
  exact twice (v i)

private theorem fibre_relation :
    ∀ x y z : Fibre, x = 0 ∨ y = 0 ∨ z = 0 ∨ x + y = 0 ∨ x + z = 0 ∨
      y + z = 0 ∨ x + y + z = 0 := by
  decide

private def rowValue (labels : Set Point → Fibre) (i : Fin 7) : Fibre :=
  (paschRows[i.val].map (labels ∘ blockSet)).sum

private theorem some_row_zero (labels : Set Point → Fibre) :
    ∃ i : Fin 7, rowValue labels i = 0 := by
  let f (i : Fin 57) := labels (blockSet i)
  let x := f 0 + f 1 + f 3 + f 6
  let y := f 0 + f 1 + f 4 + f 5
  let z := f 0 + f 2 + f 3 + f 5
  have hxy : x + y = rowValue labels 6 := by
    change (f 0 + f 1 + f 3 + f 6) + (f 0 + f 1 + f 4 + f 5) =
      f 3 + (f 4 + (f 5 + (f 6 + 0)))
    calc
      _ = (f 3 + (f 4 + (f 5 + (f 6 + 0)))) + (f 0 + f 0) + (f 1 + f 1) := by abel
      _ = _ := by simp [fibre_twice]
  have hxz : x + z = rowValue labels 5 := by
    change (f 0 + f 1 + f 3 + f 6) + (f 0 + f 2 + f 3 + f 5) =
      f 1 + (f 2 + (f 5 + (f 6 + 0)))
    calc
      _ = (f 1 + (f 2 + (f 5 + (f 6 + 0)))) + (f 0 + f 0) + (f 3 + f 3) := by abel
      _ = _ := by simp [fibre_twice]
  have hyz : y + z = rowValue labels 4 := by
    change (f 0 + f 1 + f 4 + f 5) + (f 0 + f 2 + f 3 + f 5) =
      f 1 + (f 2 + (f 3 + (f 4 + 0)))
    calc
      _ = (f 1 + (f 2 + (f 3 + (f 4 + 0)))) + (f 0 + f 0) + (f 5 + f 5) := by abel
      _ = _ := by simp [fibre_twice]
  have hxyz : x + y + z = rowValue labels 3 := by
    rw [hxy]
    change (f 3 + (f 4 + (f 5 + (f 6 + 0)))) + (f 0 + f 2 + f 3 + f 5) =
      f 0 + (f 2 + (f 4 + (f 6 + 0)))
    calc
      _ = (f 0 + (f 2 + (f 4 + (f 6 + 0)))) + (f 3 + f 3) + (f 5 + f 5) := by abel
      _ = _ := by simp [fibre_twice]
  rcases fibre_relation x y z with h | h | h | h | h | h | h
  · refine ⟨0, ?_⟩
    change f 0 + (f 1 + (f 3 + (f 6 + 0))) = 0
    simpa [x, add_assoc] using h
  · refine ⟨1, ?_⟩
    change f 0 + (f 1 + (f 4 + (f 5 + 0))) = 0
    simpa [y, add_assoc] using h
  · refine ⟨2, ?_⟩
    change f 0 + (f 2 + (f 3 + (f 5 + 0))) = 0
    simpa [z, add_assoc] using h
  · exact ⟨6, hxy.symm.trans h⟩
  · exact ⟨5, hxz.symm.trans h⟩
  · exact ⟨4, hyz.symm.trans h⟩
  · exact ⟨3, hxyz.symm.trans h⟩

private theorem representative_nodup :
    ∀ i : Fin 7,
      let (p, q, a) := representatives[i.val]
      (edgeBlocks p q a).Nodup ∧ (paschRows[i.val]).Nodup := by decide

private theorem representative_values (labels : Set Point → Fibre) (i : Fin 7) :
    let (p, q, a) := representatives[i.val]
    ((edgeBlocks p q a).map (labels ∘ blockSet)).sum = rowValue labels i := by
  rcases data : representatives[i.val] with ⟨p, q, a⟩
  have pair := representative_nodup i
  rw [data] at pair
  have reads := read_pasch i
  rw [data] at reads
  exact (((List.perm_ext_iff_of_nodup pair.1 pair.2).mpr reads.2).map _).sum_eq

open Function SimpleGraph
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension (extensionMul factor)
open D5.S3.Combinatorics.Matroids.Steiner.SteinerPaschSwitchCount (loopPivotMatchings)
open D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction
  (switchCount switchCount_eq improve)

private theorem representative_outside :
    ∀ i : Fin 7, let (p, q, a) := representatives[i.val]
      a ∉ ([0, p, q, pointProduct p q] : List Point) := by decide

private theorem special_closed :
    ∀ p q x : Point, x ∈ [0, p, q, pointProduct p q] →
      pointProduct p x ∈ [0, p, q, pointProduct p q] ∧
        pointProduct q x ∈ [0, p, q, pointProduct p q] := by decide +kernel

private theorem stationary_on_zero_row {p q a : Point}
    (labels : Set Point → Fibre) (h : IsStart p q a)
    (zero : ((edgeBlocks p q a).map (labels ∘ blockSet)).sum = 0) :
    letI := extensionMul 0 labels
    (fun u : Point × Fibre => (p, 0) * ((q, 0) * u))^[2] (a, 0) = (a, 0) := by
  let _ := extensionMul 0 labels
  let b := q * a
  let c := p * b
  let d := q * c
  have close : p * d = a := h.2
  have distinct : [0, p, q, a, b, c, d].Nodup := h.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
    not_false_eq_true, List.nodup_nil, and_true] at distinct
  have step (u v : Point) (hu : u ≠ 0) (hv : v ≠ 0) (different : u ≠ v) (z : Fibre) :
      (u, 0) * (v, z) = (u * v, z + labels (blockSet (blockNumber u v))) := by
    have triple : blockSet (blockNumber u v) = ({u, v, u * v} : Set Point) := by
      ext x
      change (x ∈ blocks[(blockNumber u v).val]) ↔ x ∈ ({u, v, pointProduct u v} : Set Point)
      simpa using read_block u v x hu hv different
    change (u * v, 0 + z + factor 0 labels u v) = _
    rw [zero_add, factor, ite_eq_right (by tauto), triple]
    rfl
  let f (u v : Point) := labels (blockSet (blockNumber u v))
  have first := step q a (by tauto) (by tauto) (by tauto) 0
  have second := step p b (by tauto) (by tauto) (by tauto) (0 + f q a)
  have third := step q c (by tauto) (by tauto) (by tauto) (0 + f q a + f p b)
  have fourth := step p d (by tauto) (by tauto) (by tauto) (0 + f q a + f p b + f q c)
  change (p, 0) * ((q, 0) * ((p, 0) * ((q, 0) * (a, (0 : Fibre))))) = (a, 0)
  rw [first, second, third, fourth, close]
  congr 1
  change f q a + (f p b + (f q c + (f p d + 0))) = 0 at zero
  simpa only [zero_add, add_zero, add_assoc] using zero

private theorem representative_beats (labels : Set Point → Fibre) :
    ∃ p q : Point, p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧
      ∃ better : Set Point → Fibre, switchCount 0 p q labels < switchCount 0 p q better := by
  classical
  obtain ⟨i, vanishes⟩ := some_row_zero labels
  rcases data : representatives[i.val] with ⟨p,q,a⟩
  have computed := read_pasch i
  have outside := representative_outside i
  have value := representative_values labels i
  rw [data] at computed outside value
  have start : IsStart p q a := computed.1
  have distinct := start.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
    not_false_eq_true, List.nodup_nil, and_true] at distinct
  have hp : p ≠ 0 := by tauto
  have hq : q ≠ 0 := by tauto
  have hpq : p ≠ q := by tauto
  let M := loopPivotMatchings 0 p q unit comm invol hp hq hpq
  have edges (u v : Point) : M.graph.Adj u v ↔ p * u = v ∨ q * u = v := Iff.rfl
  have notReach : ¬ M.graph.Reachable 0 a := by
    have stays {u : Point} (path : M.graph.Reachable 0 u) :
        u ∈ ([0, p, q, pointProduct p q] : List Point) := by
      rw [reachable_iff_reflTransGen] at path
      induction path with
      | refl => simp
      | @tail u v _ adjacent hu =>
        rcases (edges u v).mp adjacent with rfl | rfl
        · exact (special_closed p q u hu).1
        · exact (special_closed p q u hu).2
    exact fun path => outside (stays path)
  have differentComponent : M.graph.connectedComponentMk a ≠ M.graph.connectedComponentMk 0 :=
    fun same => notReach (ConnectedComponent.exact same.symm)
  have fixedPoint := stationary_on_zero_row labels start (value.trans vanishes)
  obtain ⟨better, good⟩ := improve M.graph 0 p q a labels unit comm invol centreless
    hp hq hpq edges differentComponent fixedPoint
  refine ⟨p, q, hp, hq, hpq, better, ?_⟩
  rw [switchCount_eq 0 p q labels unit comm invol centreless,
    switchCount_eq 0 p q better unit comm invol centreless]
  exact good

private noncomputable def pasches {L : Type} [Mul L] (e : L) : Set (Finset (Set L)) := by
  classical
  exact {T | ∃ p q a b c d : L, [e, p, q, a, b, c, d].Nodup ∧
    q * a = b ∧ p * b = c ∧ q * c = d ∧ p * d = a ∧
    T = {{q, a, b}, {p, b, c}, {q, c, d}, {p, d, a}}}


private theorem first_blocks_separated :
    ∀ i j : Fin 57, i.val < 7 → j.val < 7 → i ≠ j →
      ∃ x : Point, ¬ (x ∈ blocks[i.val] ↔ x ∈ blocks[j.val]) := by decide +kernel

private theorem row_ids_small :
    ∀ i : Fin 7, ∀ j : Fin 57, j ∈ paschRows[i.val] → j.val < 7 := by decide

private theorem rows_separated :
    ∀ i j : Fin 7, i ≠ j → ∃ t : Fin 57, t ∈ paschRows[i.val] ∧ t ∉ paschRows[j.val] := by
  decide

private theorem pasch_set_injective : Function.Injective paschSet := by
  classical
  intro i j equal
  by_contra different
  obtain ⟨t, present, absent⟩ := rows_separated i j different
  have mem : blockSet t ∈ paschSet i :=
    Finset.mem_image.mpr ⟨t, List.mem_toFinset.mpr present, rfl⟩
  rw [equal] at mem
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp mem
  have used := List.mem_toFinset.mp hu
  have same : u = t := by
    by_contra h
    obtain ⟨x, separates⟩ :=
      first_blocks_separated u t (row_ids_small j u used) (row_ids_small i t present) h
    exact separates (Iff.of_eq (congrArg (fun S : Set Point => x ∈ S) he))
  exact absent (same ▸ used)

private theorem seven_pasches : (pasches (0 : Point)).ncard = 7 := by
  classical
  let listed := (Finset.univ : Finset (Fin 7)).image paschSet
  have classified : pasches (0 : Point) = (listed : Set _) := by
    ext T
    constructor
    · rintro ⟨p, q, a, b, c, d, distinct, hab, hbc, hcd, hda, eq⟩
      subst b
      subst c
      subst d
      obtain ⟨i, hi⟩ := represented p q a ⟨distinct, hda⟩
      change T = startPasch p q a at eq
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (eq.trans hi).symm⟩
    · intro member
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (show T ∈ listed from member)
      rcases data : representatives[i.val] with ⟨p, q, a⟩
      have checks := read_pasch i
      rw [data] at checks
      let b := q * a
      let c := p * b
      let d := q * c
      exact ⟨p, q, a, b, c, d, checks.1.1, rfl, rfl, rfl, checks.1.2,
        (to_pasch_set checks.1 checks.2).symm⟩
  rw [classified, Set.ncard_coe_finset, Finset.card_image_of_injective _ pasch_set_injective]
  simp

/-- The dimension-two endpoint would guarantee a common maximum with at most seven Pasches. -/
def two_dimensional_claim : Prop :=
  ∀ (L : Type) [Finite L] [Mul L] (e : L),
    (∀ x, e * x = x) → (∀ x y : L, x * y = y * x) →
    (∀ x y : L, x * (x * y) = y) → Set.center L = {e} →
    (pasches e).ncard ≤ 7 →
    ∃ labels : Set L → Fibre, ∀ p q : L, p ≠ e → q ≠ e → p ≠ q →
      ∀ other : Set L → Fibre, switchCount e p q other ≤ switchCount e p q labels

/-- The 19-point instance refutes the inclusive seven-Pasch bound in fibre dimension two. -/
theorem result : ¬ two_dimensional_claim := by
  classical
  intro claim
  have cap : (pasches (0 : Point)).ncard ≤ 7 := seven_pasches.le
  obtain ⟨labels, realizes⟩ := claim Point 0 unit comm invol centreless cap
  obtain ⟨p, q, hp, hq, hpq, better, improved⟩ := representative_beats labels
  exact (not_lt_of_ge (realizes p q hp hq hpq better)) improved

end D5.S3.Combinatorics.Matroids.Steiner.SteinerSevenPasch
