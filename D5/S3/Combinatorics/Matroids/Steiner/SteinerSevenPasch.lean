/- GID: D5/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: A 19-point Steiner system has exactly the seven Pasches of one Fano subsystem. -/

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

end D5.S3.Combinatorics.Matroids.Steiner.SteinerSevenPasch
