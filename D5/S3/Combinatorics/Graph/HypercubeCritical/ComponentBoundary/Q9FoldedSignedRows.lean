/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSignedRows
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSignedRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Even-cut parity separates a six-site folded profile from every row pair. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic

/-! Exact signed row sums, vertex switching, and an even cut in a six-site profile. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows

/-- A bit at each ordered pair, with zero for a positive sign and one for a negative sign.
Only entries at neighbours are used in the row equations. -/
structure Signing (V : Type*) where
  bit : V → V → ZMod 2

/-- Adding endpoint bits is the action of the vertex switching group. -/
instance {V : Type*} : AddAction (V → ZMod 2) (Signing V) where
  vadd z s := ⟨fun u v => s.bit u v + (z u + z v)⟩
  zero_vadd s := by
    refine congrArg Signing.mk ?_
    funext u v
    change s.bit u v + ((0 : ZMod 2) + 0) = s.bit u v
    simp
  add_vadd z w s := by
    refine congrArg Signing.mk ?_
    funext u v
    change s.bit u v + ((z u + w u) + (z v + w v)) =
      (s.bit u v + (w u + w v)) + (z u + z v)
    ac_rfl

private def sign (b : ZMod 2) : ℤ := 1 - 2 * (b.val : ℤ)

/-- The exact integer sum in a row of the switched signing. -/
def rowSum {V : Type*} (neighbors : V → Finset V) (s : Signing V)
    (z : V → ZMod 2) (u : V) : ℤ :=
  ∑ v ∈ neighbors u, sign ((z +ᵥ s).bit u v)

/-- The graph Laplacian over the field of two elements. -/
def laplacian {V : Type*} (neighbors : V → Finset V)
    (z : V → ZMod 2) (u : V) : ZMod 2 :=
  ∑ v ∈ neighbors u, (z u + z v)

/-- Parity of the negative incidences in the selected rows. With symmetric,
loopless adjacency and symmetric signs, each internal edge contributes twice
and the sum is the parity of the negative edges crossing the cut. -/
def cutParity {V : Type*} (neighbors : V → Finset V) (s : Signing V)
    (cut : Finset V) : ZMod 2 :=
  ∑ u ∈ cut, ∑ v ∈ neighbors u, s.bit u v

private theorem row_parity {V : Type*} (neighbors : V → Finset V) (s : Signing V)
    (z : V → ZMod 2) (u : V) :
    (((((neighbors u).card : ℤ) - rowSum neighbors s z u) / 2 : ℤ) : ZMod 2) =
      (∑ v ∈ neighbors u, s.bit u v) + laplacian neighbors z u := by
  have hcount : rowSum neighbors s z u =
      (neighbors u).card - 2 * ∑ v ∈ neighbors u, (((z +ᵥ s).bit u v).val : ℤ) := by
    simp [rowSum, sign, Finset.sum_sub_distrib, Finset.mul_sum]
  have hhalf : (((neighbors u).card : ℤ) - rowSum neighbors s z u) / 2 =
      ∑ v ∈ neighbors u, (((z +ᵥ s).bit u v).val : ℤ) := by omega
  rw [hhalf, Int.cast_sum, laplacian, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [Int.cast_natCast]
  exact ZMod.natCast_zmod_val ((z +ᵥ s).bit u v)

private theorem laplacian_pairing {V : Type*} [Fintype V]
    (neighbors : V → Finset V) (symmetric : ∀ u v, v ∈ neighbors u ↔ u ∈ neighbors v)
    (x z : V → ZMod 2) :
    (∑ u, x u * laplacian neighbors z u) = ∑ u, z u * laplacian neighbors x u := by
  classical
  have sum_neighbors (u : V) (f : V → ZMod 2) :
      (∑ v ∈ neighbors u, f v) = ∑ v, if v ∈ neighbors u then f v else 0 := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc
    (∑ u, x u * laplacian neighbors z u) =
        ∑ u, ∑ v ∈ neighbors u, (x u * z u + x u * z v) := by
      simp only [laplacian, Finset.mul_sum, mul_add]
    _ = ∑ u, ∑ v ∈ neighbors u, (x u * z u + x v * z u) := by
      simp only [Finset.sum_add_distrib, add_right_inj]
      simp_rw [sum_neighbors]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
        simp only [symmetric v u]
    _ = _ := by
      simp only [laplacian, Finset.mul_sum, mul_add]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
        by rw [mul_comm (x u) (z u), mul_comm (x v) (z u)]

private theorem cutParity_vadd {V : Type*} [Finite V] [DecidableEq V]
    (neighbors : V → Finset V) (symmetric : ∀ u v, v ∈ neighbors u ↔ u ∈ neighbors v)
    (cut : Finset V) (evenCut : ∀ u,
      laplacian neighbors (fun v => if v ∈ cut then 1 else 0) u = 0)
    (s : Signing V) (z : V → ZMod 2) :
    cutParity neighbors (z +ᵥ s) cut = cutParity neighbors s cut := by
  let _ := Fintype.ofFinite V
  have hzero : ∑ u ∈ cut, laplacian neighbors z u = 0 := by
    calc
      _ = ∑ u, (if u ∈ cut then 1 else 0) * laplacian neighbors z u := by
        have hfilter : Finset.univ.filter (· ∈ cut) = cut := by simp
        conv_lhs => rw [← hfilter, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro u _
        split <;> simp_all
      _ = ∑ u, z u * laplacian neighbors (fun v => if v ∈ cut then 1 else 0) u :=
        laplacian_pairing neighbors symmetric _ _
      _ = 0 := by simp [evenCut]
  calc
    cutParity neighbors (z +ᵥ s) cut =
        cutParity neighbors s cut + ∑ u ∈ cut, laplacian neighbors z u := by
      unfold cutParity
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      rw [laplacian, ← Finset.sum_add_distrib]
      rfl
    _ = _ := by rw [hzero, add_zero]

/-- Exact integer row sums on an even cut prescribe the parity of negative incidences.
Only the rows indexed by the cut side are needed. -/
theorem signed_rows_even_cut {V : Type*} [Finite V] [DecidableEq V]
    (neighbors : V → Finset V) (symmetric : ∀ u v, v ∈ neighbors u ↔ u ∈ neighbors v)
    (cut : Finset V) (evenCut : ∀ u,
      laplacian neighbors (fun v => if v ∈ cut then 1 else 0) u = 0)
    (s : Signing V) (z : V → ZMod 2) (target : V → ℤ)
    (rows : ∀ u ∈ cut, rowSum neighbors s z u = target u) :
    (∑ u ∈ cut, (((((neighbors u).card : ℤ) - target u) / 2 : ℤ) : ZMod 2)) =
      cutParity neighbors s cut := by
  rw [← cutParity_vadd neighbors symmetric cut evenCut s z]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← rows u hu, row_parity, laplacian, ← Finset.sum_add_distrib]
  rfl

/-- Neighbours at the sites a, b, c, d, x, y in that order. -/
def sixNeighbors : Fin 6 → Finset (Fin 6)
  | 0 => {1, 3, 4}
  | 1 => {0, 2, 5}
  | 2 => {1, 3}
  | 3 => {0, 2}
  | 4 => {0}
  | 5 => {1}

/-- Negative edges are bc and by and their reversals. -/
def sixSigning : Signing (Fin 6) :=
  ⟨fun u v => if (u = 1 ∧ (v = 2 ∨ v = 5)) ∨
    (v = 1 ∧ (u = 2 ∨ u = 5)) then 1 else 0⟩

/-- The symmetric signed row targets, in vertex order. -/
def sixTarget : Fin 6 → ℤ
  | 0 => -1
  | 1 => -1
  | 2 => 2
  | 3 => 0
  | 4 => 1
  | 5 => -1

/-- The three rows whose cut parity obstructs a solution. -/
def sixCut : Finset (Fin 6) := {0, 2, 4}

private def fromMask (m : ℕ) (u : Fin 6) : ZMod 2 := if m.testBit u.val then 1 else 0

private def pairMask (u v : Fin 6) : ℕ :=
  match min u v, max u v with
  | 0, 1 => 24
  | 0, 2 => 18
  | 0, 3 | 0, 4 => 14
  | 0, 5 => 9
  | 1, 2 => 34
  | 1, 3 => 6
  | 1, 4 | 1, 5 => 0
  | 2, 5 => 12
  | 3, 5 => 1
  | 4, 5 => 0
  | _, 5 => 44
  | _, _ => 12

/-- Each pair of distinct exact rows is feasible, while the three indicated
rows already violate the switching-invariant parity constraint. -/
theorem six_row_separation :
    (∀ u v : Fin 6, u ≠ v → ∃ z : Fin 6 → ZMod 2,
      rowSum sixNeighbors sixSigning z u = sixTarget u ∧
      rowSum sixNeighbors sixSigning z v = sixTarget v) ∧
    ¬ ∃ z : Fin 6 → ZMod 2, ∀ u ∈ sixCut,
      rowSum sixNeighbors sixSigning z u = sixTarget u := by
  constructor
  · have witnesses : ∀ u v : Fin 6, u ≠ v →
        rowSum sixNeighbors sixSigning (fromMask (pairMask u v)) u = sixTarget u ∧
        rowSum sixNeighbors sixSigning (fromMask (pairMask u v)) v = sixTarget v := by decide
    exact fun u v huv => ⟨fromMask (pairMask u v), witnesses u v huv⟩
  · rintro ⟨z, rows⟩
    have symmetric : ∀ u v : Fin 6, v ∈ sixNeighbors u ↔ u ∈ sixNeighbors v := by decide
    have evenCut : ∀ u : Fin 6,
        laplacian sixNeighbors (fun v => if v ∈ sixCut then 1 else 0) u = 0 := by decide
    have parity := signed_rows_even_cut sixNeighbors symmetric sixCut evenCut
      sixSigning z sixTarget rows
    have mismatch :
        (∑ u ∈ sixCut, (((((sixNeighbors u).card : ℤ) - sixTarget u) / 2 : ℤ) : ZMod 2)) ≠
          cutParity sixNeighbors sixSigning sixCut := by decide
    exact mismatch parity

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows
