/- GID: D5/S3/Topology/CubicalChains/CubicalBox
   generality: G
   mirror-B: none(waiver:covered-by-planar-wilson-loop-area-law-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Open cubical boxes and the mod-two boundary of an axis-aligned rectangle. -/

import OmegaBuild.Commands
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic

/-! Omega original.

Open cubical boxes and the mod-two boundary of an axis-aligned rectangle.
A ray of links tests the parity of a projected plaquette fiber.
-/

compile_only_with_mathlib

set_option autoImplicit false

open Matrix BigOperators

namespace Omega.CubicalBox

variable {d : ℕ}

/-- The width of an axis counts its unit intervals. A width of zero leaves one vertex. -/
abbrev Vertex (w : Fin d → ℕ) := (i : Fin d) → Fin (w i + 1)

/-- A positive coordinate link, indexed by its direction and lower endpoint. -/
abbrev Link (w : Fin d → ℕ) :=
  {e : Fin d × Vertex w // (e.2 e.1).val < w e.1}

/-- A unit square, indexed by its ordered pair of distinct directions and lower corner. -/
abbrev Plaquette (w : Fin d → ℕ) :=
  {p : (Fin d × Fin d) × Vertex w // p.1.1 < p.1.2 ∧
    (p.2 p.1.1).val < w p.1.1 ∧ (p.2 p.1.2).val < w p.1.2}

variable {w : Fin d → ℕ}

private def advance (x : Vertex w) (i : Fin d) (h : (x i).val < w i) : Vertex w :=
  Function.update x i ⟨(x i).val + 1, Nat.succ_lt_succ h⟩

private theorem advance_val (x : Vertex w) (i k : Fin d) (h : (x i).val < w i) :
    (advance x i h k).val = (x k).val + if k = i then 1 else 0 := by
  by_cases hk : k = i
  · subst k
    simp [advance]
  · simp [advance, hk]

/-- The two links parallel to the first axis have `second = false`.
The upper link is shifted by one unit along the other axis. -/
def face (p : Plaquette w) (second upper : Bool) : Link w := by
  obtain ⟨⟨⟨i, j⟩, x⟩, hij, hi, hj⟩ := p
  cases second
  · refine ⟨(i, if upper then advance x j hj else x), ?_⟩
    cases upper <;> simp [advance_val, ne_of_lt hij, hi]
  · refine ⟨(j, if upper then advance x i hi else x), ?_⟩
    cases upper <;> simp [advance_val, ne_of_gt hij, hj]

private def linkBit (f e : Link w) : ZMod 2 := if e = f then 1 else 0

/-- The four geometric links of each plaquette, with coefficients in `ZMod 2`. -/
def incidence (w : Fin d → ℕ) : Matrix (Plaquette w) (Link w) (ZMod 2) :=
  fun p e => linkBit (face p false false) e + linkBit (face p false true) e +
    (linkBit (face p true false) e + linkBit (face p true true) e)

theorem incidence_mulVec (r : Link w → ZMod 2) (p : Plaquette w) :
    (incidence w *ᵥ r) p =
      r (face p false false) + r (face p false true) +
      (r (face p true false) + r (face p true true)) := by
  simp only [mulVec, dotProduct, incidence, add_mul, Finset.sum_add_distrib]
  simp [linkBit, ite_mul]

/-- A test cochain on links parallel to `i` at column `a`, through height `b` along `j`. -/
private def ray (i j : Fin d) (a b : ℕ) (e : Link w) : ZMod 2 :=
  if e.1.1 = i ∧ (e.1.2 i).val = a ∧ (e.1.2 j).val ≤ b then 1 else 0

private theorem ray_mulVec (i j : Fin d) (hij : i < j) (a b : ℕ) (p : Plaquette w) :
    (incidence w *ᵥ ray i j a b) p =
      if p.1.1 = (i, j) ∧ (p.1.2 i).val = a ∧ (p.1.2 j).val = b then 1 else 0 := by
  rw [incidence_mulVec]
  obtain ⟨⟨⟨k, l⟩, x⟩, hkl, hk, hl⟩ := p
  by_cases hki : k = i
  · subst k
    by_cases hlj : l = j
    · subst l
      dsimp [ray, face]
      simp [advance_val, ne_of_lt hij, ne_of_gt hij]
      split_ifs <;> first | rfl | omega
    · simp [ray, face, advance_val, ne_of_lt hkl, ne_of_gt hkl, Ne.symm hlj, hlj,
        ZModModule.add_self]
  · by_cases hli : l = i
    · subst l
      have hjk : j ≠ k := ne_of_gt (lt_trans hkl hij)
      simp [ray, face, advance_val, hki, Ne.symm hki, hjk, ZModModule.add_self]
    · simp [ray, face, hki, hli]

/-- The parity of a projected plaquette fiber, over all transverse coordinates. -/
def projectedCoefficient (i j : Fin d) (a b : ℕ) (S : Plaquette w → ZMod 2) : ZMod 2 :=
  ∑ p, if p.1.1 = (i, j) ∧ (p.1.2 i).val = a ∧ (p.1.2 j).val = b then S p else 0

/-- Pairing the boundary with a ray determines the parity over each projected square. -/
theorem projectedCoefficient_eq_of_boundary_eq (i j : Fin d) (hij : i < j) (a b : ℕ)
    {S U : Plaquette w → ZMod 2} (h : (incidence w)ᵀ *ᵥ S = (incidence w)ᵀ *ᵥ U) :
    projectedCoefficient i j a b S = projectedCoefficient i j a b U := by
  have pairing (V : Plaquette w → ZMod 2) :
      V ⬝ᵥ (incidence w *ᵥ ray i j a b) = projectedCoefficient i j a b V := by
    simp only [dotProduct, projectedCoefficient, ray_mulVec i j hij, mul_ite, mul_one, mul_zero]
  rw [← pairing S, ← pairing U, dotProduct_mulVec, dotProduct_mulVec,
    ← mulVec_transpose, ← mulVec_transpose, h]

/-- An open two-dimensional box has no nonzero plaquette chain with zero boundary. -/
theorem boundary_injective_2d (w : Fin 2 → ℕ) :
    Function.Injective (fun S : Plaquette w → ZMod 2 => (incidence w)ᵀ *ᵥ S) := by
  intro S U h
  funext p
  have isolate (V : Plaquette w → ZMod 2) :
      projectedCoefficient p.1.1.1 p.1.1.2 (p.1.2 p.1.1.1).val (p.1.2 p.1.1.2).val V = V p := by
    unfold projectedCoefficient
    have unique (q : Plaquette w) :
        (q.1.1 = p.1.1 ∧ (q.1.2 p.1.1.1).val = (p.1.2 p.1.1.1).val ∧
          (q.1.2 p.1.1.2).val = (p.1.2 p.1.1.2).val) ↔ q = p := by
      constructor
      · rintro ⟨hd, hi, hj⟩
        apply Subtype.ext
        refine Prod.ext hd (funext fun k => Fin.ext ?_)
        have hk : k = p.1.1.1 ∨ k = p.1.1.2 := by
          have := p.2.1
          grind [Fin.ext_iff, Fin.lt_def]
        rcases hk with rfl | rfl <;> assumption
      · rintro rfl
        simp
    simp [unique]
  simpa only [isolate] using
    projectedCoefficient_eq_of_boundary_eq _ _ p.2.1 (p.1.2 p.1.1.1).val (p.1.2 p.1.1.2).val h

/-- An axis-aligned rectangle based at a vertex, with transverse coordinates fixed. -/
structure Rectangle (w : Fin d → ℕ) where
  i : Fin d
  j : Fin d
  ordered : i < j
  corner : Vertex w
  width : ℕ
  height : ℕ
  fitsWidth : (corner i).val + width ≤ w i
  fitsHeight : (corner j).val + height ≤ w j

namespace Rectangle

variable (r : Rectangle w)

private def point (a : Fin (r.width + 1)) (b : Fin (r.height + 1)) : Vertex w :=
  fun k => ⟨(r.corner k).val + (if k = r.i then a.val else if k = r.j then b.val else 0), by
    have := r.fitsWidth
    have := r.fitsHeight
    split_ifs with hi hj
    · subst k
      omega
    · subst k
      omega
    · simpa using (r.corner k).isLt⟩

private def horizontal (a : Fin r.width) (b : Fin (r.height + 1)) : Link w :=
  ⟨(r.i, r.point a.castSucc b), by
    have := r.fitsWidth
    have := a.isLt
    simp only [point, ite_true, Fin.val_castSucc]
    omega⟩

private def vertical (a : Fin (r.width + 1)) (b : Fin r.height) : Link w :=
  ⟨(r.j, r.point a b.castSucc), by
    have := r.fitsHeight
    have := b.isLt
    simp only [point, ite_eq_right (ne_of_gt r.ordered), ite_true, Fin.val_castSucc]
    omega⟩

private def cells : Fin r.width × Fin r.height ↪ Plaquette w where
  toFun q := ⟨((r.i, r.j), r.point q.1.castSucc q.2.castSucc), r.ordered,
    (r.horizontal q.1 q.2.castSucc).2, (r.vertical q.1.castSucc q.2).2⟩
  inj' := by
    intro q q' h
    apply Prod.ext <;> apply Fin.ext
    · simpa [point] using congrArg (fun p : Plaquette w => (p.1.2 r.i).val) h
    · simpa [point, ne_of_gt r.ordered] using congrArg (fun p : Plaquette w => (p.1.2 r.j).val) h

/-- The indicator of precisely the unit squares of the rectangle. -/
def filling (p : Plaquette w) : ZMod 2 := if p ∈ Finset.univ.map r.cells then 1 else 0

/-- The Wilson loop as an edge chain over `ZMod 2`. -/
def loop : Link w → ZMod 2 := (incidence w)ᵀ *ᵥ r.filling

theorem filling_support_card :
    (Finset.univ.filter fun p => r.filling p ≠ 0).card = r.width * r.height := by
  have hs : (Finset.univ.filter fun p => r.filling p ≠ 0) = Finset.univ.map r.cells := by
    apply Finset.ext
    intro p
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, filling]
    by_cases hp : p ∈ Finset.univ.map r.cells
    · rw [ite_eq_left hp]
      exact iff_of_true one_ne_zero hp
    · rw [ite_eq_right hp]
      exact iff_of_false (not_not_intro rfl) hp
  rw [hs, Finset.card_map]
  simp

private theorem sum_filling (f : Plaquette w → ZMod 2) :
    (∑ p, f p * r.filling p) = ∑ q, f (r.cells q) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map r.cells)), Finset.sum_map]
  · have cell (q : Fin r.width × Fin r.height) : r.filling (r.cells q) = 1 := by simp [filling]
    simp only [cell, mul_one]
  · intro p _ hp
    simp [filling, hp]

/-- The four sides of the rectangle, added as edge chains. Coincident sides cancel. -/
def perimeter (e : Link w) : ZMod 2 :=
  (∑ a : Fin r.width, (linkBit (r.horizontal a 0) e +
    linkBit (r.horizontal a (Fin.last r.height)) e)) +
  (∑ b : Fin r.height, (linkBit (r.vertical 0 b) e +
    linkBit (r.vertical (Fin.last r.width) b) e))

private theorem sum_adjacent {n : ℕ} (f : Fin (n + 1) → ZMod 2) :
    (∑ a : Fin n, (f a.castSucc + f a.succ)) = f 0 + f (Fin.last n) := by
  have low : (∑ a, f a) = f (Fin.last n) + ∑ a : Fin n, f a.castSucc := by
    rw [Fin.univ_castSuccEmb, Finset.sum_cons, Finset.sum_map]
    rfl
  have high : (∑ a, f a) = f 0 + ∑ a : Fin n, f a.succ := by
    rw [Fin.univ_succ, Finset.sum_cons, Finset.sum_map]
    rfl
  rw [Finset.sum_add_distrib, eq_sub_of_add_eq' low.symm, eq_sub_of_add_eq' high.symm]
  simp only [sub_eq_add_neg, ZModModule.neg_eq_self]
  calc
    _ = ((∑ a, f a) + (∑ a, f a)) + (f 0 + f (Fin.last n)) := by ac_rfl
    _ = _ := by rw [ZModModule.add_self, zero_add]

/-- Adjacent squares contribute the same interior edge twice. Only the four side sums survive. -/
theorem loop_eq_perimeter : r.loop = r.perimeter := by
  funext e
  have horizontal_upper (a : Fin r.width) (b : Fin r.height) :
      face (r.cells (a, b)) false true = r.horizontal a b.succ := by
    apply Subtype.ext
    refine Prod.ext rfl (funext fun k => Fin.ext ?_)
    have bound : (r.point a.castSucc b.castSucc r.j).val < w r.j :=
      (r.cells (a, b)).2.2.2
    change (advance (r.point a.castSucc b.castSucc) r.j bound k).val =
      (r.point a.castSucc b.succ k).val
    rw [advance_val]
    simp only [point, Fin.val_castSucc, Fin.val_succ]
    have := ne_of_lt r.ordered
    split_ifs <;> omega
  have vertical_upper (a : Fin r.width) (b : Fin r.height) :
      face (r.cells (a, b)) true true = r.vertical a.succ b := by
    apply Subtype.ext
    refine Prod.ext rfl (funext fun k => Fin.ext ?_)
    have bound : (r.point a.castSucc b.castSucc r.i).val < w r.i :=
      (r.cells (a, b)).2.2.1
    change (advance (r.point a.castSucc b.castSucc) r.i bound k).val =
      (r.point a.succ b.castSucc k).val
    rw [advance_val]
    simp only [point, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  change (∑ p, incidence w p e * r.filling p) = r.perimeter e
  rw [r.sum_filling]
  simp only [incidence, horizontal_upper, vertical_upper]
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type_right]
  change (∑ a : Fin r.width, ∑ b : Fin r.height,
    (linkBit (r.horizontal a b.castSucc) e + linkBit (r.horizontal a b.succ) e)) +
    (∑ b : Fin r.height, ∑ a : Fin r.width,
      (linkBit (r.vertical a.castSucc b) e + linkBit (r.vertical a.succ b) e)) = r.perimeter e
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl ?_) (Finset.sum_congr rfl ?_)
  · intro a _
    exact sum_adjacent (fun b => linkBit (r.horizontal a b) e)
  · intro b _
    exact sum_adjacent (fun a => linkBit (r.vertical a b) e)

end Rectangle

end Omega.CubicalBox
