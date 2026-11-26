/- GID: D5/S0/FiniteGeometry/DoubledTriangleFolds
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/DoubledTriangleFolds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minimum-fold good colorings of doubled triangles have uniformly opposite sheets. -/

module

public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import OmegaBuild.Commands

/-! # Fold minima of doubled triangular subdivisions -/

compile_only_with_mathlib

noncomputable section

@[expose] public section

set_option autoImplicit false

namespace D5.S0.FiniteGeometry.DoubledTriangleFolds

open scoped BigOperators

/-- The three barycentric axes, with their cyclic order. -/
inductive Axis where
  | x | y | z
  deriving DecidableEq

instance : Fintype Axis where
  elems := {.x, .y, .z}
  complete a := by cases a <;> simp

private def Axis.rotate : Axis ≃ Axis where
  toFun | .x => .z | .y => .x | .z => .y
  invFun | .x => .y | .y => .z | .z => .x
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

/-- A triple of nonnegative barycentric coordinates summing to `n - offset`.
The additive constraint excludes down faces when `n = 1`. -/
@[ext] structure Point (n offset : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  total : x + y + z + offset = n
  deriving DecidableEq

instance (n d : ℕ) : Fintype (Point n d) :=
  Fintype.ofInjective (fun p : Point n d =>
    ((⟨p.x, by have := p.total; omega⟩ : Fin (n+1)),
     (⟨p.y, by have := p.total; omega⟩ : Fin (n+1)))) (by
      intro p q h
      have hx := congrArg (fun a : Fin (n+1) × Fin (n+1) => a.1.val) h
      have hy := congrArg (fun a : Fin (n+1) × Fin (n+1) => a.2.val) h
      change p.x = q.x at hx
      change p.y = q.y at hy
      have := p.total
      have := q.total
      exact Point.ext hx hy (by omega))

variable {n d : ℕ}

def Point.coord (p : Point n d) : Axis → ℕ
  | .x => p.x
  | .y => p.y
  | .z => p.z

private def Point.rotate : Point n d ≃ Point n d where
  toFun p := ⟨p.y, p.z, p.x, by have := p.total; omega⟩
  invFun p := ⟨p.z, p.x, p.y, by have := p.total; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem Point.rotate_coord (p : Point n d) (a : Axis) :
    (Point.rotate p).coord (Axis.rotate a) = p.coord a := by cases a <;> rfl

/-- A unit cell in one planar subdivision. -/
abbrev Cell (n : ℕ) := Point n 1 ⊕ Point n 2

/-- The sheet is `false` on the front and `true` on the back. -/
abbrev Face (n : ℕ) := Bool × Cell n

abbrev Coloring (n : ℕ) := Face n → Bool

abbrev up (s : Bool) (p : Point n 1) : Face n := (s, .inl p)
abbrev down (s : Bool) (p : Point n 2) : Face n := (s, .inr p)

private def rotateFace : Face n ≃ Face n :=
  (Equiv.refl Bool).prodCongr (Equiv.sumCongr Point.rotate Point.rotate)

/-- Boundary points belong to both sheets after gluing. -/
def Point.boundary (p : Point n 0) : Prop := p.x = 0 ∨ p.y = 0 ∨ p.z = 0

instance (p : Point n 0) : Decidable p.boundary := by unfold Point.boundary; infer_instance

def bump (a b : Axis) : ℕ := if a = b then 1 else 0
def bumpPair (a b : Axis) : ℕ := if a = b then 0 else 1

/-- An up corner is indexed by the coordinate increased by one. A down corner
is indexed by the coordinate omitted from the two increases. -/
def cornerVertex (t : Cell n) (a : Axis) : Point n 0 :=
  match t with
  | .inl p =>
    ⟨p.x + bump a .x, p.y + bump a .y, p.z + bump a .z,
      by have := p.total; cases a <;> simp [bump] <;> omega⟩
  | .inr p =>
    ⟨p.x + bumpPair a .x, p.y + bumpPair a .y, p.z + bumpPair a .z,
      by have := p.total; cases a <;> simp [bumpPair] <;> omega⟩

def atUp (v : Point n 0) (s : Bool) (a : Axis) : Option (Face n) :=
  if h : 0 < v.coord a then
    some (up s ⟨v.x - bump a .x, v.y - bump a .y, v.z - bump a .z,
      by have := v.total; cases a <;> simp [bump, Point.coord] at * <;> omega⟩)
  else none

def atDown (v : Point n 0) (s : Bool) (a : Axis) : Option (Face n) :=
  if h : bumpPair a .x ≤ v.x ∧ bumpPair a .y ≤ v.y ∧ bumpPair a .z ≤ v.z then
    some (down s ⟨v.x - bumpPair a .x, v.y - bumpPair a .y, v.z - bumpPair a .z,
      by have := v.total; cases a <;> simp [bumpPair] at * <;> omega⟩)
  else none

def sheetCorners (v : Point n 0) (s : Bool) : List (Face n) :=
  [atUp v s .x, atUp v s .y, atUp v s .z,
    atDown v s .x, atDown v s .y, atDown v s .z].filterMap id

/-- The incident face corners. Boundary points combine both sheets. Each
interior point checks its own sheet. -/
def incidentCorners (v : Point n 0) (s : Bool) : List (Face n) :=
  if v.boundary then sheetCorners v false ++ sheetCorners v true else sheetCorners v s

def black (C : Coloring n) (faces : List (Face n)) : Int :=
  faces.countP C

def white (C : Coloring n) (faces : List (Face n)) : Int :=
  faces.countP (fun f => !C f)

/-- At each glued vertex, the number of black corners minus the number of
white corners is divisible by three. -/
def Good (C : Coloring n) : Prop :=
  ∀ v s, (3 : Int) ∣ (black C (incidentCorners v s) - white C (incidentCorners v s))

/-- An edge is the up triangle and its omitted corner. A positive constant
coordinate gives two edges, one on each sheet. A zero constant coordinate
gives one seam edge, represented with sheet `false`. -/
abbrev Edge (n : ℕ) :=
  { p : Point n 1 × Axis × Bool // p.1.coord p.2.1 = 0 → p.2.2 = false }

instance (p : Point n 1 × Axis × Bool) :
    Decidable (p.1.coord p.2.1 = 0 → p.2.2 = false) := inferInstance

def edge (p : Point n 1) (a : Axis) (s : Bool) : Edge n :=
  ⟨(p, a, if p.coord a = 0 then false else s), by simp +contextual⟩

def below (p : Point n 1) (a : Axis) (h : p.coord a ≠ 0) : Point n 2 :=
  ⟨p.x - bump a .x, p.y - bump a .y, p.z - bump a .z,
    by have := p.total; cases a <;> simp [bump, Point.coord] at * <;> omega⟩

/-- The two faces incident to the edge. -/
def edgeFaces (e : Edge n) : Face n × Face n :=
  let (p, a, s) := e.val
  (up s p, if h : p.coord a = 0 then up true p else down s (below p a h))

/-- An edge is folded when its incident faces have different colors. -/
def Fold (C : Coloring n) (e : Edge n) : Prop :=
  C (edgeFaces e).1 ≠ C (edgeFaces e).2

instance (C : Coloring n) (e : Edge n) : Decidable (Fold C e) := by
  unfold Fold
  infer_instance

def folds (C : Coloring n) : Finset (Edge n) := Finset.univ.filter (Fold C)

/-- The total number of folds in the glued subdivision. -/
def foldCount (C : Coloring n) : ℕ := (folds C).card

private abbrev Cut (n : ℕ) := Axis × Fin n

private def Crosses (e : Edge n) (r : Cut n) : Prop :=
  e.val.2.1 ≠ r.1 ∧ e.val.1.coord r.1 = r.2.val

private instance (e : Edge n) (r : Cut n) : Decidable (Crosses e r) := by
  unfold Crosses
  infer_instance

private def cutFolds (C : Coloring n) (r : Cut n) : Finset (Edge n) :=
  (folds C).filter (fun e => Crosses e r)

private theorem mem_cutFolds {C : Coloring n} {r : Cut n} {e : Edge n} :
    e ∈ cutFolds C r ↔ Fold C e ∧ Crosses e r := by
  simp [cutFolds, folds]

private theorem edgeFaces_seam (p : Point n 1) (a : Axis) (h : p.coord a = 0)
    (s : Bool) : edgeFaces (edge p a s) = (up false p, up true p) := by
  simp [edgeFaces, edge, h]

private theorem edgeFaces_inside (p : Point n 1) (a : Axis) (h : p.coord a ≠ 0)
    (s : Bool) : edgeFaces (edge p a s) = (up s p, down s (below p a h)) := by
  simp [edgeFaces, edge, h]

private def signed (b : Bool) : Int := if b then 1 else -1

private theorem signed_balance (C : Coloring n) (fs : List (Face n)) :
    black C fs - white C fs = (fs.map (fun f => signed (C f))).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases h : C f <;> simp [black, white, h, signed] at ih ⊢ <;> omega

private theorem good_balance {C : Coloring n} (hC : Good C) (v : Point n 0) (s : Bool) :
    (3 : Int) ∣ ((incidentCorners v s).map (fun f => signed (C f))).sum := by
  rw [← signed_balance]
  exact hC v s

private theorem opposite_from_two {a b : Bool}
    (h : (3 : Int) ∣ signed a + signed b) : a ≠ b := by
  cases a <;> cases b <;> simp [signed] at h ⊢

private theorem aligned_from_four {a b c : Bool}
    (h : (3 : Int) ∣ signed a * 4 + signed b + signed c) : b = a ∧ c = a := by
  cases a <;> cases b <;> cases c <;> simp [signed] at h ⊢

private structure Ring (n : ℕ) where
  level : ℕ
  width : ℕ
  size : level + width + 1 = n

private def Ring.next (r : Ring n) (hw : 0 < r.width) : Ring n :=
  ⟨r.level + 1, r.width - 1, by have := r.size; omega⟩

private def Ring.U (r : Ring n) (j : ℕ) (hj : j ≤ r.width) : Point n 1 :=
  ⟨r.level, j, r.width - j, by have := r.size; omega⟩

private def Ring.D (r : Ring n) (j : ℕ) (hj : j < r.width) : Point n 2 :=
  ⟨r.level, j, r.width - (j+1), by have := r.size; omega⟩

private def Ring.Mono (C : Coloring n) (r : Ring n) (b : Bool) : Prop :=
  (∀ (s : Bool) (j : ℕ) (hj : j ≤ r.width), C (up s (r.U j hj)) = b) ∧
  (∀ (s : Bool) (j : ℕ) (hj : j < r.width), C (down s (r.D j hj)) = b)

private theorem corner_opposite {C : Coloring n} (hC : Good C) (p : Point n 1)
    (hy : p.y = 0) (hz : p.z = 0) : C (up false p) ≠ C (up true p) := by
  let v : Point n 0 := ⟨p.x + 1, 0, 0, by have := p.total; omega⟩
  have hv := good_balance hC v false
  have hp : (⟨p.x, 0, 0, by have := p.total; omega⟩ : Point n 1) = p :=
    Point.ext rfl hy.symm hz.symm
  apply opposite_from_two
  simpa [incidentCorners, Point.boundary, sheetCorners, atUp, atDown, bump, bumpPair,
    Point.coord, v, hp] using hv

private theorem ring_next_start {C : Coloring n} {r : Ring n} {b : Bool} (hC : Good C)
    (h : r.Mono C b) (hw : 0 < r.width) :
    ∀ s, C (up s ((r.next hw).U 0 (Nat.zero_le _))) = b := by
  let v : Point n 0 := ⟨r.level + 1, 0, r.width, by have := r.size; omega⟩
  have hv := good_balance hC v false
  have h₁ := h.1 false 0 (Nat.zero_le _)
  have h₂ := h.1 true 0 (Nat.zero_le _)
  have h₃ := h.2 false 0 hw
  have h₄ := h.2 true 0 hw
  simp [Ring.U, Ring.D] at h₁ h₂ h₃ h₄
  simp [incidentCorners, Point.boundary, sheetCorners, atUp, atDown, bump, bumpPair,
    Point.coord, v, hw, Nat.succ_le_iff, h₁, h₂, h₃, h₄] at hv
  have hsum : (3 : Int) ∣ signed b * 4 +
      signed (C (up false ((r.next hw).U 0 (Nat.zero_le _)))) +
      signed (C (up true ((r.next hw).U 0 (Nat.zero_le _)))) := by
    convert hv using 1
    simp [Ring.next, Ring.U]
    omega
  have hcol := aligned_from_four hsum
  intro s
  cases s
  · exact hcol.1
  · exact hcol.2

private theorem ring_next_step {C : Coloring n} {r : Ring n} {b : Bool} (hC : Good C)
    (h : r.Mono C b) {j : ℕ} (hj : j+1 < r.width) (s : Bool)
    (hs : C (up s ((r.next (by omega)).U j (by simp [Ring.next]; omega))) = b) :
    C (down s ((r.next (by omega)).D j (by simp [Ring.next]; omega))) = b ∧
    C (up s ((r.next (by omega)).U (j+1) (by simp [Ring.next]; omega))) = b := by
  let v : Point n 0 := ⟨r.level + 1, j+1, r.width - (j+1), by have := r.size; omega⟩
  have hv := good_balance hC v s
  have h₁ := h.1 s (j+1) (by omega)
  have h₂ := h.2 s (j+1) hj
  have h₃ := h.2 s j (by omega)
  have hz : 0 < r.width - (j+1) := by omega
  have hd : r.width - (j+1) - 1 = r.width - (j+1+1) := by omega
  have hd' : r.width - 1 - (j+1) = r.width - (j+1) - 1 := by omega
  have hu : r.width - 1 - j = r.width - (j+1) := by omega
  simp [Ring.U, Ring.D] at h₁ h₂ h₃
  simp [Ring.U, Ring.next, hu] at hs
  simp [incidentCorners, Point.boundary, sheetCorners, atUp, atDown, bump, bumpPair,
    Point.coord, v, hz, Nat.ne_of_gt hz, hd, Nat.succ_le_iff, h₁, h₂, h₃, hs] at hv
  apply aligned_from_four
  convert hv using 1
  simp [Ring.next, Ring.U, Ring.D, hd', hd]
  omega

private theorem ring_next_mono {C : Coloring n} {r : Ring n} {b : Bool} (hC : Good C)
    (h : r.Mono C b) (hw : 0 < r.width) : (r.next hw).Mono C b := by
  have hu (s : Bool) (j : ℕ) (hj : j ≤ (r.next hw).width) :
      C (up s ((r.next hw).U j hj)) = b := by
    induction j with
    | zero => exact ring_next_start hC h hw s
    | succ j ih =>
      have hj' : j + 1 < r.width := by
        simp [Ring.next] at hj
        omega
      exact (ring_next_step hC h hj' s (ih (by omega))).2
  refine ⟨hu, ?_⟩
  intro s j hj
  have hj' : j + 1 < r.width := by simp [Ring.next] at hj; omega
  exact (ring_next_step hC h hj' s (hu s j (by omega))).1

private theorem ring_not_mono {C : Coloring n} (hC : Good C) (r : Ring n) (b : Bool) :
    ¬ r.Mono C b := by
  intro h
  induction w : r.width using Nat.strong_induction_on generalizing r with
  | h w ih =>
    by_cases hw : 0 < r.width
    · exact ih (r.next hw).width (by simp [Ring.next]; omega) (r.next hw)
        (ring_next_mono hC h hw) rfl
    · let p := r.U 0 (Nat.zero_le _)
      have hne := corner_opposite hC p rfl (by change r.width - 0 = 0; omega)
      exact hne ((h.1 false 0 (Nat.zero_le _)).trans (h.1 true 0 (Nat.zero_le _)).symm)

private def Ring.cut (r : Ring n) : Cut n :=
  (.x, ⟨r.level, by have := r.size; omega⟩)

private theorem edge_axis (p : Point n 1) (a : Axis) (s : Bool) :
    (edge p a s).val.2.1 = a := rfl

private theorem edge_sheet (p : Point n 1) (a : Axis) (s : Bool) :
    (edge p a s).val.2.2 = if p.coord a = 0 then false else s := rfl

private def xTraversal (e : Edge n) : Face n × Face n :=
  if (decide (e.val.2.1 = .z) != e.val.2.2) then edgeFaces e
  else (edgeFaces e).swap

private theorem ring_edge_z {r : Ring n} {j : ℕ} (hj : j < r.width) (s : Bool) :
    edgeFaces (edge (r.U j (by omega)) .z s) =
      (up s (r.U j (by omega)), down s (r.D j hj)) := by
  rw [edgeFaces_inside _ _ (by change r.width - j ≠ 0; omega)]
  congr 2

private theorem ring_edge_y {r : Ring n} {j : ℕ} (hj : j < r.width) (s : Bool) :
    edgeFaces (edge (r.U (j+1) (by omega)) .y s) =
      (up s (r.U (j+1) (by omega)), down s (r.D j hj)) := by
  rw [edgeFaces_inside _ _ (by change j+1 ≠ 0; omega)]
  congr 2

private theorem ring_crosses {r : Ring n} {j : ℕ} (hj : j ≤ r.width)
    {a : Axis} (ha : a ≠ .x) (s : Bool) : Crosses (edge (r.U j hj) a s) r.cut :=
  ⟨ha, rfl⟩

private theorem ring_mono_of_monotone (r : Ring n) (F : Face n → ℕ)
    (h : ∀ e, Crosses e r.cut → F (xTraversal e).1 ≤ F (xTraversal e).2) :
    ∃ m, (∀ (s : Bool) j (hj : j ≤ r.width), F (up s (r.U j hj)) = m) ∧
      (∀ (s : Bool) j (hj : j < r.width), F (down s (r.D j hj)) = m) := by
  let u (s : Bool) (j : ℕ) (hj : j ≤ r.width) := F (up s (r.U j hj))
  let d (s : Bool) (j : ℕ) (hj : j < r.width) := F (down s (r.D j hj))
  have front (j : ℕ) (hj : j < r.width) :
      u false j (by omega) ≤ d false j hj ∧ d false j hj ≤ u false (j+1) (by omega) := by
    have hz : (r.U j (by omega)).coord .z ≠ 0 := by change r.width - j ≠ 0; omega
    have hy : (r.U (j+1) (by omega)).coord .y ≠ 0 := by change j+1 ≠ 0; omega
    constructor
    · simpa [xTraversal, edge_axis, edge_sheet, hz, ring_edge_z hj false, u, d] using
        h (edge (r.U j (by omega)) .z false) (ring_crosses _ (by decide) _)
    · simpa [xTraversal, edge_axis, edge_sheet, hy, ring_edge_y hj false, u, d] using
        h (edge (r.U (j+1) (by omega)) .y false) (ring_crosses _ (by decide) _)
  have back (j : ℕ) (hj : j < r.width) :
      u true (j+1) (by omega) ≤ d true j hj ∧ d true j hj ≤ u true j (by omega) := by
    have hz : (r.U j (by omega)).coord .z ≠ 0 := by change r.width - j ≠ 0; omega
    have hy : (r.U (j+1) (by omega)).coord .y ≠ 0 := by change j+1 ≠ 0; omega
    constructor
    · simpa [xTraversal, edge_axis, edge_sheet, hy, ring_edge_y hj true, u, d] using
        h (edge (r.U (j+1) (by omega)) .y true) (ring_crosses _ (by decide) _)
    · simpa [xTraversal, edge_axis, edge_sheet, hz, ring_edge_z hj true, u, d] using
        h (edge (r.U j (by omega)) .z true) (ring_crosses _ (by decide) _)
  have first : u true 0 (Nat.zero_le _) ≤ u false 0 (Nat.zero_le _) := by
    have hy : (r.U 0 (Nat.zero_le _)).coord .y = 0 := rfl
    simpa [xTraversal, edge_axis, edge_sheet, hy, edgeFaces_seam _ .y hy, u] using
      h (edge (r.U 0 (Nat.zero_le _)) .y false) (ring_crosses _ (by decide) _)
  have last : u false r.width (le_refl _) ≤ u true r.width (le_refl _) := by
    have hz : (r.U r.width (le_refl _)).coord .z = 0 := Nat.sub_self _
    simpa [xTraversal, edge_axis, edge_sheet, hz, edgeFaces_seam _ .z hz, u] using
      h (edge (r.U r.width (le_refl _)) .z false) (ring_crosses _ (by decide) _)
  have order (i j : ℕ) (hij : i ≤ j) (hj : j ≤ r.width) :
      u false i (hij.trans hj) ≤ u false j hj ∧
      u true j hj ≤ u true i (hij.trans hj) := by
    induction hij with
    | refl => exact ⟨le_refl _, le_refl _⟩
    | @step j hij ih =>
      have h₁ := ih (by omega)
      have hf := front j (by omega)
      have hb := back j (by omega)
      exact ⟨h₁.1.trans (hf.1.trans hf.2), hb.1.trans (hb.2.trans h₁.2)⟩
  have allU (s : Bool) (j : ℕ) (hj : j ≤ r.width) :
      u s j hj = u false 0 (Nat.zero_le _) := by
    have h₁ := order 0 j (Nat.zero_le _) hj
    have h₂ := order j r.width hj (le_refl _)
    have h₃ := order 0 r.width (Nat.zero_le _) (le_refl _)
    cases s
    · exact le_antisymm (h₂.1.trans (last.trans (h₃.2.trans first))) h₁.1
    · exact le_antisymm (h₁.2.trans first) (h₃.1.trans (last.trans h₂.2))
  refine ⟨u false 0 (Nat.zero_le _), allU, ?_⟩
  intro s j hj
  cases s
  · have hf := front j hj
    exact le_antisymm (hf.2.trans (allU false (j+1) (by omega)).le)
      ((allU false j (by omega)).ge.trans hf.1)
  · have hb := back j hj
    exact le_antisymm (hb.2.trans (allU true j (by omega)).le)
      ((allU true (j+1) (by omega)).ge.trans hb.1)

private theorem ring_has_descent {C : Coloring n} (r : Ring n) (h : ∀ b, ¬ r.Mono C b) :
    ∃ e, Crosses e r.cut ∧ (C (xTraversal e).2).toNat < (C (xTraversal e).1).toNat := by
  by_contra! h'
  obtain ⟨m, hu, hd⟩ := ring_mono_of_monotone r (fun f => (C f).toNat) h'
  let p := r.U 0 (Nat.zero_le _)
  have hm : (C (up false p)).toNat = m := hu false 0 (Nat.zero_le _)
  apply h (C (up false p))
  have injective : Function.Injective Bool.toNat := by
    intro a b hab
    cases a <;> cases b <;> simp_all
  exact ⟨fun s j hj => injective ((hu s j hj).trans hm.symm),
    fun s j hj => injective ((hd s j hj).trans hm.symm)⟩

private theorem ring_two_folds {C : Coloring n} (hC : Good C) (r : Ring n) :
    2 ≤ (cutFolds C r.cut).card := by
  obtain ⟨e, he, hdec⟩ := ring_has_descent r (ring_not_mono hC r)
  let opposite : Coloring n := fun f => !C f
  have hOpp (b : Bool) : ¬ r.Mono opposite b := by
    intro h
    apply ring_not_mono hC r (!b)
    constructor
    · intro s j hj
      have hc := h.1 s j hj
      exact (Bool.not_not _).symm.trans (congrArg Bool.not hc)
    · intro s j hj
      have hc := h.2 s j hj
      exact (Bool.not_not _).symm.trans (congrArg Bool.not hc)
  obtain ⟨f, hf, hinc'⟩ := ring_has_descent r hOpp
  have hinc : (C (xTraversal f).1).toNat < (C (xTraversal f).2).toNat := by
    dsimp [opposite] at hinc'
    cases h₁ : C (xTraversal f).1 <;> cases h₂ : C (xTraversal f).2 <;>
      simp [h₁, h₂] at hinc' ⊢
  have fold_of_ne (g : Edge n) (hneq : C (xTraversal g).1 ≠ C (xTraversal g).2) :
      Fold C g := by
    unfold xTraversal at hneq
    split at hneq
    · exact hneq
    · exact Ne.symm hneq
  have he' := mem_cutFolds.mpr ⟨fold_of_ne e (fun heq => by rw [heq] at hdec; omega), he⟩
  have hf' := mem_cutFolds.mpr ⟨fold_of_ne f (fun hfq => by rw [hfq] at hinc; omega), hf⟩
  exact Finset.one_lt_card.mpr ⟨e, he', f, hf', fun hEq => by rw [hEq] at hdec; omega⟩

private theorem Point.rotate_boundary (v : Point n 0) :
    (Point.rotate v).boundary ↔ v.boundary := by
  simp [Point.rotate, Point.boundary, or_left_comm, or_comm]

private theorem atUp_rotate (v : Point n 0) (s : Bool) (a : Axis) :
    atUp (Point.rotate v) s (Axis.rotate a) = (atUp v s a).map rotateFace := by
  cases a <;> simp [atUp, Point.rotate, Axis.rotate, Point.coord, bump, rotateFace]

private theorem atDown_rotate (v : Point n 0) (s : Bool) (a : Axis) :
    atDown (Point.rotate v) s (Axis.rotate a) = (atDown v s a).map rotateFace := by
  cases a <;>
    simp [atDown, Point.rotate, Axis.rotate, bumpPair, rotateFace, and_comm]

private def optionSign (C : Coloring n) (f : Option (Face n)) : Int :=
  f.elim 0 (fun f => signed (C f))

private theorem sum_filterMap (C : Coloring n) (fs : List (Option (Face n))) :
    ((fs.filterMap id).map (fun f => signed (C f))).sum = (fs.map (optionSign C)).sum := by
  induction fs with
  | nil => rfl
  | cons a fs ih =>
    change ((fs.filterMap (fun f => f)).map _).sum = _ at ih
    cases a <;> simp [optionSign, ih]

private theorem sheet_balance_rotate (C : Coloring n) (v : Point n 0) (s : Bool) :
    ((sheetCorners v s).map (fun f => signed (C (rotateFace f)))).sum =
    ((sheetCorners (Point.rotate v) s).map (fun f => signed (C f))).sum := by
  have h (f : Option (Face n)) :
      optionSign C (f.map rotateFace) = optionSign (fun a => C (rotateFace a)) f := by
    cases f <;> rfl
  have hx : Axis.rotate .x = .z := rfl
  have hy : Axis.rotate .y = .x := rfl
  have hz : Axis.rotate .z = .y := rfl
  have hUx := atUp_rotate v s .x
  have hUy := atUp_rotate v s .y
  have hUz := atUp_rotate v s .z
  have hDx := atDown_rotate v s .x
  have hDy := atDown_rotate v s .y
  have hDz := atDown_rotate v s .z
  simp only [hx, hy, hz] at hUx hUy hUz hDx hDy hDz
  simp only [sheetCorners, sum_filterMap, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hUx, hUy, hUz, hDx, hDy, hDz, h]
  -- The cyclic permutation changes only the order of summation.
  omega

private theorem good_rotate {C : Coloring n} (hC : Good C) :
    Good (fun f => C (rotateFace f)) := by
  intro v s
  rw [signed_balance]
  have hv := good_balance hC (Point.rotate v) s
  by_cases hb : v.boundary <;>
    simpa [incidentCorners, Point.rotate_boundary, hb, List.map_append, List.sum_append,
      sheet_balance_rotate] using hv

private def rotateEdge : Edge n ≃ Edge n where
  toFun e := ⟨(Point.rotate e.val.1, Axis.rotate e.val.2.1, e.val.2.2), by
    intro h
    apply e.property
    exact (Point.rotate_coord _ _).symm.trans h⟩
  invFun e := ⟨(Point.rotate.symm e.val.1, Axis.rotate.symm e.val.2.1, e.val.2.2), by
    intro h
    apply e.property
    have he := Point.rotate_coord (Point.rotate.symm e.val.1) (Axis.rotate.symm e.val.2.1)
    simpa using he.trans h⟩
  left_inv e := by
    apply Subtype.ext
    simp
  right_inv e := by
    apply Subtype.ext
    simp

private theorem rotateEdge_mk (p : Point n 1) (a : Axis) (s : Bool) :
    rotateEdge (edge p a s) = edge (Point.rotate p) (Axis.rotate a) s := by
  apply Subtype.ext
  simp [rotateEdge, edge, Point.rotate_coord]

private theorem edge_eta (e : Edge n) : edge e.val.1 e.val.2.1 e.val.2.2 = e := by
  rcases e with ⟨⟨p, a, s⟩, he⟩
  apply Subtype.ext
  by_cases h : p.coord a = 0
  · have hs : s = false := he h
    subst s
    simp [edge, h]
  · simp [edge, h]

private theorem below_rotate (p : Point n 1) (a : Axis) (h : p.coord a ≠ 0) :
    below (Point.rotate p) (Axis.rotate a) (by simpa only [Point.rotate_coord] using h) =
      Point.rotate (below p a h) := by
  cases a <;> rfl

private theorem edgeFaces_rotate (e : Edge n) :
    edgeFaces (rotateEdge e) = ((rotateFace (edgeFaces e).1), rotateFace (edgeFaces e).2) := by
  rw [← edge_eta e, rotateEdge_mk]
  by_cases h : e.val.1.coord e.val.2.1 = 0
  · rw [edgeFaces_seam _ _ h, edgeFaces_seam _ _ (by simpa only [Point.rotate_coord] using h)]
    rfl
  · rw [edgeFaces_inside _ _ h,
      edgeFaces_inside _ _ (by simpa only [Point.rotate_coord] using h), below_rotate]
    rfl

private theorem fold_rotate {C : Coloring n} {e : Edge n} :
    Fold (fun f => C (rotateFace f)) e ↔ Fold C (rotateEdge e) := by
  simp only [Fold, edgeFaces_rotate]

private def rotateCut : Cut n ≃ Cut n := Axis.rotate.prodCongr (Equiv.refl (Fin n))

private theorem crosses_rotate {e : Edge n} {r : Cut n} :
    Crosses (rotateEdge e) (rotateCut r) ↔ Crosses e r := by
  simp [Crosses, rotateEdge, rotateCut, Point.rotate_coord]

private theorem cut_card_rotate (C : Coloring n) (r : Cut n) :
    (cutFolds (fun f => C (rotateFace f)) r).card = (cutFolds C (rotateCut r)).card := by
  apply Finset.card_bij (fun e _ => rotateEdge e)
  · intro e he
    have h := mem_cutFolds.mp he
    exact mem_cutFolds.mpr ⟨fold_rotate.mp h.1, crosses_rotate.mpr h.2⟩
  · intro _ _ _ _ h
    exact rotateEdge.injective h
  · intro e he
    refine ⟨rotateEdge.symm e, ?_, rotateEdge.apply_symm_apply e⟩
    have h := mem_cutFolds.mp he
    exact mem_cutFolds.mpr ⟨fold_rotate.mpr (by simpa using h.1),
      crosses_rotate.mp (by simpa using h.2)⟩

private theorem every_cut_two_folds {C : Coloring n} (hC : Good C) (cut : Cut n) :
    2 ≤ (cutFolds C cut).card := by
  obtain ⟨a, k⟩ := cut
  let r : Ring n := ⟨k.val, n - (k.val + 1), by have := k.isLt; omega⟩
  have hr : r.cut = (.x, k) := rfl
  cases a with
  | x => exact hr ▸ ring_two_folds hC r
  | y =>
    have h := ring_two_folds (good_rotate (good_rotate hC)) r
    rw [cut_card_rotate (fun f => C (rotateFace f)), cut_card_rotate C, hr] at h
    exact h
  | z =>
    have h := ring_two_folds (good_rotate hC) r
    rw [cut_card_rotate C, hr] at h
    exact h

private theorem axis_univ : (Finset.univ : Finset Axis) = {.x, .y, .z} := rfl

private theorem card_cut : Fintype.card (Cut n) = 3 * n := by
  have hc : Fintype.card Axis = 3 := by decide
  simp [Fintype.card_prod, hc]

private theorem edge_cut_sum (e : Edge n) :
    (∑ r : Cut n, if Crosses e r then (1 : ℕ) else 0) = 2 := by
  rw [Fintype.sum_prod_type]
  have h (a : Axis) : (∑ k : Fin n, if Crosses e (a, k) then (1 : ℕ) else 0) =
      if e.val.2.1 ≠ a then 1 else 0 := by
    by_cases ha : e.val.2.1 = a
    · simp [Crosses, ha]
    · let k : Fin n := ⟨e.val.1.coord a, by
        have := e.val.1.total
        cases a <;> simp [Point.coord] <;> omega⟩
      rw [Finset.sum_eq_single k]
      · simp [Crosses, ha, k]
      · intro j _ hj
        have hj' : e.val.1.coord a ≠ j.val := fun h => hj (Fin.ext h.symm)
        simp [Crosses, hj']
      · simp
  simp only [h]
  rw [axis_univ]
  cases e.val.2.1 <;> simp

private theorem cut_fold_sum (C : Coloring n) :
    (∑ r : Cut n, (cutFolds C r).card) = foldCount C * 2 := by
  simp only [cutFolds, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [edge_cut_sum, foldCount]

private theorem minimum_bound {C : Coloring n} (hC : Good C) : 3 * n ≤ foldCount C := by
  have h : (∑ _ : Cut n, (2 : ℕ)) ≤ ∑ r : Cut n, (cutFolds C r).card :=
    Finset.sum_le_sum (fun r _ => every_cut_two_folds hC r)
  rw [cut_fold_sum] at h
  simp only [Finset.sum_const, Finset.card_univ, card_cut, Nat.nsmul_eq_mul] at h
  omega

private theorem exact_cuts {C : Coloring n} (hC : Good C) (hcount : foldCount C = 3 * n)
    (r : Cut n) : (cutFolds C r).card = 2 := by
  have hmin := every_cut_two_folds hC r
  by_contra hne
  have hlt : (∑ _ : Cut n, (2 : ℕ)) < ∑ q : Cut n, (cutFolds C q).card :=
    Finset.sum_lt_sum (fun q _ => every_cut_two_folds hC q)
      ⟨r, Finset.mem_univ _, by omega⟩
  rw [cut_fold_sum, hcount] at hlt
  simp only [Finset.sum_const, Finset.card_univ, card_cut, Nat.nsmul_eq_mul] at hlt
  omega

end D5.S0.FiniteGeometry.DoubledTriangleFolds
