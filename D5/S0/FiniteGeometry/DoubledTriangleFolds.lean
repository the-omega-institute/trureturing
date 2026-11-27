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

/-- At each quotient vertex, including each sheet interior vertex, the number
of black corners minus the number of white corners is divisible by three. -/
def Good (C : Coloring n) : Prop :=
  ∀ v s, (3 : Int) ∣ (black C (incidentCorners v s) - white C (incidentCorners v s))

/-- An edge is the up triangle and its omitted corner. A positive constant
coordinate gives two edges, one on each sheet. A zero constant coordinate
gives one seam edge, represented with sheet `false`. -/
abbrev Edge (n : ℕ) :=
  { p : Point n 1 × Axis × Bool // p.1.coord p.2.1 = 0 → p.2.2 = false }

instance (p : Point n 1 × Axis × Bool) :
    Decidable (p.1.coord p.2.1 = 0 → p.2.2 = false) := inferInstance

private def edge (p : Point n 1) (a : Axis) (s : Bool) : Edge n :=
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
  have hcorners : incidentCorners v false =
      [up false (r.U 0 (Nat.zero_le _)), up false ((r.next hw).U 0 (Nat.zero_le _)),
        down false (r.D 0 hw), up true (r.U 0 (Nat.zero_le _)),
        up true ((r.next hw).U 0 (Nat.zero_le _)), down true (r.D 0 hw)] := by
    simp [incidentCorners, Point.boundary, sheetCorners, atUp, atDown, bump, bumpPair,
      Point.coord, v, hw, Nat.succ_le_iff, Ring.U, Ring.D, Ring.next]
  rw [hcorners] at hv
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    h.1 false 0 (Nat.zero_le _), h.1 true 0 (Nat.zero_le _), h.2 false 0 hw,
    h.2 true 0 hw] at hv
  have hsum : (3 : Int) ∣ signed b * 4 +
      signed (C (up false ((r.next hw).U 0 (Nat.zero_le _)))) +
      signed (C (up true ((r.next hw).U 0 (Nat.zero_le _)))) := by
    convert hv using 1
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
  have hz : 0 < r.width - (j + 1) := by omega
  have hd : r.width - (j + 1) - 1 = r.width - (j + 1 + 1) := by omega
  have hd' : r.width - 1 - (j + 1) = r.width - (j + 1) - 1 := by omega
  have hu : r.width - 1 - j = r.width - (j + 1) := by omega
  have hcorners : incidentCorners v s =
      [up s (r.U (j + 1) (by omega)),
        up s ((r.next (by omega)).U j (by simp [Ring.next]; omega)),
        up s ((r.next (by omega)).U (j + 1) (by simp [Ring.next]; omega)),
        down s ((r.next (by omega)).D j (by simp [Ring.next]; omega)),
        down s (r.D (j + 1) hj), down s (r.D j (by omega))] := by
    simp [incidentCorners, Point.boundary, sheetCorners, atUp, atDown, bump, bumpPair,
      Point.coord, v, hz, Nat.ne_of_gt hz, Nat.succ_le_iff, Ring.U, Ring.D, Ring.next, hd, hd', hu]
  rw [hcorners] at hv
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    h.1 s (j + 1) (by omega), h.2 s (j + 1) hj, h.2 s j (by omega), hs] at hv
  apply aligned_from_four
  convert hv using 1
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

private theorem zero_side_folds {C : Coloring n} (hC : Good C) (hn : 0 < n)
    (hcard : (cutFolds C (.x, ⟨0, hn⟩)).card = 2)
    (p : Point n 1) (hp : p.x = 0) : Fold C (edge p .x false) := by
  let r : Ring n := ⟨0, n - 1, by omega⟩
  let p₀ := r.U 0 (Nat.zero_le _)
  let p₁ := r.U r.width (le_refl _)
  let e₀ := edge p₀ .y false
  let e₁ := edge p₁ .z false
  have h₀ : p₀.coord .y = 0 := rfl
  have h₁ : p₁.coord .z = 0 := Nat.sub_self _
  have opp₀ : C (up false p₀) ≠ C (up true p₀) := by
    exact corner_opposite (good_rotate hC) (Point.rotate.symm p₀) rfl rfl
  have opp₁ : C (up false p₁) ≠ C (up true p₁) := by
    exact corner_opposite (good_rotate (good_rotate hC))
      (Point.rotate.symm (Point.rotate.symm p₁)) (Nat.sub_self _) rfl
  have he₀ : e₀ ∈ cutFolds C r.cut :=
    mem_cutFolds.mpr ⟨by simpa only [e₀, Fold, edgeFaces_seam _ _ h₀] using opp₀,
      ring_crosses _ (by decide) _⟩
  have he₁ : e₁ ∈ cutFolds C r.cut :=
    mem_cutFolds.mpr ⟨by simpa only [e₁, Fold, edgeFaces_seam _ _ h₁] using opp₁,
      ring_crosses _ (by decide) _⟩
  have hne : e₀ ≠ e₁ := by
    intro h
    have : Axis.y = Axis.z := congrArg (fun e : Edge n => e.val.2.1) h
    cases this
  have hcut : cutFolds C r.cut = {e₀, e₁} := by
    apply (Finset.eq_of_subset_of_card_le (Finset.insert_subset he₀ (Finset.singleton_subset_iff.mpr he₁)) _).symm
    change (cutFolds C (.x, ⟨0, hn⟩)).card ≤ _
    rw [hcard]
    have hm : e₀ ∉ ({e₁} : Finset (Edge n)) := by simpa using hne
    simp [Finset.card_insert_of_notMem hm]
  have internal (e : Edge n) (hc : Crosses e r.cut)
      (hi : e.val.1.coord e.val.2.1 ≠ 0) : ¬ Fold C e := by
    intro hfold
    have he := mem_cutFolds.mpr ⟨hfold, hc⟩
    rw [hcut] at he
    rcases Finset.mem_insert.mp he with he | he
    · exact hi (he.symm ▸ h₀)
    · have he' := Finset.mem_singleton.mp he
      exact hi (he'.symm ▸ h₁)
  have colors (s : Bool) (j : ℕ) (hj : j ≤ r.width) :
      C (up s (r.U j hj)) = C (up s p₀) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hj' : j < r.width := by omega
      have hz := internal (edge (r.U j (by omega)) .z s) (ring_crosses _ (by decide) _)
        (by change r.width - j ≠ 0; omega)
      have hy := internal (edge (r.U (j+1) hj) .y s) (ring_crosses _ (by decide) _)
        (by change j+1 ≠ 0; omega)
      have hz' : C (up s (r.U j (by omega))) = C (down s (r.D j hj')) :=
        not_not.mp (by simpa only [Fold, ring_edge_z hj' s] using hz)
      have hy' : C (up s (r.U (j+1) hj)) = C (down s (r.D j hj')) :=
        not_not.mp (by simpa only [Fold, ring_edge_y hj' s] using hy)
      exact hy'.trans (hz'.symm.trans (ih (by omega)))
  have hpy : p.y ≤ r.width := by
    have := p.total
    change p.y ≤ n - 1
    omega
  have hp' : r.U p.y hpy = p := by
    apply Point.ext
    · exact hp.symm
    · rfl
    · have := p.total
      change n - 1 - p.y = p.z
      omega
  have hf := colors false p.y hpy
  have hb := colors true p.y hpy
  rw [hp'] at hf hb
  simp only [Fold, edgeFaces_seam _ .x hp]
  exact fun he => opp₀ (hf.symm.trans (he.trans hb))

private theorem every_seam_fold {C : Coloring n} (hC : Good C) (hn : 0 < n)
    (htotal : foldCount C = 3 * n) (p : Point n 1) (a : Axis) (h : p.coord a = 0) :
    Fold C (edge p a false) := by
  let cut : Cut n := (.x, ⟨0, hn⟩)
  cases a with
  | x => exact zero_side_folds hC hn (exact_cuts hC htotal cut) p h
  | y =>
    let C' : Coloring n := fun f => C (rotateFace f)
    have hc : (cutFolds (fun f => C' (rotateFace f)) cut).card = 2 := by
      rw [cut_card_rotate C', cut_card_rotate C]
      exact exact_cuts hC htotal _
    have hfold := zero_side_folds (good_rotate (good_rotate hC)) hn hc
      (Point.rotate.symm (Point.rotate.symm p)) h
    have hfold' := (fold_rotate (C := C')).mp hfold
    have hfold'' := (fold_rotate (C := C)).mp hfold'
    simpa [rotateEdge_mk, Axis.rotate] using hfold''
  | z =>
    have hc : (cutFolds (fun f => C (rotateFace f)) cut).card = 2 := by
      rw [cut_card_rotate C]
      exact exact_cuts hC htotal _
    have hfold := zero_side_folds (good_rotate hC) hn hc (Point.rotate.symm p) h
    apply fold_rotate.mp at hfold
    simpa [rotateEdge_mk, Axis.rotate] using hfold

private def seamPoint (k : Fin n) (a : Axis) : Point n 1 :=
  match a with
  | .x => ⟨0, k.val, n - (k.val + 1), by have := k.isLt; omega⟩
  | .y => ⟨n - (k.val + 1), 0, k.val, by have := k.isLt; omega⟩
  | .z => ⟨k.val, n - (k.val + 1), 0, by have := k.isLt; omega⟩

private theorem seamPoint_zero (k : Fin n) (a : Axis) : (seamPoint k a).coord a = 0 := by
  cases a <;> rfl

private def seamEmbedding : Cut n ↪ Edge n where
  toFun r := edge (seamPoint r.2 r.1) r.1 false
  inj' := by
    rintro ⟨a,k⟩ ⟨b,l⟩ h
    have hab : a = b := congrArg (fun e : Edge n => e.val.2.1) h
    subst b
    have hp : seamPoint k a = seamPoint l a := congrArg (fun e : Edge n => e.val.1) h
    apply congrArg (fun i : Fin n => (a, i))
    apply Fin.ext
    cases a
    · exact congrArg Point.y hp
    · exact congrArg Point.z hp
    · exact congrArg Point.x hp

private def seams : Finset (Edge n) := Finset.univ.map seamEmbedding

private theorem card_seams : (seams (n := n)).card = 3 * n := by
  rw [seams, Finset.card_map, Finset.card_univ, card_cut]

private theorem mem_seams {e : Edge n} : e ∈ seams ↔ e.val.1.coord e.val.2.1 = 0 := by
  constructor
  · intro h
    obtain ⟨⟨a,k⟩, _, rfl⟩ := Finset.mem_map.mp h
    exact seamPoint_zero k a
  · intro he
    let p := e.val.1
    let a := e.val.2.1
    have hs := e.property he
    have hr : edge p a false = e := by
      simpa only [hs] using edge_eta e
    have hex : ∃ k : Fin n, seamPoint k a = p := by
      have ht := p.total
      cases ha : a with
      | x =>
        have h : p.x = 0 := by
          have hp : p.coord a = 0 := he
          rw [ha] at hp
          exact hp
        refine ⟨⟨p.y, by omega⟩, Point.ext h.symm rfl ?_⟩
        change n - (p.y + 1) = p.z
        omega
      | y =>
        have h : p.y = 0 := by
          have hp : p.coord a = 0 := he
          rw [ha] at hp
          exact hp
        refine ⟨⟨p.z, by omega⟩, Point.ext ?_ h.symm rfl⟩
        change n - (p.z + 1) = p.x
        omega
      | z =>
        have h : p.z = 0 := by
          have hp : p.coord a = 0 := he
          rw [ha] at hp
          exact hp
        refine ⟨⟨p.x, by omega⟩, Point.ext rfl ?_ h.symm⟩
        change n - (p.x + 1) = p.y
        omega
    obtain ⟨k,hk⟩ := hex
    refine Finset.mem_map.mpr ⟨(a,k), Finset.mem_univ _, ?_⟩
    change edge (seamPoint k a) a false = e
    rw [hk, hr]

private theorem folds_eq_seams {C : Coloring n} (hC : Good C) (hn : 0 < n)
    (hupper : foldCount C ≤ 3 * n) : folds C = seams := by
  have hcount := le_antisymm hupper (minimum_bound hC)
  apply (Finset.eq_of_subset_of_card_le _ _).symm
  · intro e he
    have h := mem_seams.mp he
    have hs := e.property h
    have hf := every_seam_fold hC hn hcount e.val.1 e.val.2.1 h
    have hr : edge e.val.1 e.val.2.1 false = e := by
      simpa only [hs] using edge_eta e
    rw [hr] at hf
    simpa [folds] using hf
  · rw [card_seams, ← hcount]
    exact le_rfl

private def cornerUp (hn : 0 < n) : Point n 1 := ⟨n-1, 0, 0, by omega⟩

private theorem colors_of_unfolded_interior (C : Coloring n) (hn : 0 < n)
    (h : ∀ e : Edge n, e.val.1.coord e.val.2.1 ≠ 0 → ¬ Fold C e)
    (s : Bool) (t : Cell n) : C (s, t) = C (up s (cornerUp hn)) := by
  have adjacent (p : Point n 1) (a : Axis) (hp : p.coord a ≠ 0) :
      C (up s p) = C (down s (below p a hp)) := by
    have hf := h (edge p a s) hp
    exact not_not.mp (by simpa only [Fold, edgeFaces_inside _ _ hp] using hf)
  have allUp (p : Point n 1) : C (up s p) = C (up s (cornerUp hn)) := by
    induction heq : p.y + p.z using Nat.strong_induction_on generalizing p with
    | h dist ih =>
      have htotal := p.total
      by_cases hy : p.y = 0
      · by_cases hz : p.z = 0
        · have he : p = cornerUp hn := Point.ext (by change p.x = n-1; omega) hy hz
          rw [he]
        · let q : Point n 1 := ⟨p.x + 1, p.y, p.z - 1, by omega⟩
          have hq : q.coord .x ≠ 0 := by change p.x+1 ≠ 0; omega
          have hd : below p .z hz = below q .x hq := by
            apply Point.ext <;> simp [below, bump, q]
          exact (adjacent p .z hz).trans
            ((congrArg (fun a => C (down s a)) hd).trans
              ((adjacent q .x hq).symm.trans (ih _ (by change p.y + (p.z-1) < dist; omega) q rfl)))
      · let q : Point n 1 := ⟨p.x + 1, p.y - 1, p.z, by omega⟩
        have hq : q.coord .x ≠ 0 := by change p.x+1 ≠ 0; omega
        have hd : below p .y hy = below q .x hq := by
          apply Point.ext <;> simp [below, bump, q]
        exact (adjacent p .y hy).trans
          ((congrArg (fun a => C (down s a)) hd).trans
            ((adjacent q .x hq).symm.trans (ih _ (by change p.y - 1 + p.z < dist; omega) q rfl)))
  cases t with
  | inl p => exact allUp p
  | inr p =>
    let q : Point n 1 := ⟨p.x + 1, p.y, p.z, by have := p.total; omega⟩
    have hq : q.coord .x ≠ 0 := by change p.x+1 ≠ 0; omega
    have hd : below q .x hq = p := by apply Point.ext <;> simp [below, bump, q]
    exact (congrArg (fun a => C (down s a)) hd).symm.trans
      ((adjacent q .x hq).symm.trans (allUp q))

/-- Uniform color on the front sheet and the other color on the back sheet. -/
def twoSided (front : Bool) : Coloring n :=
  fun f => if f.1 then !front else front

private theorem twoSided_good (front : Bool) : Good (twoSided (n := n) front) := by
  intro v s
  rw [signed_balance]
  by_cases hx : v.x = 0 <;> by_cases hy : v.y = 0 <;> by_cases hz : v.z = 0 <;>
    have hx' : 0 < v.x ↔ v.x ≠ 0 := Nat.pos_iff_ne_zero <;>
    have hy' : 0 < v.y ↔ v.y ≠ 0 := Nat.pos_iff_ne_zero <;>
    have hz' : 0 < v.z ↔ v.z ≠ 0 := Nat.pos_iff_ne_zero <;>
    cases s <;> cases front <;>
    simp [incidentCorners, Point.boundary, sheetCorners, atUp, atDown, bump, bumpPair,
      Point.coord, hx, hy, hz, hx', hy', hz', Nat.succ_le_iff, signed, twoSided]

private theorem twoSided_folds (front : Bool) :
    foldCount (twoSided (n := n) front) = 3 * n := by
  have hset : folds (twoSided (n := n) front) = seams := by
    ext e
    rw [mem_seams]
    simp only [folds, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← edge_eta e]
    by_cases h : e.val.1.coord e.val.2.1 = 0
    · rw [Fold, edgeFaces_seam _ _ h]
      cases front <;> simp [twoSided, h, edge]
    · rw [Fold, edgeFaces_inside _ _ h]
      simp [twoSided, h, edge]
  rw [foldCount, hset, card_seams]

/-- A good coloring of minimum fold count is precisely one of the two
sheetwise uniform, opposite colorings. This gives the representative
with the identity triangulation symmetry and at most a global color swap. -/
theorem minimum_fold_uniqueness (hn : 0 < n) (C : Coloring n) :
    (Good C ∧ foldCount C = 3 * n) ↔
      ∃ front : Bool, (∀ t : Cell n, C (false, t) = front) ∧
        (∀ t : Cell n, C (true, t) = !front) := by
  constructor
  · rintro ⟨hC, hfold⟩
    have hs := folds_eq_seams hC hn (le_of_eq hfold)
    have hinside (e : Edge n) (h : e.val.1.coord e.val.2.1 ≠ 0) : ¬ Fold C e := by
      intro hf
      have he : e ∈ folds C := by simpa [folds] using hf
      rw [hs] at he
      exact h (mem_seams.mp he)
    let p := cornerUp hn
    have hcorner : C (up false p) ≠ C (up true p) := corner_opposite hC p rfl rfl
    have hcolors : C (up true p) = !C (up false p) := by
      cases ha : C (up false p) <;> cases hb : C (up true p) <;>
        simp [ha, hb] at hcorner ⊢
    refine ⟨C (up false p), ?_, ?_⟩
    · exact colors_of_unfolded_interior C hn hinside false
    · intro t
      exact (colors_of_unfolded_interior C hn hinside true t).trans hcolors
  · rintro ⟨front, hf, hb⟩
    have h : C = twoSided front := by
      funext f
      obtain ⟨s,t⟩ := f
      cases s
      · exact hf t
      · exact hb t
    rw [h]
    exact ⟨twoSided_good front, twoSided_folds front⟩

end D5.S0.FiniteGeometry.DoubledTriangleFolds
