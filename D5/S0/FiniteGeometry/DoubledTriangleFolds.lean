/- GID: D5/S0/FiniteGeometry/DoubledTriangleFolds
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/DoubledTriangleFolds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minimum-fold good colorings of doubled triangles have uniformly opposite sheets. -/

module

public import Mathlib.Data.Fintype.BigOperators
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

end D5.S0.FiniteGeometry.DoubledTriangleFolds
