/- GID: D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.claim; result=D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.result; claim=D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.claim
   digest: Refutes the conjectured determinant formula of M. Kade, arXiv:2509.03416v1, section 2.3, for the partition function of the six-vertex model in a box with arrow-reflecting walls: at M = 1, crossing parameter p = 2, spectral parameters x = 2, y = 3 and all boundary parameters 1, the partition function is -400400/81 while the formula gives -7150. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: the kernel evaluates the box
  partition function over the rationals, a sum over all 4096 arrow configurations of the 1 x 1
  box, to -400400/81 (`hZ`); the rational cast is a ring homomorphism preserving the vertex
  weights, the wall weights and the line parameters, so the complex partition function at the same
  point is the cast of the rational one (`transfer`); the printed formula evaluates to -7150 at
  that point, where all its denominators are nonzero (`hform`, `hW`)
admission_basis: open-problem-resolution (issue #10444)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.VertexModels.KadeBoxBoundaryRefutation

/-!
M. Kade, *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*,
arXiv:2509.03416v1, section 2.3 "The box boundary condition": a square lattice in a box, with `2M`
horizontal spectral lines (pairs `x_i, 1/x_i`) running from the right wall to the left wall and `2M`
vertical spectral lines (pairs `y_j, 1/y_j`) running from the top wall to the bottom wall. The six
vertex weights are `a = p t - 1/(p t)`, `b = t - 1/t`, `c = p - 1/p` with `t = x/y` at the crossing
of a horizontal line `x` and a vertical line `y`, and the arrow-reflecting walls are the diagonal
K-matrices of the thesis, with `q = p`.
-/

/-- The arrow on a horizontal edge. -/
inductive HArrow
  | left
  | right
  deriving DecidableEq

/-- The arrow on a vertical edge. -/
inductive VArrow
  | up
  | down
  deriving DecidableEq

instance : Fintype HArrow :=
  ⟨{HArrow.left, HArrow.right}, fun h => by cases h <;> simp⟩

instance : Fintype VArrow :=
  ⟨{VArrow.up, VArrow.down}, fun v => by cases v <;> simp⟩

variable {K : Type*} [Field K]

/-- The weight `a(t) = p t - 1/(p t)`. -/
def a (p t : K) : K := p * t - 1 / (p * t)

/-- The weight `b(t) = t - 1/t`. -/
def b (t : K) : K := t - 1 / t

/-- The weight `c = p - 1/p`. -/
def c (p : K) : K := p - 1 / p

/-- The weight of a vertex with left, right, top and bottom arrows `hl`, `hr`, `vt`, `vb`: `a` when
all four arrows point right and up or all point left and down, `b` when the horizontal arrows point
left and the vertical ones up or the horizontal ones right and the vertical ones down, `c` when the
horizontal arrows point into the vertex and the vertical ones out of it or the reverse, and `0`
for the configurations that break the ice rule. -/
def vertexWeight (p t : K) : HArrow → HArrow → VArrow → VArrow → K
  | .right, .right, .up, .up => a p t
  | .left, .left, .down, .down => a p t
  | .left, .left, .up, .up => b t
  | .right, .right, .down, .down => b t
  | .right, .left, .up, .down => c p
  | .left, .right, .down, .up => c p
  | _, _, _, _ => 0

/-- The left wall on the upper and lower edges of a pair of horizontal lines:
`k_L^+ = b(x ξ_L)` (upper arrow right, lower arrow left), `k_L^- = b(x/(p ξ_L))` (the reverse). -/
def leftWall (p x ξ : K) : HArrow → HArrow → K
  | .right, .left => b (x * ξ)
  | .left, .right => b (x / (p * ξ))
  | _, _ => 0

/-- The right wall: `k_R^+ = b(x ξ_R)` (upper arrow left, lower arrow right),
`k_R^- = b(x p/ξ_R)` (the reverse). -/
def rightWall (p x ξ : K) : HArrow → HArrow → K
  | .left, .right => b (x * ξ)
  | .right, .left => b (x * p / ξ)
  | _, _ => 0

/-- The top wall on the left and right edges of a pair of vertical lines:
`k_U^l = b(y ξ_U)` (left arrow down, right arrow up), `k_U^r = b(y p/ξ_U)` (the reverse). -/
def topWall (p y ξ : K) : VArrow → VArrow → K
  | .down, .up => b (y * ξ)
  | .up, .down => b (y * p / ξ)
  | _, _ => 0

/-- The bottom wall: `k_D^l = b(y ξ_D)` (left arrow up, right arrow down),
`k_D^r = b(y/(p ξ_D))` (the reverse). -/
def bottomWall (p y ξ : K) : VArrow → VArrow → K
  | .up, .down => b (y * ξ)
  | .down, .up => b (y / (p * ξ))
  | _, _ => 0

/-- The spectral parameter of horizontal line `r` (counted from the top): rows `2i` and `2i + 1`
carry `x_i` and `1/x_i`. -/
def rowParam {M : ℕ} (xs : Fin M → K) (r : Fin (2 * M)) : K :=
  if r.val % 2 = 0 then xs ⟨r.val / 2, by omega⟩ else 1 / xs ⟨r.val / 2, by omega⟩

/-- The spectral parameter of vertical line `s` (counted from the left): columns `2j` and `2j + 1`
carry `y_j` and `1/y_j`. -/
def colParam {M : ℕ} (ys : Fin M → K) (s : Fin (2 * M)) : K :=
  if s.val % 2 = 0 then ys ⟨s.val / 2, by omega⟩ else 1 / ys ⟨s.val / 2, by omega⟩

/-- The box partition function `Z_M({x_i}|{y_j})`: a configuration assigns an arrow to each of the
`2M + 1` segments of every horizontal line (segment `0` at the left wall, segment `2M` at the right
wall) and of every vertical line (segment `0` at the top wall, segment `2M` at the bottom wall); its
weight is the product of the wall weights and of the weights of the `(2M)²` crossings. -/
def Z (M : ℕ) (p : K) (xs ys : Fin M → K) (ξL ξU ξR ξD : K) : K :=
  ∑ h : Fin (2 * M) → Fin (2 * M + 1) → HArrow, ∑ v : Fin (2 * M) → Fin (2 * M + 1) → VArrow,
    (∏ i : Fin M,
        leftWall p (xs i) ξL (h ⟨2 * i.val, by omega⟩ 0) (h ⟨2 * i.val + 1, by omega⟩ 0) *
          rightWall p (xs i) ξR (h ⟨2 * i.val, by omega⟩ (Fin.last _))
            (h ⟨2 * i.val + 1, by omega⟩ (Fin.last _))) *
      (∏ j : Fin M,
        topWall p (ys j) ξU (v ⟨2 * j.val, by omega⟩ 0) (v ⟨2 * j.val + 1, by omega⟩ 0) *
          bottomWall p (ys j) ξD (v ⟨2 * j.val, by omega⟩ (Fin.last _))
            (v ⟨2 * j.val + 1, by omega⟩ (Fin.last _))) *
      ∏ r : Fin (2 * M), ∏ s : Fin (2 * M),
        vertexWeight p (rowParam xs r / colParam ys s)
          (h r s.castSucc) (h r s.succ) (v s r.castSucc) (v s r.succ)

/-- `W(x, y) = a(xy) a(1/(xy)) a(x/y) a(y/x)`. -/
def W (p x y : K) : K := a p (x * y) * a p (1 / (x * y)) * a p (x / y) * a p (y / x)

/-- `F^LU(x) = b(x ξ_L) b(x p/ξ_U) + b(x/(p ξ_L)) b(x ξ_U)`. -/
def FLU (p x ξL ξU : K) : K := b (x * ξL) * b (x * p / ξU) + b (x / (p * ξL)) * b (x * ξU)

/-- `F^DR(y) = b(y ξ_D) b(y p/ξ_R) + b(y/(p ξ_D)) b(y ξ_R)`. -/
def FDR (p y ξD ξR : K) : K := b (y * ξD) * b (y * p / ξR) + b (y / (p * ξD)) * b (y * ξR)

/-- The conjectured value of `Z_M`, as printed: a product over all `i, j` divided by a product over
`i < j`, times the determinant of the `M × M` matrix with entries
`c² a(x_i y_j) a(1/(x_i y_j)) F^LU(x_i) F^DR(y_j) / ((x_j/y_i - y_i/x_j) W(x_i, y_j))`. -/
def formula (M : ℕ) (p : K) (xs ys : Fin M → K) (ξL ξU ξR ξD : K) : K :=
  (∏ i, ∏ j, (xs i / ys j - ys j / xs i) * W p (xs i) (ys j)) /
      (∏ i, ∏ j ∈ Finset.Ioi i, (xs j / xs i - xs i / xs j) * (ys i / ys j - ys j / ys i)) *
    (Matrix.of fun i j => c p ^ 2 * a p (xs i * ys j) * a p (1 / (xs i * ys j)) *
        FLU p (xs i) ξL ξU * FDR p (ys j) ξD ξR /
        ((xs j / ys i - ys i / xs j) * W p (xs i) (ys j))).det

/-- Kade's conjecture: for every `M` and every choice of complex parameters at which the printed
formula has no vanishing denominator, the box partition function equals the formula. -/
def claim : Prop :=
  ∀ (M : ℕ) (p : ℂ) (xs ys : Fin M → ℂ) (ξL ξU ξR ξD : ℂ),
    p ≠ 0 → ξL ≠ 0 → ξU ≠ 0 → ξR ≠ 0 → ξD ≠ 0 → (∀ i, xs i ≠ 0) → (∀ j, ys j ≠ 0) →
    (∀ i j, xs j / ys i - ys i / xs j ≠ 0) → (∀ i j, W p (xs i) (ys j) ≠ 0) →
    (∀ i j, i < j → (xs j / xs i - xs i / xs j) * (ys i / ys j - ys j / ys i) ≠ 0) →
    Z M p xs ys ξL ξU ξR ξD = formula M p xs ys ξL ξU ξR ξD

set_option maxRecDepth 100000 in
/-- The conjecture fails at `M = 1`, `p = 2`, `x = 2`, `y = 3` and all boundary parameters `1`:
the partition function is `-400400/81` and the formula gives `-7150`. -/
theorem result : ¬ claim := by
  intro h
  -- the rational cast commutes with every weight
  have ha : ∀ p t : ℚ, ((a p t : ℚ) : ℂ) = a (p : ℂ) (t : ℂ) := by
    intro p t; simp [a]
  have hb : ∀ t : ℚ, ((b t : ℚ) : ℂ) = b (t : ℂ) := by
    intro t; simp [b]
  have hc : ∀ p : ℚ, ((c p : ℚ) : ℂ) = c (p : ℂ) := by
    intro p; simp [c]
  have hvw : ∀ (p t : ℚ) hl hr vt vb,
      ((vertexWeight p t hl hr vt vb : ℚ) : ℂ) = vertexWeight (p : ℂ) (t : ℂ) hl hr vt vb := by
    intro p t hl hr vt vb
    cases hl <;> cases hr <;> cases vt <;> cases vb <;> simp [vertexWeight, ha, hb, hc]
  have hL : ∀ (p x ξ : ℚ) hu hd,
      ((leftWall p x ξ hu hd : ℚ) : ℂ) = leftWall (p : ℂ) (x : ℂ) (ξ : ℂ) hu hd := by
    intro p x ξ hu hd; cases hu <;> cases hd <;> simp [leftWall, hb]
  have hR : ∀ (p x ξ : ℚ) hu hd,
      ((rightWall p x ξ hu hd : ℚ) : ℂ) = rightWall (p : ℂ) (x : ℂ) (ξ : ℂ) hu hd := by
    intro p x ξ hu hd; cases hu <;> cases hd <;> simp [rightWall, hb]
  have hU : ∀ (p y ξ : ℚ) hl hr,
      ((topWall p y ξ hl hr : ℚ) : ℂ) = topWall (p : ℂ) (y : ℂ) (ξ : ℂ) hl hr := by
    intro p y ξ hl hr; cases hl <;> cases hr <;> simp [topWall, hb]
  have hD : ∀ (p y ξ : ℚ) hl hr,
      ((bottomWall p y ξ hl hr : ℚ) : ℂ) = bottomWall (p : ℂ) (y : ℂ) (ξ : ℂ) hl hr := by
    intro p y ξ hl hr; cases hl <;> cases hr <;> simp [bottomWall, hb]
  have hrow : ∀ {M : ℕ} (xs : Fin M → ℚ) r,
      ((rowParam xs r : ℚ) : ℂ) = rowParam (fun i => (xs i : ℂ)) r := by
    intro M xs r; unfold rowParam; split_ifs <;> simp
  have hcol : ∀ {M : ℕ} (ys : Fin M → ℚ) s,
      ((colParam ys s : ℚ) : ℂ) = colParam (fun j => (ys j : ℂ)) s := by
    intro M ys s; unfold colParam; split_ifs <;> simp
  have transfer : ∀ (M : ℕ) (p : ℚ) (xs ys : Fin M → ℚ) (ξL ξU ξR ξD : ℚ),
      ((Z M p xs ys ξL ξU ξR ξD : ℚ) : ℂ) =
        Z M (p : ℂ) (fun i => (xs i : ℂ)) (fun j => (ys j : ℂ)) ξL ξU ξR ξD := by
    intro M p xs ys ξL ξU ξR ξD
    simp only [Z, Rat.cast_sum, Rat.cast_prod, Rat.cast_mul, Rat.cast_div, hL, hR, hU, hD, hvw,
      hrow, hcol]
  -- the kernel evaluates the rational partition function
  have hZ : Z 1 (2 : ℚ) ![2] ![3] 1 1 1 1 = -400400 / 81 := by decide +kernel
  have hW : W (2 : ℂ) 2 3 ≠ 0 := by norm_num [W, a]
  have hform : formula 1 (2 : ℂ) ![2] ![3] 1 1 1 1 = -7150 := by
    have hIoi : Finset.Ioi (0 : Fin 1) = ∅ := by decide
    simp only [formula, Fin.prod_univ_one, Matrix.det_unique, hIoi, Finset.prod_empty,
      Matrix.of_apply, Fin.default_eq_zero, Matrix.cons_val_fin_one]
    norm_num [W, FLU, FDR, a, b, c]
  have key := h 1 2 ![2] ![3] 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by intro i; fin_cases i; norm_num) (by intro j; fin_cases j; norm_num)
    (by intro i j; fin_cases i; fin_cases j; norm_num)
    (by intro i j; fin_cases i; fin_cases j; exact hW)
    (by intro i j hij; fin_cases i; fin_cases j; exact absurd hij (lt_irrefl _))
  have hcast := transfer 1 2 ![2] ![3] 1 1 1 1
  rw [hZ] at hcast
  have hfun2 : (fun i => ((![(2 : ℚ)] i : ℚ) : ℂ)) = ![(2 : ℂ)] := by
    funext i; fin_cases i; simp
  have hfun3 : (fun j => ((![(3 : ℚ)] j : ℚ) : ℂ)) = ![(3 : ℂ)] := by
    funext j; fin_cases j; simp
  rw [hfun2, hfun3] at hcast
  push_cast at hcast
  rw [← hcast, hform] at key
  norm_num at key

end D5.S3.StatisticalMechanics.VertexModels.KadeBoxBoundaryRefutation
