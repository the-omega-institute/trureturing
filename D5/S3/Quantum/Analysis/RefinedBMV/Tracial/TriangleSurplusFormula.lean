/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TriangleSurplusFormula
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Evaluation of the scaled adjugate surpluses for the three-label allocation. -/

import Lean

/-! Arithmetic shared by the polynomial and packed integer evaluations. -/

namespace RefinedBMV.Tracial.TriangleSurplus

/-- Adjoin one variable to the complete homogeneous sums. The next coefficient
is its old value plus the new variable times the preceding new coefficient. -/
def adjoin [Add R] [Mul R] (x : R) : R → List R → List R
  | _, [] => []
  | prev, c :: cs =>
    let next := c + x * prev
    next :: adjoin x next cs

/-- Insert a variable into an ascending row, keeping the constant coefficient. -/
def extend [Add R] [Mul R] (x : R) : List R → List R
  | [] => []
  | c :: cs => c :: adjoin x c cs

/-- Complete homogeneous sum in the fourth powers, minus the balanced monomial. -/
def gap [Add R] [Sub R] [Mul R] [NatCast R] [Pow R Nat]
    (a b c d : R) : R :=
  let zero : R := (↑(0 : Nat) : R)
  let initial : List R := (↑(1 : Nat) : R) :: List.replicate 17 zero
  let row := extend (d ^ 4)
    (extend (c ^ 4) (extend (b ^ 4) (extend (a ^ 4) initial)))
  row[17]?.getD zero - (↑(1140 : Nat) : R) * (a * b * c * d) ^ 17

/-- The entries of twice the backtracking coefficient times the binary Gram. -/
structure Edge (R : Type u) where
  left : R
  cross : R
  right : R

def edge [Mul R] [NatCast R] (h f g r : R) : Edge R :=
  ⟨(↑(2 : Nat) : R) * h * f, h * g, (↑(2 : Nat) : R) * h * r⟩

def Edge.form [Add R] [Mul R] [NatCast R] [Pow R Nat]
    (e : Edge R) (u v : R) : R :=
  e.left * u ^ 2 + (↑(2 : Nat) : R) * e.cross * u * v + e.right * v ^ 2

/-- The adjugate numerator for a symmetric system with diagonal a,d,f and
off-diagonal entries b,c,e. Edges are listed in the order 01, 02, 12. -/
def clearedOfEntries [Add R] [Sub R] [Mul R] [NatCast R] [Pow R Nat]
    (a b c d e f l₀ l₁ l₂ : R) (e₀₁ e₀₂ e₁₂ : Edge R) (w₀₁ w₀₂ w₁₂ : R) :
    R × R × R :=
  let aa := d * f - e ^ 2
  let ab := c * e - b * f
  let ac := b * e - c * d
  let dd := a * f - c ^ 2
  let de := b * c - a * e
  let ff := a * d - b ^ 2
  let det := a * aa + b * ab + c * ac
  let u₀ := aa * l₀ + ab * l₁ + ac * l₂
  let u₁ := ab * l₀ + dd * l₁ + de * l₂
  let u₂ := ac * l₀ + de * l₁ + ff * l₂
  (det ^ 2 - (↑(2 : Nat) : R) * w₀₁ ^ 2 * e₀₁.form u₀ u₁,
    det ^ 2 - (↑(2 : Nat) : R) * w₀₂ ^ 2 * e₀₂.form u₀ u₂,
    det ^ 2 - (↑(2 : Nat) : R) * w₁₂ ^ 2 * e₁₂.form u₁ u₂)

/-- The scalar adjugate formulas for a symmetric triangle system. Edges are
listed in the order 01, 02, 12. -/
def cleared [Add R] [Sub R] [Mul R] [NatCast R] [Pow R Nat]
    (l₀ l₁ l₂ : R) (e₀₁ e₀₂ e₁₂ : Edge R) (w₀₁ w₀₂ w₁₂ : R) :
    R × R × R :=
  let a := w₀₁ * e₀₁.left + w₀₂ * e₀₂.left
  let b := w₀₁ * e₀₁.cross
  let c := w₀₂ * e₀₂.cross
  let d := w₀₁ * e₀₁.right + w₁₂ * e₁₂.left
  let e := w₁₂ * e₁₂.cross
  let f := w₀₂ * e₀₂.right + w₁₂ * e₁₂.right
  clearedOfEntries a b c d e f l₀ l₁ l₂ e₀₁ e₀₂ e₁₂ w₀₁ w₀₂ w₁₂

/-- The three unnormalized surpluses at the nodes `1, x^4, (x*y)^4`. -/
def surplus [Add R] [Sub R] [Mul R] [NatCast R] [Pow R Nat]
    (x y : R) : R × R × R :=
  let a : R := (↑(1 : Nat) : R)
  let b := x
  let c := x * y
  let l₀ := gap a a b c
  let l₁ := gap b b a c
  let l₂ := gap c c a b
  let e₀₁ := edge l₂ (gap a a a b) (gap a a b b) (gap b b b a)
  let e₀₂ := edge l₁ (gap a a a c) (gap a a c c) (gap c c c a)
  let e₁₂ := edge l₀ (gap b b b c) (gap b b c c) (gap c c c b)
  cleared l₀ l₁ l₂ e₀₁ e₀₂ e₁₂ ((↑(3 : Nat) : R) + y ^ 17)
    (↑(4 : Nat) : R) (↑(4 : Nat) : R)

end RefinedBMV.Tracial.TriangleSurplus
