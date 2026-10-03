/- GID: D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/MonsterTwistedOctonionNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit signed Cayley-Dickson table has a multiplicative Euclidean norm. -/

/-
proof_shape: twisted_octonion_norm: content
escape_witness: Expand the eight signed coordinates and close the resulting polynomial identity
  over the reals; the two unit laws are checked independently by the same table.
admission_basis: escape-witness
Direct frozen dependencies: none.
-/

import Mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm

/-- Coordinates of the auxiliary eight-dimensional twisted group-algebra model. -/
abbrev Octonion := Fin 8 → ℝ

/-- The signed Cayley-Dickson multiplication in the basis `1,e₁,…,e₇`.

This is an explicit representative of the admissible `F₂³` sign table.  The
finite sign-table comparison and the VOA/OPE interpretation live in the theory
document; this definition itself is only the auxiliary real algebra. -/
def mul (x y : Octonion) : Octonion := fun i => (![ 
    x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 -
      x 4 * y 4 - x 5 * y 5 - x 6 * y 6 - x 7 * y 7,
    x 0 * y 1 + x 1 * y 0 + x 2 * y 3 - x 3 * y 2 +
      x 4 * y 5 - x 5 * y 4 - x 6 * y 7 + x 7 * y 6,
    x 0 * y 2 - x 1 * y 3 + x 2 * y 0 + x 3 * y 1 +
      x 4 * y 6 + x 5 * y 7 - x 6 * y 4 - x 7 * y 5,
    x 0 * y 3 + x 1 * y 2 - x 2 * y 1 + x 3 * y 0 +
      x 4 * y 7 - x 5 * y 6 + x 6 * y 5 - x 7 * y 4,
    x 0 * y 4 - x 1 * y 5 - x 2 * y 6 - x 3 * y 7 +
      x 4 * y 0 + x 5 * y 1 + x 6 * y 2 + x 7 * y 3,
    x 0 * y 5 + x 1 * y 4 - x 2 * y 7 + x 3 * y 6 -
      x 4 * y 1 + x 5 * y 0 - x 6 * y 3 + x 7 * y 2,
    x 0 * y 6 + x 1 * y 7 + x 2 * y 4 - x 3 * y 5 -
      x 4 * y 2 + x 5 * y 3 + x 6 * y 0 - x 7 * y 1,
    x 0 * y 7 - x 1 * y 6 + x 2 * y 5 + x 3 * y 4 -
      x 4 * y 3 - x 5 * y 2 + x 6 * y 1 + x 7 * y 0]) i

/-- The Euclidean square norm in the signed basis. -/
def normSq (x : Octonion) : ℝ := ∑ i, (x i) ^ 2

/-- The scalar basis vector is a two-sided unit. -/
def one : Octonion := ![1, 0, 0, 0, 0, 0, 0, 0]

theorem one_mul (x : Octonion) : mul one x = x := by
  funext i
  fin_cases i <;> simp [one, mul]

theorem mul_one (x : Octonion) : mul x one = x := by
  funext i
  fin_cases i <;> simp [one, mul]

/-- The signed multiplication has the composition (multiplicative norm) law.

The proof expands the eight coordinates and normalizes the resulting
polynomial identity.  It therefore applies to arbitrary real vectors, rather
than checking only the finite basis table. -/
theorem norm_mul (x y : Octonion) :
    normSq (mul x y) = normSq x * normSq y := by
  simp [normSq, mul, Fin.sum_univ_succ]
  ring

end D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm
