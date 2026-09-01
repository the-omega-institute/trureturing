/- GID: D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature
   generality: G
   mirror-B: D5/B/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Triangle loops define a finite matrix curvature whose holonomy conjugates and whose trace and determinant are gauge invariant. -/

import D5.S3.Observer.HigherHolonomy.MatrixGaugeCovariance
import Mathlib.Tactic

/-!
# Finite triangle holonomy curvature

Three vertices determine the closed path `a -> b -> c -> a`.  Its reverse
ordered matrix product is the triangle holonomy.  Subtracting the identity
produces a finite curvature defect.  Vertex gauge transport conjugates the
triangle holonomy at the base vertex, so its trace and determinant are gauge
invariant.  A triangle is flat exactly when its curvature defect vanishes.

This module provides the first discrete two-cell curvature object for the
matrix transport line.  It does not construct surface ordering, a crossed
module, a differential curvature form, a Chern class, or a continuum limit.
-/

/- Library-search audit trail (2026-09-01):
   * `FiniteMatrixTransport` owns path composition and endpoint gauge
     covariance.
   * `MatrixGaugeCovariance` owns trace and determinant invariance of closed
     path transport.
   * Repository search found no matrix triangle curvature specialized from
     those owners.
   * Pinned Mathlib supplies units, matrix subtraction, and group
     normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.HigherHolonomy.TriangleHolonomyCurvature

open D5.S3.Observer.HigherHolonomy.FiniteMatrixTransport
open D5.S3.Observer.HigherHolonomy.MatrixGaugeCovariance

noncomputable section

universe u v

variable {Vertex : Type v}
variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Successive vertices of the oriented triangle based at `first`. -/
def trianglePath (first second third : Vertex) : List Vertex :=
  [second, third, first]

/-- Matrix holonomy around the oriented triangle `first -> second -> third ->
first`. -/
def triangleHolonomy
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (first second third : Vertex) : (Matrix n n ℂ)ˣ :=
  pathTransport edge first (trianglePath first second third)

/-- Additive curvature defect of a finite triangle. -/
def triangleCurvature
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (first second third : Vertex) : Matrix n n ℂ :=
  (triangleHolonomy edge first second third : Matrix n n ℂ) - 1

/-- A finite triangle is flat when its loop holonomy is the identity. -/
def IsFlatTriangle
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (first second third : Vertex) : Prop :=
  triangleHolonomy edge first second third = 1

/-- Explicit ordered product formula for triangle holonomy. -/
theorem triangle_holonomy_formula
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (first second third : Vertex) :
    triangleHolonomy edge first second third =
      edge third first * edge second third * edge first second := by
  simp [triangleHolonomy, trianglePath, pathTransport, mul_assoc]

/-- Triangle paths close at their base vertex. -/
theorem triangle_path_end
    (first second third : Vertex) :
    pathEnd first (trianglePath first second third) = first := by
  rfl

/-- Vertex gauge transport conjugates triangle holonomy at the base vertex. -/
theorem triangle_holonomy_gauge_conjugate
    (gauge : Vertex → (Matrix n n ℂ)ˣ)
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (first second third : Vertex) :
    triangleHolonomy (gaugeEdgeTransport gauge edge) first second third =
      gauge first * triangleHolonomy edge first second third *
        (gauge first)⁻¹ := by
  exact loopTransport_gauge_conjugate gauge edge first
    (trianglePath first second third) (triangle_path_end first second third)

/-- Trace of triangle holonomy is gauge invariant. -/
theorem triangle_trace_gauge_invariant
    (gauge : Vertex → (Matrix n n ℂ)ˣ)
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (first second third : Vertex) :
    Matrix.trace
        (triangleHolonomy (gaugeEdgeTransport gauge edge)
          first second third : Matrix n n ℂ) =
      Matrix.trace
        (triangleHolonomy edge first second third : Matrix n n ℂ) := by
  rw [triangle_holonomy_gauge_conjugate]
  exact trace_unit_conjugate _ _

/-- Determinant of triangle holonomy is gauge invariant. -/
theorem triangle_determinant_gauge_invariant
    (gauge : Vertex → (Matrix n n ℂ)ˣ)
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (first second third : Vertex) :
    Matrix.det
        (triangleHolonomy (gaugeEdgeTransport gauge edge)
          first second third : Matrix n n ℂ) =
      Matrix.det
        (triangleHolonomy edge first second third : Matrix n n ℂ) := by
  rw [triangle_holonomy_gauge_conjugate]
  exact determinant_unit_conjugate _ _

/-- Vanishing curvature is equivalent to flat triangle holonomy. -/
theorem triangle_curvature_eq_zero_iff
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (first second third : Vertex) :
    triangleCurvature edge first second third = 0 ↔
      IsFlatTriangle edge first second third := by
  unfold triangleCurvature IsFlatTriangle
  constructor
  · intro hZero
    apply Units.ext
    exact sub_eq_zero.mp hZero
  · intro hFlat
    apply sub_eq_zero.mpr
    exact congrArg (fun unit : (Matrix n n ℂ)ˣ =>
      (unit : Matrix n n ℂ)) hFlat

/-- Flatness is preserved by every vertex gauge. -/
theorem isFlatTriangle_gauge
    (gauge : Vertex → (Matrix n n ℂ)ˣ)
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (first second third : Vertex)
    (hFlat : IsFlatTriangle edge first second third) :
    IsFlatTriangle (gaugeEdgeTransport gauge edge) first second third := by
  rw [IsFlatTriangle, triangle_holonomy_gauge_conjugate, hFlat]
  simp

/-- Traversing one edge and its prescribed inverse produces trivial
holonomy. -/
theorem backtrack_holonomy_eq_one
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (first second : Vertex)
    (hReverse : edge second first = (edge first second)⁻¹) :
    pathTransport edge first [second, first] = 1 := by
  simp [pathTransport, hReverse]

example :
    IsFlatTriangle
      (fun _ _ : Unit => (1 : (Matrix (Fin 1) (Fin 1) ℂ)ˣ))
      () () () := by
  simp [IsFlatTriangle, triangleHolonomy, trianglePath, pathTransport]

#print axioms triangle_holonomy_formula
#print axioms triangle_holonomy_gauge_conjugate
#print axioms triangle_trace_gauge_invariant
#print axioms triangle_determinant_gauge_invariant
#print axioms triangle_curvature_eq_zero_iff
#print axioms isFlatTriangle_gauge
#print axioms backtrack_holonomy_eq_one

end

end D5.S3.Observer.HigherHolonomy.TriangleHolonomyCurvature
