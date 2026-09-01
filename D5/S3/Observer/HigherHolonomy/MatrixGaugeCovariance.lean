/- GID: D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance
   generality: G
   mirror-B: D5/B/S3/Observer/HigherHolonomy/MatrixGaugeCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Trace and determinant of finite matrix loop holonomy are invariant under vertex gauge transport. -/

import D5.S3.Observer.HigherHolonomy.FiniteMatrixTransport
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
# Gauge-invariant finite loop observables

Finite path transport is gauge covariant, and a closed path changes by
conjugation at its base vertex.  This module extracts two standard scalar
observables of that conjugacy class: trace and determinant.  Both are invariant
under every vertex gauge.

The result is a finite matrix statement.  It does not define a Wilson-loop
measure, characteristic class, Chern number, or continuum gauge field.
-/

/- Library-search audit trail (2026-09-01):
   * `FiniteMatrixTransport` owns path evaluation and endpoint gauge
     covariance.
   * Repository holonomy modules use set maps or policy invariance and do not
     own conjugacy-invariant finite matrix observables.
   * Pinned Mathlib supplies cyclicity of finite matrix trace and
     multiplicativity of determinant. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.HigherHolonomy.MatrixGaugeCovariance

open D5.S3.Observer.HigherHolonomy.FiniteMatrixTransport

noncomputable section

universe u v

variable {Vertex : Type v}
variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Trace of a finite path transport. -/
def transportTrace
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (start : Vertex) (steps : List Vertex) : ℂ :=
  Matrix.trace (pathTransport edge start steps : Matrix n n ℂ)

/-- Determinant of a finite path transport. -/
def transportDeterminant
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (start : Vertex) (steps : List Vertex) : ℂ :=
  Matrix.det (pathTransport edge start steps : Matrix n n ℂ)

/-- Trace is invariant under conjugation by a matrix unit. -/
theorem trace_unit_conjugate
    (gauge holonomy : (Matrix n n ℂ)ˣ) :
    Matrix.trace
        ((gauge * holonomy * gauge⁻¹ : (Matrix n n ℂ)ˣ) :
          Matrix n n ℂ) =
      Matrix.trace (holonomy : Matrix n n ℂ) := by
  change Matrix.trace
      (((gauge : Matrix n n ℂ) * (holonomy : Matrix n n ℂ)) *
        (gauge⁻¹ : Matrix n n ℂ)) =
    Matrix.trace (holonomy : Matrix n n ℂ)
  calc
    Matrix.trace
        (((gauge : Matrix n n ℂ) * (holonomy : Matrix n n ℂ)) *
          (gauge⁻¹ : Matrix n n ℂ)) =
      Matrix.trace
        ((gauge⁻¹ : Matrix n n ℂ) *
          ((gauge : Matrix n n ℂ) * (holonomy : Matrix n n ℂ))) := by
            exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace (holonomy : Matrix n n ℂ) := by
      rw [← Matrix.mul_assoc]
      simp

/-- Determinant is invariant under conjugation by a matrix unit. -/
theorem determinant_unit_conjugate
    (gauge holonomy : (Matrix n n ℂ)ˣ) :
    Matrix.det
        ((gauge * holonomy * gauge⁻¹ : (Matrix n n ℂ)ˣ) :
          Matrix n n ℂ) =
      Matrix.det (holonomy : Matrix n n ℂ) := by
  change Matrix.det
      (((gauge : Matrix n n ℂ) * (holonomy : Matrix n n ℂ)) *
        (gauge⁻¹ : Matrix n n ℂ)) =
    Matrix.det (holonomy : Matrix n n ℂ)
  simp [Matrix.det_mul]

/-- Trace of closed-path holonomy is invariant under every vertex gauge. -/
theorem loop_transport_trace_gauge_invariant
    (gauge : Vertex → (Matrix n n ℂ)ˣ)
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (base : Vertex) (steps : List Vertex)
    (hLoop : pathEnd base steps = base) :
    transportTrace (gaugeEdgeTransport gauge edge) base steps =
      transportTrace edge base steps := by
  unfold transportTrace
  rw [loopTransport_gauge_conjugate gauge edge base steps hLoop]
  exact trace_unit_conjugate _ _

/-- Determinant of closed-path holonomy is invariant under every vertex
gauge. -/
theorem loop_transport_determinant_gauge_invariant
    (gauge : Vertex → (Matrix n n ℂ)ˣ)
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (base : Vertex) (steps : List Vertex)
    (hLoop : pathEnd base steps = base) :
    transportDeterminant (gaugeEdgeTransport gauge edge) base steps =
      transportDeterminant edge base steps := by
  unfold transportDeterminant
  rw [loopTransport_gauge_conjugate gauge edge base steps hLoop]
  exact determinant_unit_conjugate _ _

/-- The determinant of an empty loop is one. -/
theorem transportDeterminant_empty
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ) (base : Vertex) :
    transportDeterminant edge base [] = 1 := by
  simp [transportDeterminant, pathTransport]

example :
    transportTrace
      (fun _ _ : Unit => (1 : (Matrix (Fin 1) (Fin 1) ℂ)ˣ))
      () [] = 1 := by
  simp [transportTrace, pathTransport, Matrix.trace_fin_one]

#print axioms trace_unit_conjugate
#print axioms determinant_unit_conjugate
#print axioms loop_transport_trace_gauge_invariant
#print axioms loop_transport_determinant_gauge_invariant
#print axioms transportDeterminant_empty

end

end D5.S3.Observer.HigherHolonomy.MatrixGaugeCovariance
