/- GID: D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport
   generality: G
   mirror-B: D5/B/S3/Observer/HigherHolonomy/FiniteMatrixTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite matrix transport composes along vertex paths and gauge factors telescope to the endpoints. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Finite matrix path transport

Let every ordered pair of vertices carry an invertible finite matrix.  A path
is encoded by a starting vertex and the list of successive vertices.  Because
matrices act on columns, the first edge appears on the right of the total
product.

The transport of an appended path is the later transport multiplied by the
earlier transport.  Under a vertex gauge `g`, each edge changes by

`Tᵍ(a,b) = g(b) T(a,b) g(a)⁻¹`,

and all interior gauge factors cancel, leaving only the endpoint conjugation.

This module treats a finite path in a fixed finite matrix fiber.  It does not
construct a smooth bundle, connection form, curvature two-form, surface
transport, or higher gauge two-functor.
-/

/- Library-search audit trail (2026-09-01):
   * `MemoryTransport` owns composition of untyped update functions.
   * `WormholeHolonomy` owns round trips in a typed dynamical network and
     explicitly does not claim differential-geometric holonomy.
   * Repository search found no finite matrix path evaluator with an exact
     endpoint gauge-covariance theorem.
   * Pinned Mathlib supplies matrix units and noncommutative group
     normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.HigherHolonomy.FiniteMatrixTransport

noncomputable section

universe u v

variable {Vertex : Type v}
variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Endpoint reached after visiting a finite list of successive vertices. -/
def pathEnd : Vertex → List Vertex → Vertex
  | start, [] => start
  | _, next :: rest => pathEnd next rest

/-- Reverse ordered product of invertible edge matrices along a finite vertex
path. -/
def pathTransport
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ) :
    Vertex → List Vertex → (Matrix n n ℂ)ˣ
  | _, [] => 1
  | start, next :: rest =>
      pathTransport edge next rest * edge start next

/-- Appending path segments gives the later matrix product followed by the
earlier matrix product. -/
theorem pathTransport_append
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (start : Vertex) (middlePath laterPath : List Vertex) :
    pathTransport edge start (middlePath ++ laterPath) =
      pathTransport edge (pathEnd start middlePath) laterPath *
        pathTransport edge start middlePath := by
  induction middlePath generalizing start with
  | nil =>
      simp [pathTransport, pathEnd]
  | cons next middlePath inductionHypothesis =>
      simp [pathTransport, pathEnd, inductionHypothesis, mul_assoc]

/-- Vertex-gauge transformation of an edge matrix. -/
def gaugeEdgeTransport
    (gauge : Vertex → (Matrix n n ℂ)ˣ)
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (source target : Vertex) : (Matrix n n ℂ)ˣ :=
  gauge target * edge source target * (gauge source)⁻¹

/-- Gauge factors telescope along a finite path, leaving only the endpoint
factors. -/
theorem pathTransport_gauge
    (gauge : Vertex → (Matrix n n ℂ)ˣ)
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (start : Vertex) (steps : List Vertex) :
    pathTransport (gaugeEdgeTransport gauge edge) start steps =
      gauge (pathEnd start steps) *
        pathTransport edge start steps * (gauge start)⁻¹ := by
  induction steps generalizing start with
  | nil =>
      simp [pathTransport, pathEnd]
  | cons next steps inductionHypothesis =>
      simp only [pathTransport, pathEnd, gaugeEdgeTransport,
        inductionHypothesis]
      group

/-- A closed path transforms by conjugation at its base vertex. -/
theorem loopTransport_gauge_conjugate
    (gauge : Vertex → (Matrix n n ℂ)ˣ)
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (base : Vertex) (steps : List Vertex)
    (hLoop : pathEnd base steps = base) :
    pathTransport (gaugeEdgeTransport gauge edge) base steps =
      gauge base * pathTransport edge base steps * (gauge base)⁻¹ := by
  rw [pathTransport_gauge, hLoop]

/-- Empty paths have identity transport and remain at their start. -/
theorem empty_path_transport
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ) (start : Vertex) :
    pathEnd start [] = start ∧ pathTransport edge start [] = 1 := by
  exact ⟨rfl, rfl⟩

/-- A one-edge path evaluates to that edge transport. -/
theorem one_edge_path_transport
    (edge : Vertex → Vertex → (Matrix n n ℂ)ˣ)
    (source target : Vertex) :
    pathTransport edge source [target] = edge source target := by
  simp [pathTransport]

example :
    pathTransport
      (fun _ _ : Unit => (1 : (Matrix (Fin 1) (Fin 1) ℂ)ˣ))
      () [(), ()] = 1 := by
  simp [pathTransport]

#print axioms pathTransport_append
#print axioms pathTransport_gauge
#print axioms loopTransport_gauge_conjugate
#print axioms empty_path_transport
#print axioms one_edge_path_transport

end

end D5.S3.Observer.HigherHolonomy.FiniteMatrixTransport
