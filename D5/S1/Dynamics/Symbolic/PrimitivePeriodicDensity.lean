/- GID: D5/S1/Dynamics/Symbolic/PrimitivePeriodicDensity
   generality: G
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Primitive adjacency supplies positive bridge paths in a finite graph. -/
import D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Algebra.Ring.Periodic

/-! Primitive finite-graph shifts have periodic points in every finite cylinder.

The first compiled bridge records the matrix-to-quiver step needed by the
periodic-density construction. -/

noncomputable section

open Classical
open Set Function
open SymbolicDynamics
open D5.S1.Dynamics.Shadowing
open D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
open Quiver
open Quiver.Path

namespace D5.S1.Dynamics.Symbolic.PrimitivePeriodicDensity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Integer adjacency matrix, suitable for `Matrix.IsPrimitive`. -/
def adjacencyInt (edge : V → V → Prop) : Matrix V V ℤ :=
  fun i j => if edge i j then 1 else 0

@[simp] theorem adjacencyInt_apply (edge : V → V → Prop) (i j : V) :
    adjacencyInt edge i j = if edge i j then 1 else 0 := rfl

@[simp] theorem adjacencyInt_pos_iff (edge : V → V → Prop) (i j : V) :
    0 < adjacencyInt edge i j ↔ edge i j := by
  classical
  by_cases h : edge i j <;> simp [adjacencyInt, h]

private theorem adjacencyInt_nonneg (edge : V → V → Prop) (i j : V) :
    0 ≤ adjacencyInt edge i j := by
  classical
  by_cases h : edge i j <;> simp [adjacencyInt, h]

/-- A graph-language point is periodic when it has a positive additive period. -/
def periodicPoints (edge : V → V → Prop) : Set (ℕ → V) :=
  {y | y ∈ edgeLanguage edge ∧ ∃ p : ℕ, 0 < p ∧ Function.Periodic y p}

/-- Primitive adjacency gives a positive-length quiver path between any two
vertices.  The path's arrows are positive entries of the integer adjacency
matrix, hence are exactly the declared graph edges. -/
theorem primitive_bridge_path (edge : V → V → Prop)
    (hprim : Matrix.IsPrimitive (adjacencyInt edge)) (u v : V) :
    ∃ m : ℕ, m > 0 ∧
      ∃ p : @Quiver.Path V (Matrix.toQuiver (adjacencyInt edge)) u v,
        @Quiver.Path.length V (Matrix.toQuiver (adjacencyInt edge)) u v p = m := by
  obtain ⟨m, hm, hpow⟩ := hprim.exists_pos_pow
  refine ⟨m, hm, ?_⟩
  letI : Quiver V := Matrix.toQuiver (adjacencyInt edge)
  have hpos : 0 < (adjacencyInt edge ^ m) u v := hpow u v
  obtain ⟨⟨p, hp⟩⟩ :=
    (Matrix.pow_apply_pos_iff_nonempty_path
      (A := adjacencyInt edge) (fun i j => adjacencyInt_nonneg edge i j) m u v).mp hpos
  exact ⟨p, hp⟩

private theorem path_vertices_get_length
    (edge : V → V → Prop) [DecidableRel edge] {a b : V}
    (p : @Quiver.Path V (Matrix.toQuiver (adjacencyInt edge)) a b) :
    (@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a b p)[
      @Quiver.Path.length V (Matrix.toQuiver (adjacencyInt edge)) a b p]'(by
        rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a b p]
        omega) = @Quiver.Path.end V (Matrix.toQuiver (adjacencyInt edge)) a b p := by
  classical
  letI : Quiver V := Matrix.toQuiver (adjacencyInt edge)
  induction p with
  | nil => rfl
  | @cons m c p e ih =>
      simp [vertices_cons, length_cons]

private theorem path_vertices_edge
    (edge : V → V → Prop) [DecidableRel edge] :
    ∀ {a b : V}
      (p : @Quiver.Path V (Matrix.toQuiver (adjacencyInt edge)) a b),
      ∀ i : Fin (@Quiver.Path.length V (Matrix.toQuiver (adjacencyInt edge)) a b p),
      edge
        ((@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a b p)[i.val]'(by
          rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a b p]
          omega))
        ((@Quiver.Path.vertices V (Matrix.toQuiver (adjacencyInt edge)) a b p)[i.val + 1]'(by
          rw [@Quiver.Path.vertices_length V (Matrix.toQuiver (adjacencyInt edge)) a b p]
          omega)) := by
  classical
  letI : Quiver V := Matrix.toQuiver (adjacencyInt edge)
  intro a b p
  induction p with
  | nil =>
      intro i
      exact Fin.elim0 i
  | @cons m c p e ih =>
      intro i
      cases i using Fin.lastCases with
      | last =>
          have hpos : 0 < adjacencyInt edge m c := e.down
          have hedge' : edge m c := (adjacencyInt_pos_iff edge m c).mp hpos
          simpa [vertices_cons, path_vertices_get_length, Quiver.Path.end] using hedge'
      | cast j =>
          simpa [vertices_cons] using ih j

end D5.S1.Dynamics.Symbolic.PrimitivePeriodicDensity
