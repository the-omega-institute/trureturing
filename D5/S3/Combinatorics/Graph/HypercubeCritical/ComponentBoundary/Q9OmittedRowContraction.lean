/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OmittedRowContraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OmittedRowContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected, mathlib/module/Mathlib.Data.Matrix.Mul]
   utility: none
   digest: Exact contraction of weighted pair rows and all residual equations. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.Basic

/-! Exact elimination of the two-contact rows given a nowhere-zero reference vector. -/

set_option autoImplicit false
set_option linter.style.longLine false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OmittedRowContraction

open scoped BigOperators
open Finset (univ)

universe u v w

variable {V : Type u} {R : Type v} {K : Type w} [Field K]

open Classical in
/-- Each residual row has one coefficient per component, obtained by summing
its reference-weighted coefficients over the vertices of that component. -/
@[expose] noncomputable def compressedRows [Fintype V] (G : SimpleGraph V) (p : V → K)
    (B : Matrix R V K) : Matrix R G.ConnectedComponent K :=
  fun r c => ∑ v ∈ univ.filter (fun v => G.connectedComponentMk v = c), B r v * p v

private theorem normalized_eq_of_walk {G : SimpleGraph V} {p x : V → K}
    (hp : ∀ v, p v ≠ 0)
    (hedge : ∀ u v, G.Adj u v → p u * x v = p v * x u)
    {u v : V} (walk : G.Walk u v) : x u / p u = x v / p v := by
  induction walk with
  | nil => rfl
  | @cons a b c hab _ ih =>
    have hab' : x a / p a = x b / p b := (div_eq_div_iff (hp a) (hp b)).2 (by
      simpa only [mul_comm (x a), mul_comm (x b)] using (hedge a b hab).symm)
    exact hab'.trans ih

/-- The pair rows and all remaining rows are equivalent to a unique residual
solution on the connected components. Pointwise nonvanishing is preserved in
both directions. -/
theorem pair_and_residual_rows_iff [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] (p : V → K) (B : Matrix R V K) (x : V → K)
    (hp : ∀ v, p v ≠ 0) :
    ((∀ u v, G.Adj u v → p u * x v = p v * x u) ∧ B.mulVec x = 0) ↔
      ∃! z : G.ConnectedComponent → K,
        (∀ v, x v = p v * z (G.connectedComponentMk v)) ∧
          (compressedRows G p B).mulVec z = 0 ∧
          ((∀ v, x v ≠ 0) ↔ ∀ c, z c ≠ 0) := by
  classical
  have row_action (z : G.ConnectedComponent → K) :
      (compressedRows G p B).mulVec z = B.mulVec (fun v => p v * z (G.connectedComponentMk v)) := by
    funext r
    simp only [Matrix.mulVec, dotProduct, compressedRows, Finset.sum_mul]
    calc
      _ = ∑ c, ∑ v ∈ univ.filter (fun v => G.connectedComponentMk v = c),
          B r v * (p v * z (G.connectedComponentMk v)) := by
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro v hv
        rw [(Finset.mem_filter.mp hv).2, mul_assoc]
      _ = _ := Finset.sum_fiberwise univ G.connectedComponentMk _
  constructor
  · rintro ⟨hedge, hrows⟩
    let z := SimpleGraph.ConnectedComponent.lift (fun v => x v / p v)
      (fun _ _ walk _ => normalized_eq_of_walk hp hedge walk)
    have hx (v : V) : x v = p v * z (G.connectedComponentMk v) := by
      change x v = p v * (x v / p v)
      rw [mul_comm, div_mul_cancel₀ _ (hp v)]
    refine ⟨z, ⟨hx, ?_, ?_⟩, ?_⟩
    · rw [row_action, ← funext hx, hrows]
    · rw [SimpleGraph.ConnectedComponent.forall]
      exact ⟨fun h v hz => h v (by rw [hx v, hz, mul_zero]),
        fun h v => (hx v).symm ▸ mul_ne_zero (hp v) (h v)⟩
    · intro z' hz'
      funext c
      refine c.ind fun v => ?_
      exact mul_left_cancel₀ (hp v) ((hz'.1 v).symm.trans (hx v))
  · rintro ⟨z, ⟨hx, hrows, _⟩, _⟩
    refine ⟨?_, ?_⟩
    · intro u v huv
      rw [hx u, hx v, SimpleGraph.ConnectedComponent.sound huv.reachable,
        ← mul_assoc, ← mul_assoc, mul_comm (p u) (p v)]
    · rw [funext hx, ← row_action, hrows]

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OmittedRowContraction
