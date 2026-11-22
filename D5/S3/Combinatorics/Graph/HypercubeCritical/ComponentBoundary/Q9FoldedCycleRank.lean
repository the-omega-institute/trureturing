/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedCycleRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedCycleRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.IncMatrix, mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: The binary Laplacian computes the residual switching rank for exact integer signed rows. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The cycle space modulo the switches that preserve row parity. -/

set_option autoImplicit false

open scoped BigOperators Matrix
open LinearMap

universe u v

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank

abbrev Cycles {V : Type u} {E : Type v} [Fintype E] (B : Matrix V E (ZMod 2)) :=
  ker B.mulVecLin

/-- The bicycle subspace, viewed inside the cycle space. -/
def bicycles {V : Type u} {E : Type v} [Fintype V] [Fintype E] (B : Matrix V E (ZMod 2)) :
    Submodule (ZMod 2) (Cycles B) :=
  (Cycles B ⊓ range Bᵀ.mulVecLin).comap (Cycles B).subtype

/-- The dimension of the residual switching quotient. -/
noncomputable def residualRank {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (B : Matrix V E (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) (Cycles B ⧸ bicycles B)

/-- Restricting incidence to the switching space transports its kernel to the bicycles. -/
private theorem finrank_restricted_ker {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (B : Matrix V E (ZMod 2)) :
    Module.finrank (ZMod 2) (ker (B.mulVecLin.domRestrict (range Bᵀ.mulVecLin))) =
      Module.finrank (ZMod 2) (bicycles B) := by
  rw [← Submodule.finrank_map_subtype_eq (range Bᵀ.mulVecLin),
    ← Submodule.finrank_map_subtype_eq (Cycles B) (bicycles B)]
  rw [ker_domRestrict, Submodule.map_comap_subtype, bicycles, Submodule.map_comap_subtype,
    inf_comm (range Bᵀ.mulVecLin), inf_eq_right.mpr inf_le_left]

/-- The residual dimension plus twice the incidence rank equals the number of edges
plus the rank of the binary Laplacian. -/
theorem residual_rank_add_twice_rank {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (B : Matrix V E (ZMod 2)) :
    residualRank B + 2 * B.rank = Fintype.card E + (B * Bᵀ).rank := by
  have hrange : range (B.mulVecLin.domRestrict (range Bᵀ.mulVecLin)) =
      range (B * Bᵀ).mulVecLin := by
    rw [range_domRestrict, Matrix.mulVecLin_mul, range_comp]
  have hswitch := finrank_range_add_finrank_ker (B.mulVecLin.domRestrict (range Bᵀ.mulVecLin))
  rw [hrange, finrank_restricted_ker, ← Matrix.rank, ← Matrix.rank, Matrix.rank_transpose]
    at hswitch
  have hcycles := finrank_range_add_finrank_ker B.mulVecLin
  rw [← Matrix.rank, Module.finrank_pi] at hcycles
  have hquot := (bicycles B).finrank_quotient_add_finrank
  change residualRank B + Module.finrank (ZMod 2) (bicycles B) =
    Module.finrank (ZMod 2) (ker B.mulVecLin) at hquot
  omega

/-- Mathlib incidence restricted to the columns indexed by actual unordered edges. -/
abbrev incidence {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V G.edgeSet (ZMod 2) :=
  (G.incMatrix (ZMod 2)).submatrix _root_.id Subtype.val

/-- The exact number of negative edges at each vertex, using integer incidence weights. -/
def negativeDegree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : G.edgeSet → ZMod 2) : V → ℤ :=
  fun v => ∑ e : G.edgeSet, G.incMatrix ℤ v e.val * (w e).val

/-- Each incident edge contributes one, with a correction of minus two for a negative edge. -/
def signedRow {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : G.edgeSet → ZMod 2) : V → ℤ :=
  fun v => (G.degree v : ℤ) - 2 * negativeDegree G w v

private theorem cast_negativeDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : G.edgeSet → ZMod 2) :
    (fun v => (negativeDegree G w v : ZMod 2)) = (incidence G).mulVecLin w := by
  funext v
  change (↑(∑ e : G.edgeSet, G.incMatrix ℤ v e.val * ((w e).val : ℤ)) : ZMod 2) =
    ∑ e : G.edgeSet, G.incMatrix (ZMod 2) v e.val * w e
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, SimpleGraph.incMatrix_apply']
  split <;> simp_all

private theorem signedRow_eq_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : G.edgeSet → ZMod 2) (q : V → ℤ) :
    signedRow G w = (fun v => (G.degree v : ℤ) - 2 * q v) ↔ negativeDegree G w = q := by
  constructor
  · intro h
    funext v
    have hv := congrFun h v
    change (G.degree v : ℤ) - 2 * negativeDegree G w v = (G.degree v : ℤ) - 2 * q v at hv
    omega
  · intro h
    unfold signedRow
    rw [h]

local notation "sw(" G ", " s ", " z ")" => s + Matrix.mulVecLin (Matrix.transpose (incidence G)) z
local notation "target(" G ", " q ")" => (fun v => (SimpleGraph.degree G v : ℤ) - 2 * q v)

/-- A parity-compatible reference switch puts each exact witness in the affine cycle space.
An exact signed solution exists precisely when an exact witness has zero residual class.
The Laplacian rank balance makes every exact witness lift. -/
theorem exact_signed_rows {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : G.edgeSet → ZMod 2) (z₀ : V → ZMod 2) (q : V → ℤ)
    (parity : (incidence G).mulVecLin (sw(G, s, z₀)) = fun v => (q v : ZMod 2)) :
    (∀ w, negativeDegree G w = q →
      ∃ c : Cycles (incidence G), w = sw(G, s, z₀) + (c : G.edgeSet → ZMod 2)) ∧
    ((∃ z, signedRow G (sw(G, s, z)) = target(G, q)) ↔
      ∃ c : Cycles (incidence G), negativeDegree G (sw(G, s, z₀) + c.val) = q ∧
        (bicycles (incidence G)).mkQ c = 0) ∧
    (2 * (incidence G).rank =
        Fintype.card G.edgeSet + (incidence G * (incidence G)ᵀ).rank →
      (∃ w, negativeDegree G w = q) →
      ∃ z, signedRow G (sw(G, s, z)) = target(G, q)) := by
  have exactToCycle (w : G.edgeSet → ZMod 2) (hw : negativeDegree G w = q) :
      ∃ c : Cycles (incidence G), w = sw(G, s, z₀) + (c : G.edgeSet → ZMod 2) := by
    have hcast := cast_negativeDegree G w
    rw [hw, ← parity] at hcast
    refine ⟨⟨w - sw(G, s, z₀), ?_⟩, ?_⟩
    · rw [mem_ker, map_sub, ← hcast, sub_self]
    · change w = sw(G, s, z₀) + (w - sw(G, s, z₀))
      abel
  have classZero (c : Cycles (incidence G)) :
      (bicycles (incidence G)).mkQ c = 0 ↔
        c.val ∈ range (incidence G)ᵀ.mulVecLin := by
    change (bicycles (incidence G)).mkQ c = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change c.val ∈ Cycles (incidence G) ⊓ range (incidence G)ᵀ.mulVecLin ↔ _
    exact ⟨fun h => h.2, fun h => ⟨c.property, h⟩⟩
  have criterion :
      (∃ z, signedRow G (sw(G, s, z)) = target(G, q)) ↔
        ∃ c : Cycles (incidence G), negativeDegree G (sw(G, s, z₀) + c.val) = q ∧
          (bicycles (incidence G)).mkQ c = 0 := by
    constructor
    · rintro ⟨z, hz⟩
      have hw := (signedRow_eq_iff G _ q).mp hz
      obtain ⟨c, hc⟩ := exactToCycle _ hw
      refine ⟨c, hc ▸ hw, (classZero c).mpr ⟨z - z₀, ?_⟩⟩
      have h : (incidence G)ᵀ.mulVecLin z = (incidence G)ᵀ.mulVecLin z₀ + c.val :=
        add_left_cancel (by simpa only [add_assoc] using hc)
      rw [map_sub, h]
      abel
    · rintro ⟨c, hw, hc⟩
      obtain ⟨t, ht⟩ := (classZero c).mp hc
      refine ⟨z₀ + t, (signedRow_eq_iff G _ q).mpr ?_⟩
      simpa only [map_add, ht, ← add_assoc] using hw
  refine ⟨exactToCycle, criterion, ?_⟩
  intro hbalance
  rintro ⟨w, hw⟩
  have hrank := residual_rank_add_twice_rank (incidence G)
  have hzero : residualRank (incidence G) = 0 := by omega
  haveI : Subsingleton (Cycles (incidence G) ⧸ bicycles (incidence G)) :=
    (Module.finrank_eq_zero_iff_of_free _ _).mp hzero
  obtain ⟨c, hc⟩ := exactToCycle w hw
  exact criterion.mpr ⟨c, hc ▸ hw, Subsingleton.elim _ _⟩

#print axioms residual_rank_add_twice_rank
#print axioms exact_signed_rows

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank
