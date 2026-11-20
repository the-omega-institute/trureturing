/- GID: D5/S3/Geometry/DiscreteGravity/TreeConstantRatios
   generality: G
   mirror-B: D5/B/S3/Geometry/DiscreteGravity/TreeConstantRatios
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: A positive tree-equation solution has constant lengths iff constant vertex ratios. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#129)
escape_witness: ratio_of_const (with every incident length c > 0 and a neighbour, the vertex
  ratio c_i/d_i equals c), with the connected-tree step giving every vertex a neighbour.
proof_shape:
  ratio_of_const: content; consumer: constant_iff.
  constant_iff: content via ratio_of_const; the converse solves the edge equation
    2R²/ℓ − 2R = 0 at a constant ratio R > 0.
Direct frozen dependency: D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation
  (cVal, dVal, ratio, tEoM).
Search: the frozen TreeEquationsNonconstantRefutation proves only the cubic-tree negation
`result : ¬ claim`; its construction lemmas are private and do not state this equivalence.
Mathlib's Preconnected.exists_adj_of_nontrivial and degree_pos_iff_exists_adj are reused.
-/

import D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation

/-! # Constant lengths and constant vertex ratios on trees

For the tree equations of motion of Huang, Stoica, Xia and Zhong, put
`c_i = Σ_{j∼i} 1/ℓ_ij`, `d_i = Σ_{j∼i} 1/ℓ_ij²` and `R_i = c_i/d_i`. On a connected locally
finite tree with at least one edge, a positive symmetric solution of
`(R_i² + R_j²)/ℓ_ij − R_i − R_j = 0` has constant edge lengths if and only if the vertex ratios
are constant, the common ratio then being positive.
-/

set_option autoImplicit false

namespace D5.S3.Geometry.DiscreteGravity.TreeConstantRatios

open D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation

/-- With every incident length equal to `c > 0` and at least one neighbour, the vertex ratio
`c_i / d_i` equals `c`. -/
private lemma ratio_of_const {v : Type} (g : SimpleGraph v) [g.LocallyFinite]
    (ell : v → v → ℝ) (c : ℝ) (hc : 0 < c) (i : v) (hi : 0 < g.degree i)
    (hell : ∀ j, g.Adj i j → ell i j = c) : ratio g ell i = c := by
  have hcv : cVal g ell i = g.degree i * (1 / c) := by
    unfold cVal
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [hell j ((g.mem_neighborFinset i j).1 hj)]), Finset.sum_const, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree]
  have hdv : dVal g ell i = g.degree i * (1 / c ^ 2) := by
    unfold dVal
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [hell j ((g.mem_neighborFinset i j).1 hj)]), Finset.sum_const, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree]
  have hd : (0 : ℝ) < g.degree i := by exact_mod_cast hi
  unfold ratio
  rw [hcv, hdv]
  field_simp

/-- On a connected locally finite tree with an edge, a positive symmetric solution of the tree
equations has globally constant edge lengths iff its vertex ratios are globally equal to some
`R > 0`. -/
theorem constant_iff {v : Type} (g : SimpleGraph v) [g.LocallyFinite] (hT : g.IsTree)
    (hedge : ∃ i j, g.Adj i j) (ell : v → v → ℝ)
    (_hsym : ∀ i j, g.Adj i j → ell i j = ell j i)
    (hpos : ∀ i j, g.Adj i j → 0 < ell i j)
    (hsol : ∀ i j, g.Adj i j → tEoM g ell i j = 0) :
    (∃ c, ∀ i j, g.Adj i j → ell i j = c) ↔ ∃ R, 0 < R ∧ ∀ i, ratio g ell i = R := by
  obtain ⟨a, b, hab⟩ := hedge
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : 0 < c := hc a b hab ▸ hpos a b hab
    have : Nontrivial v := ⟨⟨a, b, hab.ne⟩⟩
    refine ⟨c, hc0, fun i => ratio_of_const g ell c hc0 i ?_ (hc i)⟩
    obtain ⟨j, hj⟩ := hT.connected.preconnected.exists_adj_of_nontrivial i
    exact (g.degree_pos_iff_exists_adj i).2 ⟨j, hj⟩
  · rintro ⟨R, hR, hratio⟩
    refine ⟨R, fun i j hij => ?_⟩
    have h := hsol i j hij
    have hl := hpos i j hij
    unfold tEoM at h
    rw [hratio i, hratio j] at h
    field_simp at h
    nlinarith

end D5.S3.Geometry.DiscreteGravity.TreeConstantRatios
