/- GID: D5/S3/Combinatorics/OuterIndependentRoman/CactusSupports
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OuterIndependentRoman/CactusSupports
   mirror-E: none(waiver:counting-bound)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected]
   utility: none
   digest: Support vertices of a connected graph of order at least three occupy at most half. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OuterIndependentRoman.CactusSupports

open SimpleGraph

/-- Choosing a leaf for each support gives a disjoint second copy of the support vertices. -/
theorem support_card_bound {V : Type*} [Fintype V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.Connected) (hn : 3 ≤ Fintype.card V) :
    2 * ({v | ∃ u, T.Adj v u ∧ T.degree u = 1} : Set V).toFinset.card ≤
      Fintype.card V := by
  classical
  let S : Finset V := ({v | ∃ u, T.Adj v u ∧ T.degree u = 1} : Set V).toFinset
  have hS (v : S) : ∃ u, T.Adj (v : V) u ∧ T.degree u = 1 := by
    simpa only [S, Set.mem_toFinset, Set.mem_ofPred_eq] using v.property
  choose leaf hAdj hDegree using hS
  have hnotleaf (v : S) : T.degree (v : V) ≠ 1 := by
    intro hv
    let u := leaf v
    have huv : T.Adj (v : V) u := hAdj v
    have hdu : T.degree u = 1 := hDegree v
    have huniqv := degree_eq_one_iff_existsUnique_adj.mp hv
    have huniqu := degree_eq_one_iff_existsUnique_adj.mp hdu
    have hwalk : ∀ {x y : V}, T.Walk x y →
        (x = (v : V) ∨ x = u) → (y = (v : V) ∨ y = u) := by
      intro x y p
      induction p with
      | nil => exact id
      | @cons x z y hxz p ih =>
        intro hx
        apply ih
        rcases hx with rfl | rfl
        · exact Or.inr (huniqv.unique hxz huv)
        · exact Or.inl (huniqu.unique hxz huv.symm)
    have hcover : (Finset.univ : Finset V) ⊆ {(v : V), u} := by
      intro x _
      have hx := hwalk (hT.preconnected (v : V) x).some (Or.inl rfl)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    have hcard := Finset.card_le_card hcover
    have hpair : ({(v : V), u} : Finset V).card ≤ 2 := by
      exact Finset.card_insert_le _ _ |>.trans (by simp)
    simp only [Finset.card_univ] at hcard
    omega
  have hleafinj : Function.Injective leaf := by
    intro v w h
    have hu := degree_eq_one_iff_existsUnique_adj.mp (hDegree v)
    apply Subtype.ext
    exact hu.unique (hAdj v).symm (h ▸ (hAdj w).symm)
  let e : S ⊕ S → V := Sum.elim Subtype.val leaf
  have he : Function.Injective e := by
    intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl w => exact congrArg Sum.inl (Subtype.ext h)
      | inr w =>
        change (v : V) = leaf w at h
        exact (hnotleaf v (h.symm ▸ hDegree w)).elim
    | inr v =>
      cases y with
      | inl w =>
        change leaf v = (w : V) at h
        exact (hnotleaf w (h ▸ hDegree v)).elim
      | inr w => exact congrArg Sum.inr (hleafinj h)
  have hcard := Fintype.card_le_of_injective e he
  simp only [Fintype.card_sum, Fintype.card_coe] at hcard
  change 2 * S.card ≤ Fintype.card V
  omega

#print axioms support_card_bound

end D5.S3.Combinatorics.OuterIndependentRoman.CactusSupports
