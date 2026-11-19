/- GID: D5/S3/Combinatorics/Graph/SubgroupGenerating/FiberSpectra
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubgroupGenerating/FiberSpectra
   mirror-E: none(waiver:noncomputable-spectral-transport)
   anchors: []
   utility: none
   digest: The four literal subgroup-generating spectra split into all subgroup star fibers. -/

import D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
import D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The complete subgroup-block decomposition of the four actual source spectra. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix Finset Polynomial
open scoped Classical
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
open D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra

namespace D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra

noncomputable section
variable {G : Type} [Group G] [Fintype G]
attribute [local instance] CyclicExtensionRefutation.subgroupFintype

/-- Each pair belongs to its generated subgroup, and each subgroup is its own center. -/
def component : Vertex G → Subgroup G :=
  Sum.elim (fun p => Subgroup.closure ({p.1,p.2} : Set G)) id

/-- The leaf type over H retains all ordered and repeated generating pairs. -/
abbrev PairFiber (H : Subgroup G) := {p : G × G // Subgroup.closure ({p.1,p.2} : Set G) = H}

local instance (H : Subgroup G) : Fintype (PairFiber H) := Fintype.ofFinite _

private theorem fiber_card (H : Subgroup G) : Fintype.card (PairFiber H) = pairCount H := by
  classical
  simp [PairFiber, pairCount, generatingPairs, Fintype.card_subtype]

private def blockEquiv (H : Subgroup G) :
    {v : Vertex G // component v = H} ≃ Unit ⊕ PairFiber H where
  toFun v := match v with
    | ⟨.inl p,h⟩ => .inr ⟨p,h⟩
    | ⟨.inr _,_⟩ => .inl ()
  invFun v := match v with
    | .inl _ => ⟨.inr H,rfl⟩
    | .inr p => ⟨.inl p.1,p.2⟩
  left_inv v := by
    rcases v with ⟨v,h⟩
    cases v with
    | inl p => rfl
    | inr K => simp only [component, Sum.elim_inr, id_eq] at h; subst K; rfl
  right_inv v := by cases v with | inl u => cases u; rfl | inr p => rfl

theorem degree_pair (p : G × G)
    [Fintype ((sgbGraph G).neighborSet (.inl p))] :
    (sgbGraph G).degree (.inl p) = 1 := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let e : (sgbGraph G).neighborSet (.inl p) ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨.inr (Subgroup.closure ({p.1,p.2} : Set G)),rfl⟩
      left_inv := by
        rintro ⟨v,h⟩
        cases v with
        | inl q => exact False.elim h
        | inr H =>
          apply Subtype.ext
          change Subgroup.closure ({p.1,p.2} : Set G) = H at h
          exact congrArg Sum.inr h
      right_inv := by intro u; cases u; rfl }
  exact (Fintype.card_congr e).trans (by simp)

theorem degree_subgroup (H : Subgroup G)
    [Fintype ((sgbGraph G).neighborSet (.inr H))] :
    (sgbGraph G).degree (.inr H) = pairCount H := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let e : (sgbGraph G).neighborSet (.inr H) ≃ PairFiber H :=
    { toFun := fun v => match v with
        | ⟨.inl p,h⟩ => ⟨p,h⟩
        | ⟨.inr _,h⟩ => False.elim h
      invFun := fun p => ⟨.inl p.1,p.2⟩
      left_inv := by rintro ⟨v,h⟩; cases v with
        | inl p => rfl
        | inr _ => exact False.elim h
      right_inv := by intro p; rfl }
  exact (Fintype.card_congr e).trans (fiber_card H)

private theorem common_pair_pair (p q : G × G) :
    commonNeighbourMatrix (sgbGraph G) (.inl p) (.inl q) =
      if p = q then 0 else if component (.inl p) = component (.inl q) then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · simp [hpq, commonNeighbourMatrix]
  · simp only [commonNeighbourMatrix, Sum.inl.injEq, hpq, ↓reduceIte]
    by_cases hc : component (.inl p) = component (.inl q)
    · rw [if_pos hc]
      norm_cast
      apply Finset.card_eq_one.mpr
      refine ⟨.inr (component (.inl p)),?_⟩
      ext k
      cases k with
      | inl a => simp [sgbGraph]
      | inr H => simp only [component, Sum.elim_inl] at hc
                 simp [sgbGraph, component, ← hc, eq_comm]
    · rw [if_neg hc]
      norm_cast
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      simp only [Finset.mem_filter] at hk
      obtain ⟨_,hk⟩ := hk
      cases k with
      | inl a => exact hk.2.2.1
      | inr H => exact hc ((show component (.inl p) = H from hk.2.2.1).trans
          (show component (.inl q) = H from hk.2.2.2).symm)

private theorem common_pair_subgroup (p : G × G) (H : Subgroup G) :
    commonNeighbourMatrix (sgbGraph G) (.inl p) (.inr H) = 0 := by
  classical
  simp only [commonNeighbourMatrix, Sum.inl_ne_inr, ↓reduceIte, Nat.cast_eq_zero]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  simp only [Finset.mem_filter] at hk
  obtain ⟨_,hk⟩ := hk
  cases k with
  | inl q => exact hk.2.2.1
  | inr K => exact hk.2.2.2

private theorem common_subgroup_subgroup (H K : Subgroup G) :
    commonNeighbourMatrix (sgbGraph G) (.inr H) (.inr K) = 0 := by
  classical
  by_cases h : H = K
  · simp [h, commonNeighbourMatrix]
  · simp only [commonNeighbourMatrix, Sum.inr.injEq, h, ↓reduceIte, Nat.cast_eq_zero]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    simp only [Finset.mem_filter] at hk
    obtain ⟨_,hk⟩ := hk
    cases k with
    | inl p => exact h ((show Subgroup.closure ({p.1,p.2} : Set G) = H from hk.2.2.1).symm.trans hk.2.2.2)
    | inr J => exact hk.2.2.1

private theorem common_subgroup_pair (H : Subgroup G) (p : G × G) :
    commonNeighbourMatrix (sgbGraph G) (.inr H) (.inl p) = 0 := by
  classical
  simp only [commonNeighbourMatrix, Sum.inr_ne_inl, ↓reduceIte, Nat.cast_eq_zero]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  simp only [Finset.mem_filter] at hk
  obtain ⟨_,hk⟩ := hk
  cases k with
  | inl q => exact hk.2.2.2
  | inr K => exact hk.2.2.1

private theorem source_zero_of_component_ne (kind : MatrixKind) (v w : Vertex G)
    (hc : component v ≠ component w) : sourceMatrix (sgbGraph G) kind v w = 0 := by
  classical
  have hvw : v ≠ w := by intro h; exact hc (congrArg component h)
  cases v with
  | inl p =>
    cases w with
    | inl q =>
      have hpq : p ≠ q := by intro he; exact hvw (congrArg Sum.inl he)
      cases kind <;>
        simp [sourceMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, common_pair_pair, hpq, hc, Matrix.diagonal_apply] <;> simp [sgbGraph]
    | inr H =>
      have h : Subgroup.closure ({p.1,p.2} : Set G) ≠ H := hc
      cases kind <;>
        simp [sourceMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, common_pair_subgroup] <;> simp [sgbGraph, h]
  | inr H =>
    cases w with
    | inl p =>
      have h : Subgroup.closure ({p.1,p.2} : Set G) ≠ H := Ne.symm hc
      cases kind <;>
        simp [sourceMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, common_subgroup_pair] <;> simp [sgbGraph, h]
    | inr K =>
      have h : H ≠ K := hc
      cases kind <;>
        simp [sourceMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, common_subgroup_subgroup, h, Matrix.diagonal_apply] <;> simp [sgbGraph]

private theorem source_block (H : Subgroup G) (kind : MatrixKind) :
    Matrix.reindex (blockEquiv H) (blockEquiv H)
      ((sourceMatrix (sgbGraph G) kind).toSquareBlock component H) =
      sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ PairFiber H)) kind := by
  classical
  rw [star_matrix]
  ext (i | i) (j | j)
  · cases i; cases j; cases kind <;>
      simp [Matrix.reindex_apply, Matrix.toSquareBlock_def, blockEquiv, sourceMatrix,
        SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        degree_subgroup, common_subgroup_subgroup, arrowMatrix, fiber_card] <;>
        simpa only [← SimpleGraph.ncard_neighborSet] using (degree_subgroup H)
  · cases i; cases kind <;>
      simp [Matrix.reindex_apply, Matrix.toSquareBlock_def, blockEquiv, sourceMatrix,
        SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        common_subgroup_pair, arrowMatrix, j.property] <;> simp [sgbGraph, j.property]
  · cases j; cases kind <;>
      simp [Matrix.reindex_apply, Matrix.toSquareBlock_def, blockEquiv, sourceMatrix,
        SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        common_pair_subgroup, arrowMatrix, i.property] <;> simp [sgbGraph, i.property]
  · have hij : i.1 = j.1 ↔ i = j := Subtype.val_inj
    cases kind <;>
      simp [Matrix.reindex_apply, Matrix.toSquareBlock_def, blockEquiv, sourceMatrix,
        SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        degree_pair, common_pair_pair, arrowMatrix, Matrix.diagonal_apply, Matrix.one_apply,
        component, i.property, j.property, hij, Matrix.vecMulVec, Matrix.scalar] <;>
        (try simp [sgbGraph]) <;> (split_ifs <;> norm_num)

/-- All four source spectra are the sum of their complete subgroup star spectra. -/
theorem sgb_spectrum (kind : MatrixKind) :
    graphSpectrum (sgbGraph G) kind = ∑ H : Subgroup G, starValues (pairCount H) kind := by
  classical
  letI : LinearOrder (Subgroup G) := LinearOrder.lift' (Fintype.equivFin (Subgroup G))
    (Fintype.equivFin (Subgroup G)).injective
  letI : LT (Subgroup G) := (inferInstance : LinearOrder (Subgroup G)).toLT
  have hb : (sourceMatrix (sgbGraph G) kind).BlockTriangular component := by
    intro v w hvw
    exact source_zero_of_component_ne kind v w (by
      intro he
      rw [he] at hvw
      exact (show ¬ (component w < component w) from @lt_irrefl _ (inferInstance : LinearOrder (Subgroup G)).toPreorder _) hvw)
  have himage : Finset.univ.image (component (G := G)) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro H
    exact Finset.mem_image.mpr ⟨Sum.inr H,Finset.mem_univ _,rfl⟩
  have hc : (sourceMatrix (sgbGraph G) kind).charpoly =
      ∏ H : Subgroup G,
        (sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ PairFiber H)) kind).charpoly := by
    rw [hb.charpoly,himage]
    apply Finset.prod_congr rfl
    intro H _
    rw [← Matrix.charpoly_reindex (blockEquiv H), source_block]
  have hr : (sourceMatrix (sgbGraph G) kind).charpoly.roots = graphSpectrum (sgbGraph G) kind :=
    (source_matrix_isHermitian _ kind).roots_charpoly_eq_eigenvalues
  rw [← hr,hc,Polynomial.roots_prod _ _ (by
    exact Finset.prod_ne_zero_iff.mpr (fun H _ => (Matrix.charpoly_monic _).ne_zero))]
  change (∑ H : Subgroup G, (sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ PairFiber H)) kind).charpoly.roots) = _
  apply Finset.sum_congr rfl
  intro H _
  have hrH : (sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ PairFiber H)) kind).charpoly.roots =
      graphSpectrum (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ PairFiber H)) kind :=
    (source_matrix_isHermitian _ kind).roots_charpoly_eq_eigenvalues
  rw [hrH,star_spectrum,fiber_card]

/-- Every ordered pair contributes precisely its one actual graph edge. -/
theorem edge_count : (sgbGraph G).edgeFinset.card = Fintype.card G ^ 2 := by
  classical
  have h := (sgbGraph G).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at h
  simp only [degree_pair, degree_subgroup, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one, Fintype.card_prod, sum_pairCount] at h
  nlinarith

end
end D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra
