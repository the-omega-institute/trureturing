/- GID: D5/S3/ConceptDynamics/Spacetime/HistoricalCongruence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/HistoricalCongruence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Historical isomorphisms transport native operations and exactly preserve the temporal domain. -/

import D5.S3.ConceptDynamics.Spacetime.HistoricalEquivalence
import D5.S3.ConceptDynamics.Spacetime.GeneratedProduct
import D5.S3.ConceptDynamics.Spacetime.TemporalComposition
import Mathlib.Order.RelIso.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.HistoricalCongruence

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S0.History.Spacetime.HFEncoding


noncomputable section
local instance : DecidableEq HF := Classical.decEq _
variable {d : Nat} {x x' y y' : Rich d}

private def current_equiv (hx : HistoricalEquivalence.HistoricalIsoData x x') :
    ↥x.1.current ≃ ↥x'.1.current :=
  hx.eventEquiv.subtypeEquiv fun u => by
    change u ∈ x.1.current ↔ hx.eventMap u ∈ x'.1.current
    rw [← hx.current_image, Finset.mem_map']

private theorem selected_parents_map (hx : HistoricalEquivalence.HistoricalIsoData x x') :
    (ProductNodes.selectedParents x.2).map (current_equiv hx).toEmbedding =
      ProductNodes.selectedParents x'.2 := by
  apply Finset.ext
  intro v
  obtain ⟨u, rfl⟩ := (current_equiv hx).surjective v
  calc
    (current_equiv hx) u ∈ (ProductNodes.selectedParents x.2).map
        (current_equiv hx).toEmbedding ↔ u ∈ ProductNodes.selectedParents x.2 :=
      Finset.mem_map' (current_equiv hx).toEmbedding
    _ ↔ u.val ∈ x.2.val := ProductNodes.mem_selectedParents _ _
    _ ↔ hx.eventMap u.val ∈ x'.2.val := by
      rw [← hx.selection_image, Finset.mem_map']
    _ ↔ (current_equiv hx) u ∈ ProductNodes.selectedParents x'.2 := by
      exact (ProductNodes.mem_selectedParents x'.2 ((current_equiv hx) u)).symm

private theorem parallel_relation_boundary (a b : Archive d) (u v : ParallelComposition.Node a b) :
    ParallelComposition.internal a b u v ↔ Sum.LiftRel a.causal b.causal u v := by
  cases u <;> cases v <;> simp [ParallelComposition.internal]

private theorem temporal_relation_boundary (a b : Archive d) (u v : ParallelComposition.Node a b) :
    TemporalComposition.edge a b u v ↔ Sum.Lex a.causal b.causal u v := by
  cases u <;> cases v <;> simp [TemporalComposition.edge]

private def parallel_data (hx : HistoricalEquivalence.HistoricalIsoData x x')
    (hy : HistoricalEquivalence.HistoricalIsoData y y') :
    HistoricalEquivalence.HistoricalIsoData (ParallelComposition.parallel x y) (ParallelComposition.parallel x' y') := by
  let n := Equiv.sumCongr hx.eventEquiv hy.eventEquiv
  let f := (ParallelComposition.equiv x.1.archive y.1.archive).symm.trans
    (n.trans (ParallelComposition.equiv x'.1.archive y'.1.archive))
  have hl : (ParallelComposition.left x.1.archive y.1.archive).trans f.toEmbedding =
      hx.eventMap.trans (ParallelComposition.left x'.1.archive y'.1.archive) := by
    apply Function.Embedding.ext
    intro u
    simp [f, n, ParallelComposition.left, Function.Embedding.trans_apply,
      HistoricalEquivalence.HistoricalIsoData.eventEquiv]
  have hr : (ParallelComposition.right x.1.archive y.1.archive).trans f.toEmbedding =
      hy.eventMap.trans (ParallelComposition.right x'.1.archive y'.1.archive) := by
    apply Function.Embedding.ext
    intro u
    simp [f, n, ParallelComposition.right, Function.Embedding.trans_apply,
      HistoricalEquivalence.HistoricalIsoData.eventEquiv]
  refine {
    eventMap := f.toEmbedding
    onto := f.surjective
    attributes_eq := ?_
    causal_iff := ?_
    current_image := ?_
    selection_image := ?_ }
  · intro e
    obtain ⟨u, rfl⟩ := (ParallelComposition.equiv x.1.archive y.1.archive).surjective e
    change (ParallelComposition.archive _ _).attributes (f (ParallelComposition.equiv _ _ u)) =
      (ParallelComposition.archive _ _).attributes (ParallelComposition.equiv _ _ u)
    simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply]
    cases u with
    | inl u =>
        exact (ParallelComposition.attributes_left x'.1.archive y'.1.archive _).trans
          ((hx.attributes_eq u).trans (ParallelComposition.attributes_left _ _ u).symm)
    | inr u =>
        exact (ParallelComposition.attributes_right x'.1.archive y'.1.archive _).trans
          ((hy.attributes_eq u).trans (ParallelComposition.attributes_right _ _ u).symm)
  · intro e k
    obtain ⟨u, rfl⟩ := (ParallelComposition.equiv x.1.archive y.1.archive).surjective e
    obtain ⟨v, rfl⟩ := (ParallelComposition.equiv x.1.archive y.1.archive).surjective k
    change (ParallelComposition.archive _ _).causal (f (ParallelComposition.equiv _ _ u)) (f (ParallelComposition.equiv _ _ v)) ↔
      (ParallelComposition.archive _ _).causal (ParallelComposition.equiv _ _ u) (ParallelComposition.equiv _ _ v)
    simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply, ParallelComposition.causal_cases,
      parallel_relation_boundary]
    exact (RelEmbedding.sumLiftRelMap
      (⟨hx.eventMap, fun {a b} => hx.causal_iff a b⟩ : x.1.archive.causal ↪r x'.1.archive.causal)
      (⟨hy.eventMap, fun {a b} => hy.causal_iff a b⟩ : y.1.archive.causal ↪r y'.1.archive.causal)).map_rel_iff
  · change ((ParallelComposition.context x.1 y.1).current).map f.toEmbedding =
      (ParallelComposition.context x'.1 y'.1).current
    rw [ParallelComposition.current_eq, Finset.map_union, Finset.map_map, Finset.map_map, hl, hr,
      ← Finset.map_map, ← Finset.map_map, hx.current_image, hy.current_image, ParallelComposition.current_eq]
  · change (ParallelComposition.selection x.2 y.2).val.map f.toEmbedding = (ParallelComposition.selection x'.2 y'.2).val
    rw [ParallelComposition.selection_eq, Finset.map_union, Finset.map_map, Finset.map_map, hl, hr,
      ← Finset.map_map, ← Finset.map_map, hx.selection_image, hy.selection_image,
      ParallelComposition.selection_eq]

/-- Transport the four native generators, with the actual mapped current parents. -/
private theorem product_edge_transport (hx : HistoricalEquivalence.HistoricalIsoData x x')
    (hy : HistoricalEquivalence.HistoricalIsoData y y')
    (cx : ↥x.1.current ≃ ↥x'.1.current) (cy : ↥y.1.current ≃ ↥y'.1.current)
    (hcx : ∀ u, (cx u).val = hx.eventEquiv u.val)
    (hcy : ∀ v, (cy v).val = hy.eventEquiv v.val) :
    let n := Equiv.sumCongr (Equiv.sumCongr hx.eventEquiv hy.eventEquiv)
      (Equiv.prodCongr cx cy)
    ∀ u v, ProductPaths.Edge x'.1 y'.1 (n u) (n v) ↔ ProductPaths.Edge x.1 y.1 u v := by
  dsimp only
  let n := Equiv.sumCongr (Equiv.sumCongr hx.eventEquiv hy.eventEquiv)
    (Equiv.prodCongr cx cy)
  have forward : ∀ u v, ProductPaths.Edge x.1 y.1 u v → ProductPaths.Edge x'.1 y'.1 (n u) (n v) := by
    intro u v h
    cases h with
    | left h => exact ProductPaths.Edge.left ((hx.causal_iff _ _).mpr h)
    | right h => exact ProductPaths.Edge.right ((hy.causal_iff _ _).mpr h)
    | parentLeft p =>
      change ProductPaths.Edge x'.1 y'.1 (ProductNodes.oldLeft _ _ (hx.eventEquiv p.1.val))
        (ProductNodes.generated _ _ (cx p.1, cy p.2))
      rw [← hcx]
      exact @ProductPaths.Edge.parentLeft d x'.1 y'.1 (cx p.1, cy p.2)
    | parentRight p =>
      change ProductPaths.Edge x'.1 y'.1 (ProductNodes.oldRight _ _ (hy.eventEquiv p.2.val))
        (ProductNodes.generated _ _ (cx p.1, cy p.2))
      rw [← hcy]
      exact @ProductPaths.Edge.parentRight d x'.1 y'.1 (cx p.1, cy p.2)
  have hcxi (u : ↥x'.1.current) : (cx.symm u).val = hx.eventEquiv.symm u.val := by
    apply hx.eventEquiv.injective
    rw [← hcx, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hcyi (v : ↥y'.1.current) : (cy.symm v).val = hy.eventEquiv.symm v.val := by
    apply hy.eventEquiv.injective
    rw [← hcy, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have backward : ∀ u v, ProductPaths.Edge x'.1 y'.1 u v →
      ProductPaths.Edge x.1 y.1 (n.symm u) (n.symm v) := by
    intro u v h
    cases h with
    | left h =>
      apply ProductPaths.Edge.left
      apply (hx.causal_iff _ _).mp
      change x'.1.archive.causal (hx.eventEquiv (hx.eventEquiv.symm _))
        (hx.eventEquiv (hx.eventEquiv.symm _))
      simpa only [Equiv.apply_symm_apply] using h
    | right h =>
      apply ProductPaths.Edge.right
      apply (hy.causal_iff _ _).mp
      change y'.1.archive.causal (hy.eventEquiv (hy.eventEquiv.symm _))
        (hy.eventEquiv (hy.eventEquiv.symm _))
      simpa only [Equiv.apply_symm_apply] using h
    | parentLeft p =>
      change ProductPaths.Edge x.1 y.1 (ProductNodes.oldLeft _ _ (hx.eventEquiv.symm p.1.val))
        (ProductNodes.generated _ _ (cx.symm p.1, cy.symm p.2))
      rw [← hcxi]
      exact @ProductPaths.Edge.parentLeft d x.1 y.1 (cx.symm p.1, cy.symm p.2)
    | parentRight p =>
      change ProductPaths.Edge x.1 y.1 (ProductNodes.oldRight _ _ (hy.eventEquiv.symm p.2.val))
        (ProductNodes.generated _ _ (cx.symm p.1, cy.symm p.2))
      rw [← hcyi]
      exact @ProductPaths.Edge.parentRight d x.1 y.1 (cx.symm p.1, cy.symm p.2)
  intro u v
  exact ⟨fun h => by simpa only [Equiv.symm_apply_apply] using backward (n u) (n v) h,
    forward u v⟩

private def product_data (hx : HistoricalEquivalence.HistoricalIsoData x x')
    (hy : HistoricalEquivalence.HistoricalIsoData y y') :
    HistoricalEquivalence.HistoricalIsoData (GeneratedProduct.product x y) (GeneratedProduct.product x' y') := by
  let cx := current_equiv hx
  let cy := current_equiv hy
  let p := Equiv.prodCongr cx cy
  let n := Equiv.sumCongr (Equiv.sumCongr hx.eventEquiv hy.eventEquiv) p
  let f := (GeneratedProduct.equiv x.1 y.1).symm.trans (n.trans (GeneratedProduct.equiv x'.1 y'.1))
  have hm : (GeneratedProduct.generatedMap x.1 y.1).trans f.toEmbedding =
      p.toEmbedding.trans (GeneratedProduct.generatedMap x'.1 y'.1) := by
    apply Function.Embedding.ext
    intro u
    simp [f, n, GeneratedProduct.generatedMap, Function.Embedding.trans_apply]
  have hp : (ProductNodes.selectedParents x.2 ×ˢ ProductNodes.selectedParents y.2).map p.toEmbedding =
      ProductNodes.selectedParents x'.2 ×ˢ ProductNodes.selectedParents y'.2 := by
    change (ProductNodes.selectedParents x.2 ×ˢ ProductNodes.selectedParents y.2).map
      ((current_equiv hx).toEmbedding.prodMap (current_equiv hy).toEmbedding) = _
    rw [Finset.prodMap_map_product, selected_parents_map hx, selected_parents_map hy]
  refine {
    eventMap := f.toEmbedding
    onto := f.surjective
    attributes_eq := ?_
    causal_iff := ?_
    current_image := ?_
    selection_image := ?_ }
  · intro e
    obtain ⟨u, rfl⟩ := (GeneratedProduct.equiv x.1 y.1).surjective e
    change (GeneratedProduct.archive _ _).attributes (f (GeneratedProduct.equiv _ _ u)) =
      (GeneratedProduct.archive _ _).attributes (GeneratedProduct.equiv _ _ u)
    simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply]
    rcases u with (u | v) | w
    · exact (GeneratedProduct.attributes_left _ _ _).trans
        ((hx.attributes_eq u).trans (GeneratedProduct.attributes_left _ _ u).symm)
    · exact (GeneratedProduct.attributes_right _ _ _).trans
        ((hy.attributes_eq v).trans (GeneratedProduct.attributes_right _ _ v).symm)
    · change (GeneratedProduct.archive _ _).attributes (GeneratedProduct.generatedMap _ _ (p w)) =
        (GeneratedProduct.archive _ _).attributes (GeneratedProduct.generatedMap _ _ w)
      rw [GeneratedProduct.attributes_generated, GeneratedProduct.attributes_generated]
      change ProductNodes.generatedAttributes x'.1 y'.1
        (current_equiv hx w.1, current_equiv hy w.2) = ProductNodes.generatedAttributes x.1 y.1 w
      unfold ProductNodes.generatedAttributes
      simp only [current_equiv, Equiv.subtypeEquiv_apply, HistoricalEquivalence.HistoricalIsoData.eventEquiv,
        Equiv.ofBijective_apply, hx.attributes_eq, hy.attributes_eq]
  · intro e k
    obtain ⟨u, rfl⟩ := (GeneratedProduct.equiv x.1 y.1).surjective e
    obtain ⟨v, rfl⟩ := (GeneratedProduct.equiv x.1 y.1).surjective k
    change (GeneratedProduct.archive _ _).causal (f (GeneratedProduct.equiv _ _ u)) (f (GeneratedProduct.equiv _ _ v)) ↔
      (GeneratedProduct.archive _ _).causal (GeneratedProduct.equiv _ _ u) (GeneratedProduct.equiv _ _ v)
    simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply, GeneratedProduct.causal_equiv]
    have he : ∀ u v, ProductPaths.Edge x'.1 y'.1 (n u) (n v) ↔ ProductPaths.Edge x.1 y.1 u v :=
      product_edge_transport hx hy cx cy (fun _ => rfl) (fun _ => rfl)
    constructor
    · intro h
      have hi : ∀ u v, ProductPaths.Edge x'.1 y'.1 u v →
          ProductPaths.Edge x.1 y.1 (n.symm u) (n.symm v) := by
        intro u v huv
        exact (he _ _).mp (by simpa only [Equiv.apply_symm_apply] using huv)
      simpa only [Function.onFun, Equiv.symm_apply_apply] using Relation.TransGen.lift n.symm hi _ _ h
    · exact Relation.TransGen.lift n (fun u v => (he u v).mpr) _ _
  · change (Finset.univ.map (GeneratedProduct.generatedMap _ _)).map f.toEmbedding =
      Finset.univ.map (GeneratedProduct.generatedMap _ _)
    rw [Finset.map_map, hm, ← Finset.map_map, Finset.map_univ_equiv]
  · change ((ProductNodes.selectedParents x.2 ×ˢ ProductNodes.selectedParents y.2).map
      (GeneratedProduct.generatedMap _ _)).map f.toEmbedding =
      (ProductNodes.selectedParents x'.2 ×ˢ ProductNodes.selectedParents y'.2).map (GeneratedProduct.generatedMap _ _)
    rw [Finset.map_map, hm, ← Finset.map_map, hp]

private def complement_data (hx : HistoricalEquivalence.HistoricalIsoData x x') :
    HistoricalEquivalence.HistoricalIsoData (ComplementCharge.complementRich x) (ComplementCharge.complementRich x') := by
  refine HistoricalEquivalence.HistoricalIsoData.mk hx.toArchiveEmbedding hx.onto hx.current_image ?_
  change (x.1.current \ x.2.val).map hx.eventMap = x'.1.current \ x'.2.val
  rw [Finset.map_sdiff, hx.current_image, hx.selection_image]

private theorem temporal_guard_iff_data (hx : HistoricalEquivalence.HistoricalIsoData x x')
    (hy : HistoricalEquivalence.HistoricalIsoData y y') :
    TemporalComposition.Guard x.1.archive y.1.archive ↔ TemporalComposition.Guard x'.1.archive y'.1.archive := by
  constructor
  · intro h e f
    obtain ⟨u, rfl⟩ := hx.eventEquiv.surjective e
    obtain ⟨v, rfl⟩ := hy.eventEquiv.surjective f
    change (x'.1.archive.attributes (hx.eventMap u)).time <
      (y'.1.archive.attributes (hy.eventMap v)).time
    rw [hx.attributes_eq, hy.attributes_eq]
    exact h u v
  · intro h e f
    have hh := h (hx.eventMap e) (hy.eventMap f)
    simpa only [hx.attributes_eq, hy.attributes_eq] using hh

private def temporal_data (hx : HistoricalEquivalence.HistoricalIsoData x x')
    (hy : HistoricalEquivalence.HistoricalIsoData y y')
    (g : TemporalComposition.Guard x.1.archive y.1.archive) (g' : TemporalComposition.Guard x'.1.archive y'.1.archive) :
    HistoricalEquivalence.HistoricalIsoData (TemporalComposition.temporal x y g) (TemporalComposition.temporal x' y' g') := by
  let n := Equiv.sumCongr hx.eventEquiv hy.eventEquiv
  let f := (TemporalComposition.equiv x.1.archive y.1.archive g).symm.trans
    (n.trans (TemporalComposition.equiv x'.1.archive y'.1.archive g'))
  refine {
    eventMap := f.toEmbedding
    onto := f.surjective
    attributes_eq := (parallel_data hx hy).attributes_eq
    current_image := (parallel_data hx hy).current_image
    selection_image := (parallel_data hx hy).selection_image
    causal_iff := ?_ }
  intro e k
  obtain ⟨u, rfl⟩ := (TemporalComposition.equiv x.1.archive y.1.archive g).surjective e
  obtain ⟨v, rfl⟩ := (TemporalComposition.equiv x.1.archive y.1.archive g).surjective k
  change (TemporalComposition.archive _ _ g').causal (f (TemporalComposition.equiv _ _ g u)) (f (TemporalComposition.equiv _ _ g v)) ↔
    (TemporalComposition.archive _ _ g).causal (TemporalComposition.equiv _ _ g u) (TemporalComposition.equiv _ _ g v)
  simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply, TemporalComposition.causal_equiv,
    temporal_relation_boundary]
  exact (RelIso.sumLexCongr
    (⟨hx.eventEquiv, fun {a b} => hx.causal_iff a b⟩ : x.1.archive.causal ≃r x'.1.archive.causal)
    (⟨hy.eventEquiv, fun {a b} => hy.causal_iff a b⟩ : y.1.archive.causal ≃r y'.1.archive.causal)).map_rel_iff

/-- Full-archive equivalence and congruence, including both temporal-domain directions. -/
theorem historical_congruence {d : Nat} :
    Equivalence (HistoricalEquivalence.HistoricalIso (d := d)) ∧
    (∀ {x x' y y' : Rich d}, HistoricalEquivalence.HistoricalIso x x' → HistoricalEquivalence.HistoricalIso y y' →
      HistoricalEquivalence.HistoricalIso (ParallelComposition.parallel x y) (ParallelComposition.parallel x' y')) ∧
    (∀ {x x' y y' : Rich d}, HistoricalEquivalence.HistoricalIso x x' → HistoricalEquivalence.HistoricalIso y y' →
      HistoricalEquivalence.HistoricalIso (GeneratedProduct.product x y) (GeneratedProduct.product x' y')) ∧
    (∀ {x x' : Rich d}, HistoricalEquivalence.HistoricalIso x x' →
      HistoricalEquivalence.HistoricalIso (ComplementCharge.complementRich x) (ComplementCharge.complementRich x')) ∧
    (∀ {x x' y y' : Rich d}, HistoricalEquivalence.HistoricalIso x x' → HistoricalEquivalence.HistoricalIso y y' →
      (TemporalComposition.Guard x.1.archive y.1.archive ↔ TemporalComposition.Guard x'.1.archive y'.1.archive) ∧
      (∀ (g : TemporalComposition.Guard x.1.archive y.1.archive) (g' : TemporalComposition.Guard x'.1.archive y'.1.archive),
        HistoricalEquivalence.HistoricalIso (TemporalComposition.temporal x y g) (TemporalComposition.temporal x' y' g'))) := by
  refine ⟨⟨HistoricalEquivalence.historical_iso_refl, HistoricalEquivalence.historical_iso_symm, HistoricalEquivalence.historical_iso_trans⟩,
    ?_, ?_, ?_, ?_⟩
  · rintro x x' y y' ⟨hx⟩ ⟨hy⟩
    exact ⟨parallel_data hx hy⟩
  · rintro x x' y y' ⟨hx⟩ ⟨hy⟩
    exact ⟨product_data hx hy⟩
  · rintro x x' ⟨hx⟩
    exact ⟨complement_data hx⟩
  · rintro x x' y y' ⟨hx⟩ ⟨hy⟩
    exact ⟨temporal_guard_iff_data hx hy, fun g g' => ⟨temporal_data hx hy g g'⟩⟩

end
end D5.S3.ConceptDynamics.Spacetime.HistoricalCongruence
