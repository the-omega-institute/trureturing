/- GID: D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/LeafSquareReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual filtered product reads the finite sum of leaf source-charge squares. -/

import D5.S3.ConceptDynamics.Spacetime.GeneratedProduct
import Mathlib.Data.Finsupp.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.LeafSquareReadout

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S0.History.Spacetime.SourceTreeEncoding
open ComplementCharge ProductNodes GeneratedProduct

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Definition 13: only selection changes; the entire dependent Context is identical. -/
def sourceFilter (L : Set SourceTree) (x : Rich 3) : Rich 3 :=
  ⟨x.1, ⟨x.2.val.filter (fun e => (x.1.archive.attributes e).source ∈ L),
    (Finset.filter_subset _ _).trans x.2.property⟩⟩

/-- Definition 13 balanced lift, used on the actual generated product in the readout. -/
def sourceFilterBalanced (L : Set SourceTree) (X : BalancedRich 3) : BalancedRich 3 :=
  ⟨sourceFilter L X.val, X.property⟩

/-- The P68 source function is the sum of signed singletons over actual selected occurrences. -/
def sourceCharge (x : Rich 3) : SourceTree →₀ Int :=
  ∑ e ∈ x.2.val, Finsupp.single (x.1.archive.attributes e).source (contribution x.1 e)

/-- P68 coefficient and singleton-filter representation, consumed by the square readout. -/
theorem source_charge_apply (x : Rich 3) (r : SourceTree) :
    sourceCharge x r =
      ∑ e ∈ x.2.val.filter (fun e => (x.1.archive.attributes e).source = r), contribution x.1 e ∧
    sourceCharge x r = q (sourceFilter {r} x) := by
  have h : sourceCharge x r =
      ∑ e ∈ x.2.val.filter (fun e => (x.1.archive.attributes e).source = r),
        contribution x.1 e := by
    simp [sourceCharge, Finsupp.single_apply, Finsupp.finsetSum_apply, Finset.sum_filter]
  exact ⟨h, by simpa [q, sourceFilter, readout, charge] using h⟩

/-- The fixed P68 parameter compares equal leaf sources, not occurrence identities. -/
def equalLeafSources : Set SourceTree :=
  Set.range (fun j : Nat => FreeMagma.mul (FreeMagma.of j) (FreeMagma.of j))

private theorem pair_mem_equalLeafSources (r s : SourceTree) :
    FreeMagma.mul r s ∈ equalLeafSources ↔ r = s ∧ r ∈ Set.range FreeMagma.of := by
  constructor
  · rintro ⟨j, h⟩
    have hp : FreeMagma.of j = r ∧ FreeMagma.of j = s := by injection h with h₁ h₂; exact ⟨h₁, h₂⟩
    exact ⟨hp.1.symm.trans hp.2, ⟨j, hp.1⟩⟩
  · rintro ⟨rfl, j, rfl⟩
    exact ⟨j, rfl⟩

private theorem selectedParents_filter (x : Rich 3) (r : SourceTree) :
    selectedParents (sourceFilter {r} x).2 =
      (selectedParents x.2).filter (fun e => (x.1.archive.attributes e.val).source = r) := by
  ext e
  simp [sourceFilter]

private theorem selected_fiber_sum (x : Rich 3) (r : SourceTree) (f : x.1.Event → Int) :
    (∑ e ∈ (selectedParents x.2).filter
      (fun e => (x.1.archive.attributes e.val).source = r), f e.val) =
      ∑ e ∈ x.2.val.filter (fun e => (x.1.archive.attributes e).source = r), f e := by
  rw [← selectedParents_filter]
  simpa only [sourceFilter, Set.mem_singleton_iff] using
    sum_selectedParents (sourceFilter {r} x).2 f

/-- P68's displayed signed double sum, retaining every ordered occurrence in each leaf fiber. -/
theorem leaf_product_fiber_readout (X : BalancedRich 3) :
    q (sourceFilterBalanced equalLeafSources (productBalanced X X)).val =
      ∑ r ∈ (X.val.2.val.image (fun e => (X.val.1.archive.attributes e).source)).filter
          (fun r => r ∈ Set.range FreeMagma.of),
        ∑ e ∈ X.val.2.val.filter (fun e => (X.val.1.archive.attributes e).source = r),
          ∑ f ∈ X.val.2.val.filter (fun f => (X.val.1.archive.attributes f).source = r),
            contribution X.val.1 e * contribution X.val.1 f := by
  let c := X.val.1
  let a := selectedParents X.val.2
  let src : ↥c.current → SourceTree := fun e => (c.archive.attributes e.val).source
  let leaves := (X.val.2.val.image (fun e => (c.archive.attributes e).source)).filter
    (fun r => r ∈ Set.range FreeMagma.of)
  let pairs := (a ×ˢ a).filter (fun p => FreeMagma.mul (src p.1) (src p.2) ∈ equalLeafSources)
  have actual : q (sourceFilterBalanced equalLeafSources (productBalanced X X)).val =
      ∑ p ∈ pairs, contribution c p.1.val * contribution c p.2.val := by
    change charge (context c c)
      (((a ×ˢ a).map (generatedMap c c)).filter
        (fun e => ((archive c c).attributes e).source ∈ equalLeafSources)) = _
    rw [Finset.filter_map]
    have hf : (a ×ˢ a).filter
        ((fun e => ((archive c c).attributes e).source ∈ equalLeafSources) ∘ generatedMap c c) =
        pairs := by
      apply Finset.filter_congr
      intro p _
      change ((archive c c).attributes (generatedMap c c p)).source ∈ equalLeafSources ↔ _
      rw [GeneratedProduct.attributes_generated]
      rfl
    exact (congrArg (fun s : Finset (Parents c c) =>
      charge (context c c) (s.map (generatedMap c c))) hf).trans (charge_generated c c pairs)
  have maps : ∀ p ∈ pairs, src p.1 ∈ leaves := by
    intro p hp
    obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨p.1.val, (mem_selectedParents _ _).mp (Finset.mem_product.mp hp).1, rfl⟩,
      (pair_mem_equalLeafSources _ _).mp hs |>.2⟩
  rw [actual, ← Finset.sum_fiberwise_of_maps_to maps]
  apply Finset.sum_congr rfl
  intro r hr
  have hl : r ∈ Set.range FreeMagma.of := (Finset.mem_filter.mp hr).2
  have fiber : pairs.filter (fun p => src p.1 = r) =
      (a.filter (fun e => src e = r)) ×ˢ (a.filter (fun e => src e = r)) := by
    ext p
    simp only [pairs, Finset.mem_filter, Finset.mem_product, pair_mem_equalLeafSources]
    constructor
    · rintro ⟨⟨⟨he, hf⟩, hsame, _⟩, hr⟩
      exact ⟨⟨he, hr⟩, hf, hsame.symm.trans hr⟩
    · rintro ⟨⟨he, hr⟩, hf, hs⟩
      exact ⟨⟨⟨he, hf⟩, hr.trans hs.symm, hr ▸ hl⟩, hr⟩
  rw [fiber, Finset.sum_product]
  change (∑ e ∈ a.filter (fun e => src e = r),
    ∑ f ∈ a.filter (fun f => src f = r), contribution c e.val * contribution c f.val) = _
  calc
    _ = ∑ e ∈ a.filter (fun e => src e = r),
        ∑ f ∈ X.val.2.val.filter (fun f => (c.archive.attributes f).source = r),
          contribution c e.val * contribution c f := by
      apply Finset.sum_congr rfl
      intro e _
      exact selected_fiber_sum X.val r (fun f => contribution c e.val * contribution c f)
    _ = _ := selected_fiber_sum X.val r (fun e =>
      ∑ f ∈ X.val.2.val.filter (fun f => (c.archive.attributes f).source = r),
        contribution c e * contribution c f)

private theorem support_sourceCharge_subset (x : Rich 3) :
    (sourceCharge x).support ⊆ x.2.val.image (fun e => (x.1.archive.attributes e).source) := by
  intro r hr
  by_contra h
  have he : x.2.val.filter (fun e => (x.1.archive.attributes e).source = r) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e he hs
    exact h (Finset.mem_image.mpr ⟨e, he, hs⟩)
  have hz := (source_charge_apply x r).1
  rw [he, Finset.sum_empty] at hz
  exact (Finsupp.mem_support_iff.mp hr) hz

/-- LEAF-SQUARE-READOUT on actual histories. Zero fiber totals are removed only after grouping. -/
theorem leaf_square_readout (X : BalancedRich 3) :
    q (sourceFilterBalanced equalLeafSources (productBalanced X X)).val =
      ((sourceCharge X.val).filter (fun r => r ∈ Set.range FreeMagma.of)).sum
        (fun _ z => z ^ 2) := by
  rw [leaf_product_fiber_readout]
  let leaves := (X.val.2.val.image (fun e => (X.val.1.archive.attributes e).source)).filter
    (fun r => r ∈ Set.range FreeMagma.of)
  have hs : ((sourceCharge X.val).filter
      (fun r => r ∈ Set.range FreeMagma.of)).support ⊆ leaves := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨support_sourceCharge_subset X.val
      (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩
  rw [Finsupp.sum_of_support_subset _ hs _ (by intros; simp)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hr).2,
    (source_charge_apply X.val r).1, pow_two, Finset.sum_mul_sum]

/-- The natural leaf restriction is derived from the one source charge, restricted to leaves. -/
def leafCharge (x : Rich 3) : Nat →₀ Int :=
  ((sourceCharge x).filter (fun r => r ∈ Set.range FreeMagma.of)).comapDomain
    FreeMagma.of (fun _ _ _ _ h => by injection h)

private theorem leafCharge_apply (x : Rich 3) (j : Nat) :
    leafCharge x j = sourceCharge x (FreeMagma.of j) := by
  simp [leafCharge, Finsupp.comapDomain_apply]

private theorem leaf_reindex (x : Rich 3) :
    (leafCharge x).sum (fun _ z => z ^ 2) =
      ((sourceCharge x).filter (fun r => r ∈ Set.range FreeMagma.of)).sum
        (fun _ z => z ^ 2) := by
  let z := (sourceCharge x).filter (fun r => r ∈ Set.range FreeMagma.of)
  have hb : Set.BijOn (FreeMagma.of : Nat → SourceTree)
      (FreeMagma.of ⁻¹' (↑z.support : Set SourceTree)) ↑z.support := by
    refine ⟨fun _ h => h, fun _ _ _ _ h => by injection h, ?_⟩
    intro r hr
    obtain ⟨j, rfl⟩ := (Finset.mem_filter.mp hr).2
    exact ⟨j, hr, rfl⟩
  exact Finsupp.sum_comapDomain FreeMagma.of z (fun _ z => z ^ 2) hb

/-- The natural-index form of LEAF-SQUARE-READOUT uses exactly the same source coefficients. -/
theorem leaf_square_readout_nat (X : BalancedRich 3) :
    q (sourceFilterBalanced equalLeafSources (productBalanced X X)).val =
      ∑ j ∈ (leafCharge X.val).support, sourceCharge X.val (FreeMagma.of j) ^ 2 := by
  rw [leaf_square_readout, ← leaf_reindex]
  simp only [Finsupp.sum, leafCharge_apply]

end
end D5.S3.ConceptDynamics.Spacetime.LeafSquareReadout
