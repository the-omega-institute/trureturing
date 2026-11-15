/- GID: D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Wild numbers and greedy runs under graph isomorphisms. -/

/-
admission_basis: escape-witness (run_reflect)
escape_witness: run_reflect
Direct frozen dependencies: none.
setMap_card: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
connecting_iff: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
run_map: proof_shape: content; escape_witness: none; Direct frozen dependencies: none.
setMap_surjective: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
output_reflect: proof_shape: content; escape_witness: none; Direct frozen dependencies: none.
wildNumber_map: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
colorMap_surjective: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
run_reflect: proof_shape: content; escape_witness: run_reflect; Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21209
-/

import D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.Relabel
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
open scoped Classical
variable {V U C : Type*} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype C]
variable {G : SimpleGraph V} {H : SimpleGraph U}
private theorem edgeMap_injective (f : G ≃g H) : Function.Injective (Sym2.map f) :=
  Sym2.map.injective f.injective
private theorem edgeMap_surjective (f : G ≃g H) : Function.Surjective (Sym2.map f) := by
  exact Quot.map_surjective _ (f.surjective.prodMap f.surjective)
@[simp] private theorem mem_setMap (f : G ≃g H) (W : Finset (Sym2 V)) (e : Sym2 V) :
    Sym2.map f e ∈ (fun f W => Finset.image (Sym2.map f) W) f W ↔ e ∈ W :=
  (edgeMap_injective f).mem_finset_image
@[simp] private theorem setMap_insert (f : G ≃g H) (W : Finset (Sym2 V)) (e : Sym2 V) :
    (fun f W => Finset.image (Sym2.map f) W) f (insert e W) = insert (Sym2.map f e) ((fun f W => Finset.image (Sym2.map f) W) f W) := Finset.image_insert _ _ _
@[simp] theorem setMap_card (f : G ≃g H) (W : Finset (Sym2 V)) :
    ((fun f W => Finset.image (Sym2.map f) W) f W).card = W.card := Finset.card_image_of_injective _ (edgeMap_injective f)
@[simp] private theorem colorMap_edge (f : G ≃g H) (γ : G.edgeSet → C) (e : G.edgeSet) :
    (SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom) ((SimpleGraph.Iso.mapEdgeSet f) e) = γ e := by
  exact congrArg γ ((SimpleGraph.Iso.mapEdgeSet f).symm_apply_apply e)
private def colorIso (f : G ≃g H) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) (c : C) :
    wildColorGraph G γ W c ≃g wildColorGraph H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) ((fun f W => Finset.image (Sym2.map f) W) f W) c where
  __ := f.toEquiv
  map_rel_iff' := by
    intro u v
    simp only [wildColorGraph,SimpleGraph.fromEdgeSet_adj]
    have he : colorEdges H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) c s(f u,f v) ↔ colorEdges G γ c s(u,v) := by
      constructor
      · rintro ⟨he,hc⟩
        have ho : s(u,v) ∈ G.edgeSet := f.map_mem_edgeSet_iff.mp he
        refine ⟨ho,?_⟩
        have hm := colorMap_edge f γ ⟨s(u,v),ho⟩
        exact hm.symm.trans hc
      · rintro ⟨he,hc⟩
        refine ⟨f.map_mem_edgeSet_iff.mpr he,?_⟩
        exact (colorMap_edge f γ ⟨s(u,v),he⟩).trans hc
    have hm : s(f u,f v) ∈ (fun f W => Finset.image (Sym2.map f) W) f W ↔ s(u,v) ∈ W := mem_setMap f W s(u,v)
    change ((s(f u,f v) ∈ (fun f W => Finset.image (Sym2.map f) W) f W ∨ colorEdges H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) c s(f u,f v)) ∧ f u ≠ f v) ↔
      ((s(u,v) ∈ W ∨ colorEdges G γ c s(u,v)) ∧ u ≠ v)
    rw [he,hm, f.injective.ne_iff]
@[simp] private theorem kappa_colorMap (f : G ≃g H) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) (c : C) :
    Nat.card (wildColorGraph H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) ((fun f W => Finset.image (Sym2.map f) W) f W) c).ConnectedComponent = Nat.card (wildColorGraph G γ W c).ConnectedComponent :=
  (Nat.card_congr (colorIso f γ W c).connectedComponentEquiv).symm
theorem connecting_iff (f : G ≃g H) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) :
    IsColorConnecting H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) ((fun f W => Finset.image (Sym2.map f) W) f W) ↔ IsColorConnecting G γ W := by
  constructor
  · rintro ⟨hv,hc⟩
    refine ⟨?_,fun c => (colorIso f γ W c).connected_iff.mpr (hc c)⟩
    intro e he
    exact f.map_mem_edgeSet_iff.mp (hv ((mem_setMap f W e).mpr he))
  · rintro ⟨hv,hc⟩
    refine ⟨?_,fun c => (colorIso f γ W c).connected_iff.mp (hc c)⟩
    intro e he
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
    exact f.map_mem_edgeSet_iff.mpr (hv hd)
@[simp] private theorem dip_map (f : G ≃g H) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) (e : Sym2 V) :
    dip H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) ((fun f W => Finset.image (Sym2.map f) W) f W) (Sym2.map f e) = dip G γ W e := by
  unfold dip
  simp only [←setMap_insert,kappa_colorMap]
private theorem edges_map (f : G ≃g H) : (Set.toFinite H.edgeSet).toFinset = (fun f W => Finset.image (Sym2.map f) W) f ((Set.toFinite G.edgeSet).toFinset) := by
  ext e
  obtain ⟨d,rfl⟩ := edgeMap_surjective f e
  simp only [Set.Finite.mem_toFinset,mem_setMap]
  exact f.map_mem_edgeSet_iff
@[simp] private theorem potential_map (f : G ≃g H) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) (e : Sym2 V) :
    potential H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) ((fun f W => Finset.image (Sym2.map f) W) f W) (Sym2.map f e) = potential G γ W e := by
  unfold potential
  rw [edges_map f]
  rw [Finset.image_val_of_injOn (edgeMap_injective f).injOn,Multiset.map_map]
  apply congrArg (fun m : Multiset ℕ => m.sort (· ≥ ·))
  apply congrArg (fun p : Sym2 V → ℕ => ((Set.toFinite G.edgeSet).toFinset).val.map p)
  funext d
  change dip H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) (insert (Sym2.map f e) ((fun f W => Finset.image (Sym2.map f) W) f W)) (Sym2.map f d) =
    dip G γ (insert e W) d
  rw [←setMap_insert,dip_map]
private theorem step_iff (f : G ≃g H) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) (e : Sym2 V) :
    IsGreedyStep H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) ((fun f W => Finset.image (Sym2.map f) W) f W) (Sym2.map f e) ↔ IsGreedyStep G γ W e := by
  have hm (d : Sym2 V) : Sym2.map f d ∈ (Set.toFinite H.edgeSet).toFinset \ (fun f W => Finset.image (Sym2.map f) W) f W ↔ d ∈ (Set.toFinite G.edgeSet).toFinset \ W := by
    simp only [Finset.mem_sdiff,Set.Finite.mem_toFinset,mem_setMap]
    exact and_congr f.map_mem_edgeSet_iff Iff.rfl
  have hall : ∀ d : Sym2 U, ∃ a : Sym2 V, Sym2.map f a = d := edgeMap_surjective f
  simp only [IsGreedyStep,connecting_iff,hm,dip_map,potential_map]
  constructor
  · rintro ⟨hn,he,hd,hp⟩
    exact ⟨hn,he,fun d h => by simpa using hd (Sym2.map f d) ((hm d).mpr h),
      fun d h heq => by simpa using hp (Sym2.map f d) ((hm d).mpr h) (by simpa using heq)⟩
  · rintro ⟨hn,he,hd,hp⟩
    refine ⟨hn,he,?_,?_⟩
    · intro d h
      obtain ⟨a,rfl⟩ := hall d
      simpa using hd a ((hm a).mp h)
    · intro d h heq
      obtain ⟨a,rfl⟩ := hall d
      simpa using hp a ((hm a).mp h) (by simpa using heq)
theorem run_map (f : G ≃g H) (γ : G.edgeSet → C) {W : Finset (Sym2 V)} (hr : IsGreedyRun G γ W) :
    IsGreedyRun H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) ((fun f W => Finset.image (Sym2.map f) W) f W) := by
  induction hr with
  | empty => simpa [] using (IsGreedyRun.empty (G := H) (γ := (SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)))
  | @step W e hr hs ih =>
    rw [setMap_insert]
    exact .step ih ((step_iff f γ W e).mpr hs)
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.Relabel
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.Relabel
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
open scoped Classical
variable {V U C : Type*} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype C]
variable {G : SimpleGraph V} {H : SimpleGraph U}
theorem setMap_surjective (f : G ≃g H) : Function.Surjective ((fun f W => Finset.image (Sym2.map f) W) f) := by
  classical
  let e : Sym2 V ≃ Sym2 U := Equiv.ofBijective (Sym2.map f)
    ⟨Sym2.map.injective f.injective, Quot.map_surjective _ (f.surjective.prodMap f.surjective)⟩
  change Function.Surjective (fun W : Finset (Sym2 V) => W.image e.toEmbedding)
  simpa only [Function.Surjective, Equiv.finsetCongr_apply, Finset.map_eq_image] using e.finsetCongr.surjective
private theorem run_reflect (f : G ≃g H) (γ : G.edgeSet → C) {U : Finset (Sym2 U)}
    (hr : IsGreedyRun H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) U) :
    ∃ W, (fun f W => Finset.image (Sym2.map f) W) f W = U ∧ IsGreedyRun G γ W := by
  have hc : SimpleGraph.EdgeLabeling.pullback
      (SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom) f.toHom = γ := by
    funext e
    exact colorMap_edge f γ e
  refine ⟨U.image (Sym2.map f.symm), ?_, ?_⟩
  · change Finset.image (Sym2.map f) (U.image (Sym2.map f.symm)) = U
    rw [Finset.image_image]
    have he : (Sym2.map f) ∘ (Sym2.map f.symm) = id := by
      have hf : (f ∘ f.symm) = id := by
        exact RelIso.self_comp_symm f
      rw [← Sym2.map_comp, hf, Sym2.map_id]
    rw [he, Finset.image_id]
  · have hh := run_map f.symm (SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom) hr
    change IsGreedyRun G (SimpleGraph.EdgeLabeling.pullback
      (SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom) f.toHom)
      (U.image (Sym2.map f.symm)) at hh
    rwa [hc] at hh
theorem output_reflect (f : G ≃g H) (γ : G.edgeSet → C) {U : Finset (Sym2 U)}
    (hr : IsGreedyOutput H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) U) :
    ∃ W, (fun f W => Finset.image (Sym2.map f) W) f W = U ∧ IsGreedyOutput G γ W := by
  obtain ⟨W,rfl,hw⟩ := run_reflect f γ hr.1
  exact ⟨W,rfl,hw,(connecting_iff f γ W).mp hr.2⟩
theorem wildNumber_map (f : G ≃g H) (γ : G.edgeSet → C) :
    wildNumber H ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) = wildNumber G γ := by
  unfold wildNumber
  congr 1
  ext k
  constructor
  · rintro ⟨U,hU,hk⟩
    obtain ⟨W,rfl⟩ := setMap_surjective f U
    exact ⟨W,(connecting_iff f γ W).mp hU,by simpa using hk⟩
  · rintro ⟨W,hW,hk⟩
    exact ⟨(fun f W => Finset.image (Sym2.map f) W) f W,(connecting_iff f γ W).mpr hW,by simpa using hk⟩
theorem colorMap_surjective (f : G ≃g H) (γ : G.edgeSet → C) (hγ : Function.Surjective γ) :
    Function.Surjective ((SimpleGraph.EdgeLabeling.pullback γ f.symm.toHom)) := by
  exact hγ.comp (SimpleGraph.Iso.mapEdgeSet f).symm.surjective
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.Relabel
