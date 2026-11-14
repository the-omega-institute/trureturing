/- GID: D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamWild
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamWild
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Greedy choices separate over rooted blocks and their output sizes add. -/

/-
admission_basis: escape-witness (greedy_step_restrict)
escape_witness: greedy_step_restrict
Direct frozen dependencies: none.
amplify: proof_shape: content; escape_witness: none; Direct frozen dependencies: none.
greedy_step_restrict: proof_shape: content; escape_witness: greedy_step_restrict; Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21209
-/

import D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
import D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
import D5.S3.Combinatorics.EdgeLabeling.WildNumber.MultisetLex

namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
variable {ι A C : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Fintype C]
noncomputable def starColor (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) : (starGraph B).edgeSet → C := fun e =>
  γ ((edgeEquiv B).symm e).1 ((edgeEquiv B).symm e).2
@[simp] private theorem starColor_lift (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) (i : ι) (e : (B i).edgeSet) :
    starColor B γ ⟨(Sym2.map (Option.map (Prod.mk i))) e.val,liftEdgeMem B i e.property⟩ = γ i e := by
  change starColor B γ ((edgeEquiv B) ⟨i,e⟩) = γ i e
  unfold starColor
  rw [Equiv.symm_apply_apply]
private noncomputable def assemble (W : ι → Finset (Sym2 (Option A))) :
    Finset (Sym2 (Option (ι × A))) := by
  classical
  exact Finset.univ.biUnion (fun i => (W i).image ((Sym2.map (Option.map (Prod.mk i)))))
@[simp] private theorem mem_assemble (W : ι → Finset (Sym2 (Option A))) (e) :
    e ∈ assemble W ↔ ∃ i f, f ∈ W i ∧ (Sym2.map (Option.map (Prod.mk i))) f = e := by
  classical
  simp [assemble]
private theorem assemble_valid (B : ι → SimpleGraph (Option A))
    (W : ι → Finset (Sym2 (Option A))) (hW : ∀ i, (W i : Set _) ⊆ (B i).edgeSet) :
    (assemble W : Set _) ⊆ (starGraph B).edgeSet := by
  intro e he
  obtain ⟨i,f,hf,rfl⟩ := (mem_assemble W e).mp he
  exact liftEdgeMem B i (hW i hf)
private theorem assemble_insert (W : ι → Finset (Sym2 (Option A))) (i : ι) (e) :
    assemble (Function.update W i (insert e (W i))) = insert ((Sym2.map (Option.map (Prod.mk i))) e) (assemble W) := by
  classical
  ext f
  simp only [mem_assemble,Finset.mem_insert]
  constructor
  · rintro ⟨j,g,hg,rfl⟩
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self,Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · exact Or.inl rfl
      · exact Or.inr ⟨i,g,hg,rfl⟩
    · rw [Function.update_of_ne hji] at hg
      exact Or.inr ⟨j,g,hg,rfl⟩
  · rintro (rfl | ⟨j,g,hg,rfl⟩)
    · exact ⟨i,e,by simp,rfl⟩
    · refine ⟨j,g,?_,rfl⟩
      by_cases hji : j = i
      · subst j
        simp [hg]
      · simpa [Function.update_of_ne hji] using hg
private theorem assemble_set (W : ι → Finset (Sym2 (Option A))) :
    (assemble W : Set _) = ⋃ i, (Sym2.map (Option.map (Prod.mk i))) '' (↑(W i) : Set (Sym2 (Option A))) := by
  ext e
  simp only [Finset.mem_coe,mem_assemble,Set.mem_iUnion,Set.mem_image]
private theorem star_fromEdgeSet (S : ι → Set (Sym2 (Option A))) :
    SimpleGraph.fromEdgeSet (⋃ i, (Sym2.map (Option.map (Prod.mk i))) '' S i) =
      starGraph (fun i => SimpleGraph.fromEdgeSet (S i)) := by
  ext x y
  rw [SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨he,hxy⟩
    obtain ⟨i,e,hei,hm⟩ := (show ∃ i e, e ∈ S i ∧ (Sym2.map (Option.map (Prod.mk i))) e = s(x,y) by
      simpa only [Set.mem_iUnion,Set.mem_image] using he)
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [Sym2.map_mk,Sym2.eq_iff] at hm
      rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨i,u,v,by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨hei,fun h => hxy (congrArg ((Option.map (Prod.mk i))) h)⟩,rfl,rfl⟩
      · exact ⟨i,v,u,by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simpa only [Sym2.eq_swap] using hei,fun h => hxy (congrArg ((Option.map (Prod.mk i))) h)⟩,rfl,rfl⟩
  · rintro ⟨i,u,v,huv,rfl,rfl⟩
    rw [SimpleGraph.fromEdgeSet_adj] at huv
    refine ⟨?_,fun h => huv.2 (embed_injective i h)⟩
    exact Set.mem_iUnion.mpr ⟨i,s(u,v),huv.1,rfl⟩
private theorem starColor_edges (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) (c : C) :
    colorEdges (starGraph B) (starColor B γ) c = ⋃ i, (Sym2.map (Option.map (Prod.mk i))) '' colorEdges (B i) (γ i) c := by
  ext e
  constructor
  · rintro ⟨he,hγ⟩
    obtain ⟨i,f,hf,rfl⟩ := (star_edge_decomp B).mp he
    rw [starColor_lift B γ i ⟨f,hf⟩] at hγ
    exact Set.mem_iUnion.mpr ⟨i,f,⟨hf,hγ⟩,rfl⟩
  · intro he
    obtain ⟨i,f,⟨hf,hγ⟩,rfl⟩ := (by simpa only [Set.mem_iUnion,Set.mem_image] using he)
    refine ⟨liftEdgeMem B i hf,?_⟩
    rw [starColor_lift B γ i ⟨f,hf⟩]
    exact hγ
private theorem wildColor_star (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) (W : ι → Finset (Sym2 (Option A))) (c : C) :
    wildColorGraph (starGraph B) (starColor B γ) (assemble W) c =
      starGraph (fun i => wildColorGraph (B i) (γ i) (W i) c) := by
  classical
  unfold wildColorGraph
  rw [assemble_set,starColor_edges,←Set.iUnion_union_distrib]
  simp_rw [←Set.image_union]
  exact star_fromEdgeSet _
private theorem dip_star_local (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) (W : ι → Finset (Sym2 (Option A))) (i : ι) (e) :
    dip (starGraph B) (starColor B γ) (assemble W) ((Sym2.map (Option.map (Prod.mk i))) e) =
      dip (B i) (γ i) (W i) e := by
  classical
  unfold dip
  apply Finset.sum_congr rfl
  intro c hc
  rw [←assemble_insert,wildColor_star,wildColor_star]
  change Nat.card _ - Nat.card _ = Nat.card _ - Nat.card _
  rw [component_count_star_difference _ _ i (by
    intro j hj
    simp only [Function.update_of_ne hj])]
  simp only [Function.update_self]
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
open scoped Classical
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
variable {ι A C : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Fintype C]
private noncomputable def profile {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) : Multiset ℕ :=
  ((fun G : SimpleGraph _ => @SimpleGraph.edgeFinset _ G (Fintype.ofFinite G.edgeSet)) G).val.map (dip G γ W)
private theorem edges_map_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : Sym2 V → ℕ) :
    ((fun G : SimpleGraph _ => @SimpleGraph.edgeFinset _ G (Fintype.ofFinite G.edgeSet)) G).val.map f = ∑ e : G.edgeSet, ({f e.val} : Multiset ℕ) := by
  classical
  have hv : (Finset.univ : Finset G.edgeSet).val.map Subtype.val = ((fun G : SimpleGraph _ => @SimpleGraph.edgeFinset _ G (Fintype.ofFinite G.edgeSet)) G).val := by
    rw [Finset.univ_val_map_subtype_val]
    congr 1
    ext e
    simp []
  rw [←hv,Multiset.map_map]
  change _ = (Finset.univ.val.map (fun e : G.edgeSet => ({f e.val} : Multiset ℕ))).sum
  simpa only [Multiset.map_map,Function.comp_def] using
    (Multiset.sum_map_singleton (Finset.univ.val.map (fun e : G.edgeSet => f e.val))).symm
private theorem profile_star (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) (W : ι → Finset (Sym2 (Option A))) :
    profile (starGraph B) (starColor B γ) (assemble W) = ∑ i : ι, profile (B i) (γ i) (W i) := by
  classical
  unfold profile
  rw [edges_map_eq_sum]
  calc
    _ = ∑ e : Σ i, (B i).edgeSet,
        ({dip (starGraph B) (starColor B γ) (assemble W) ((Sym2.map (Option.map (Prod.mk e.1))) e.2.val)} : Multiset ℕ) :=
      (Fintype.sum_equiv (edgeEquiv B) _ _ (fun _ => rfl)).symm
    _ = ∑ i : ι, ∑ e : (B i).edgeSet,
        ({dip (B i) (γ i) (W i) e.val} : Multiset ℕ) := by
      rw [Fintype.sum_sigma]
      simp_rw [dip_star_local]
    _ = _ := by simp_rw [edges_map_eq_sum]
private theorem profile_star_insert (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) (W : ι → Finset (Sym2 (Option A))) (i : ι) (e) :
    profile (starGraph B) (starColor B γ) (insert ((Sym2.map (Option.map (Prod.mk i))) e) (assemble W)) =
      profile (B i) (γ i) (insert e (W i)) +
        ∑ j ∈ Finset.univ.erase i, profile (B j) (γ j) (W j) := by
  classical
  rw [←assemble_insert,profile_star]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
private theorem potential_star_lex_iff (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) (W : ι → Finset (Sym2 (Option A))) (i : ι) (e f) :
    List.Lex (· < ·)
      (potential (starGraph B) (starColor B γ) (assemble W) ((Sym2.map (Option.map (Prod.mk i))) e))
      (potential (starGraph B) (starColor B γ) (assemble W) ((Sym2.map (Option.map (Prod.mk i))) f)) ↔
      List.Lex (· < ·) (potential (B i) (γ i) (W i) e) (potential (B i) (γ i) (W i) f) := by
  change List.Lex (· < ·) (profile _ _ (insert _ _) |>.sort (· ≥ ·))
    (profile _ _ (insert _ _) |>.sort (· ≥ ·)) ↔ _
  rw [profile_star_insert,profile_star_insert,D5.S3.Combinatorics.EdgeLabeling.WildNumber.MultisetLex.sort_add_lex_iff]
  rfl
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
variable {ι A C : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Fintype C]
private theorem liftEdgeMem_assemble_iff (W : ι → Finset (Sym2 (Option A))) (i : ι)
    (e : Sym2 (Option A)) (he : ¬e.IsDiag) : (Sym2.map (Option.map (Prod.mk i))) e ∈ assemble W ↔ e ∈ W i := by
  constructor
  · intro h
    obtain ⟨j,f,hf,heq⟩ := (mem_assemble W _).mp h
    have hij : i = j := liftEdge_block_unique he heq.symm
    subst j
    have hfe := liftEdge_injective i heq
    simpa only [hfe] using hf
  · intro h
    exact (mem_assemble W _).mpr ⟨i,e,h,rfl⟩
private theorem greedy_step_restrict (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) (hB : ∀ i, (B i).Connected)
    (W : ι → Finset (Sym2 (Option A))) (hW : ∀ i, (W i : Set _) ⊆ (B i).edgeSet)
    (i : ι) (e : Sym2 (Option A)) (he : e ∈ (B i).edgeSet)
    (hs : IsGreedyStep (starGraph B) (starColor B γ) (assemble W) ((Sym2.map (Option.map (Prod.mk i))) e)) :
    IsGreedyStep (B i) (γ i) (W i) e := by
  classical
  have hnDiag : ¬e.IsDiag := (B i).not_isDiag_of_mem_edgeSet he
  have hmem (j : ι) (f : Sym2 (Option A)) (hf : f ∈ (fun G : SimpleGraph _ => @SimpleGraph.edgeFinset _ G (Fintype.ofFinite G.edgeSet)) (B j) \ W j) :
      (Sym2.map (Option.map (Prod.mk j))) f ∈ (fun G : SimpleGraph _ => @SimpleGraph.edgeFinset _ G (Fintype.ofFinite G.edgeSet)) (starGraph B) \ assemble W := by
    have hfedge : f ∈ (B j).edgeSet := by simpa [] using (Finset.mem_sdiff.mp hf).1
    apply Finset.mem_sdiff.mpr
    constructor
    · simpa [] using liftEdgeMem B j hfedge
    · exact fun hm => (Finset.mem_sdiff.mp hf).2
        ((liftEdgeMem_assemble_iff W j f ((B j).not_isDiag_of_mem_edgeSet hfedge)).mp hm)
  refine ⟨?_,?_,?_,?_⟩
  · intro hcc
    have hz := D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy.dip_zero_of_connected (B i) (γ i) (W i) hcc e
    have hp := D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy.step_positive (starGraph B) (starColor B γ)
      ((connected_star_iff B).mpr hB) (assemble W) (assemble_valid B W hW) hs
    rw [dip_star_local,hz] at hp
    exact (Nat.lt_irrefl 0 hp)
  · apply Finset.mem_sdiff.mpr
    constructor
    · simpa [] using he
    · intro hm
      apply (Finset.mem_sdiff.mp hs.2.1).2
      exact (liftEdgeMem_assemble_iff W i e hnDiag).mpr hm
  · intro f hf
    have hle := hs.2.2.1 ((Sym2.map (Option.map (Prod.mk i))) f) (hmem i f hf)
    simpa only [dip_star_local] using hle
  · intro f hf heq hlex
    apply hs.2.2.2 ((Sym2.map (Option.map (Prod.mk i))) f) (hmem i f hf)
    · simpa only [dip_star_local] using heq
    · exact (potential_star_lex_iff B γ W i e f).mpr hlex
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
open scoped BigOperators Classical
variable {ι A C : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Fintype C]
private theorem assemble_card (B : ι → SimpleGraph (Option A))
    (W : ι → Finset (Sym2 (Option A))) (hW : ∀ i, (W i : Set _) ⊆ (B i).edgeSet) :
    (assemble W).card = ∑ i, (W i).card := by
  classical
  unfold assemble
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i hi
    exact Finset.card_image_of_injective _ (liftEdge_injective i)
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro e he hje
    obtain ⟨f,hif,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨g,hg,heq⟩ := Finset.mem_image.mp hje
    exact hij (liftEdge_block_unique ((B i).not_isDiag_of_mem_edgeSet (hW i hif)) heq.symm)
private noncomputable def restrict (B : ι → SimpleGraph (Option A))
    (W : Finset (Sym2 (Option (ι × A)))) (i : ι) : Finset (Sym2 (Option A)) :=
  ((fun G : SimpleGraph _ => @SimpleGraph.edgeFinset _ G (Fintype.ofFinite G.edgeSet)) (B i)).filter (fun e => (Sym2.map (Option.map (Prod.mk i))) e ∈ W)
private theorem restrict_valid (B : ι → SimpleGraph (Option A)) (W : Finset (Sym2 (Option (ι × A)))) :
    ∀ i, (restrict B W i : Set _) ⊆ (B i).edgeSet := by
  intro i e he
  simpa [] using (Finset.mem_filter.mp he).1
private theorem assemble_restrict (B : ι → SimpleGraph (Option A))
    (W : Finset (Sym2 (Option (ι × A)))) (hW : (W : Set _) ⊆ (starGraph B).edgeSet) :
    assemble (restrict B W) = W := by
  ext e
  constructor
  · intro he
    obtain ⟨i,f,hf,rfl⟩ := (mem_assemble _ _).mp he
    exact (Finset.mem_filter.mp hf).2
  · intro he
    obtain ⟨i,f,hf,rfl⟩ := (star_edge_decomp B).mp (hW he)
    apply (mem_assemble _ _).mpr
    refine ⟨i,f,Finset.mem_filter.mpr ⟨?_,he⟩,rfl⟩
    simpa [] using hf
private theorem connecting_assemble_iff (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) (W : ι → Finset (Sym2 (Option A)))
    (hW : ∀ i, (W i : Set _) ⊆ (B i).edgeSet) :
    IsColorConnecting (starGraph B) (starColor B γ) (assemble W) ↔
      ∀ i, IsColorConnecting (B i) (γ i) (W i) := by
  constructor
  · intro h i
    refine ⟨hW i,fun c => ?_⟩
    have hc := h.2 c
    rw [wildColor_star] at hc
    exact (connected_star_iff _).mp hc i
  · intro h
    refine ⟨assemble_valid B W hW,fun c => ?_⟩
    rw [wildColor_star]
    exact (connected_star_iff _).mpr (fun i => (h i).2 c)
private theorem run_valid (G : SimpleGraph (Option A)) (γ : G.edgeSet → C) {W}
    (h : IsGreedyRun G γ W) : (W : Set _) ⊆ G.edgeSet := by
  induction h with
  | empty => simp
  | @step W e hr hs ih =>
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · simpa [] using (Finset.mem_sdiff.mp hs.2.1).1
    · exact ih hf
private theorem run_decompose (B : ι → SimpleGraph (Option A))
    (γ : ∀ i, (B i).edgeSet → C) (hB : ∀ i, (B i).Connected) {W}
    (h : IsGreedyRun (starGraph B) (starColor B γ) W) :
    ∃ L : ι → Finset (Sym2 (Option A)), assemble L = W ∧
      ∀ i, IsGreedyRun (B i) (γ i) (L i) := by
  induction h with
  | empty =>
    refine ⟨fun _ => ∅,?_,fun _ => .empty⟩
    ext e
    simp [mem_assemble]
  | @step W e hr hs ih =>
    obtain ⟨L,rfl,hL⟩ := ih
    have he : e ∈ (starGraph B).edgeSet := by
      simpa [] using (Finset.mem_sdiff.mp hs.2.1).1
    obtain ⟨i,f,hf,rfl⟩ := (star_edge_decomp B).mp he
    have hv : ∀ j, (L j : Set _) ⊆ (B j).edgeSet := fun j => run_valid _ _ (hL j)
    refine ⟨Function.update L i (insert f (L i)),assemble_insert L i f,?_⟩
    intro j
    by_cases hji : j = i
    · subst j
      rw [Function.update_self]
      exact .step (hL i) (greedy_step_restrict B γ hB L hv i f hf hs)
    · simpa [Function.update_of_ne hji] using hL j
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
open scoped BigOperators Classical
variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C]
theorem amplify (B : SimpleGraph (Option A)) (γ : B.edgeSet → C) (hB : B.Connected)
    (hγ : Function.Surjective γ) (a b : ℕ)
    (hO : ∃ O, IsColorConnecting B γ O ∧ O.card = a)
    (hlow : ∀ W, IsColorConnecting B γ W → a ≤ W.card)
    (hout : ∀ W, IsGreedyOutput B γ W → W.card = b)
    (r : ℕ) (hr : 1 ≤ r) :
    let Br : SimpleGraph (Option (Fin r × A)) := starGraph (Function.const (Fin r) B)
    let γr := starColor (Function.const (Fin r) B) (Function.const (Fin r) γ)
    Br.Connected ∧ Function.Surjective γr ∧ wildNumber Br γr = a*r ∧
      (∃ W, IsGreedyOutput Br γr W) ∧
      ∀ W, IsGreedyOutput Br γr W → W.card = b*r := by
  classical
  let Bs : Fin r → SimpleGraph (Option A) := fun _ => B
  let γs : ∀ i : Fin r, (Bs i).edgeSet → C := fun _ => γ
  change (starGraph Bs).Connected ∧ Function.Surjective (starColor Bs γs) ∧
    wildNumber (starGraph Bs) (starColor Bs γs) = a*r ∧
      (∃ W, IsGreedyOutput (starGraph Bs) (starColor Bs γs) W) ∧
      ∀ W, IsGreedyOutput (starGraph Bs) (starColor Bs γs) W → W.card = b*r
  have hBs : ∀ i, (Bs i).Connected := fun _ => hB
  have hconn := (connected_star_iff Bs).mpr hBs
  refine ⟨hconn,?_,?_,D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy.exists_greedy_output _ _ hconn,?_⟩
  · intro c
    obtain ⟨e,he⟩ := hγ c
    let i : Fin r := ⟨0,by omega⟩
    refine ⟨⟨(Sym2.map (Option.map (Prod.mk i))) e.val,liftEdgeMem Bs i e.property⟩,?_⟩
    rw [starColor_lift]
    exact he
  · obtain ⟨O,hO,ha⟩ := hO
    let Os : Fin r → Finset (Sym2 (Option A)) := fun _ => O
    have hv : ∀ i, (Os i : Set _) ⊆ (Bs i).edgeSet := fun _ => hO.1
    have hcc : IsColorConnecting (starGraph Bs) (starColor Bs γs) (assemble Os) :=
      (connecting_assemble_iff Bs γs Os hv).mpr (fun _ => hO)
    have hc : (assemble Os).card = a*r := by
      rw [assemble_card Bs Os hv]
      simp only [Os,ha,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
      exact Nat.mul_comm r a
    unfold wildNumber
    apply le_antisymm
    · exact Nat.sInf_le ⟨assemble Os,hcc,hc⟩
    · apply le_csInf (show Set.Nonempty {k | ∃ W, IsColorConnecting (starGraph Bs) (starColor Bs γs) W ∧ W.card = k} from
        ⟨a*r,assemble Os,hcc,hc⟩)
      rintro k ⟨W,hw,hk⟩
      let L := restrict Bs W
      have hvL := restrict_valid Bs W
      have heq : assemble L = W := assemble_restrict Bs W hw.1
      have hccL : ∀ i, IsColorConnecting (Bs i) (γs i) (L i) :=
        (connecting_assemble_iff Bs γs L hvL).mp (by simpa only [heq] using hw)
      have hl : ∑ i : Fin r, a ≤ ∑ i : Fin r, (L i).card :=
        Finset.sum_le_sum (fun i _ => hlow (L i) (hccL i))
      rw [←assemble_card Bs L hvL,heq,hk] at hl
      simpa [Nat.mul_comm] using hl
  · intro W hw
    obtain ⟨L,heq,hL⟩ := run_decompose Bs γs hBs hw.1
    have hvL : ∀ i, (L i : Set _) ⊆ (Bs i).edgeSet := fun i => run_valid _ _ (hL i)
    have hccL : ∀ i, IsColorConnecting (Bs i) (γs i) (L i) :=
      (connecting_assemble_iff Bs γs L hvL).mp (by simpa only [heq] using hw.2)
    rw [←heq,assemble_card Bs L hvL]
    have hh : ∀ i, (L i).card = b := fun i => hout (L i) ⟨hL i,hccL i⟩
    simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    exact Nat.mul_comm r b
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
