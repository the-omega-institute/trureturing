/- GID: D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Components and edges of rooted graph amalgamations. -/

/-
admission_basis: escape-witness (component_count_star)
escape_witness: component_count_star
Direct frozen dependencies: none.
embed_injective: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
reachable_map_of_adj: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
connected_star_iff: proof_shape: content; escape_witness: none; Direct frozen dependencies: none.
liftEdge_injective: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
liftEdge_block_unique: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
liftEdgeMem: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
star_edge_decomp: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
edgeForwardBijective: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
component_count_star_difference: proof_shape: content; escape_witness: none; Direct frozen dependencies: none.
component_count_star: proof_shape: content; escape_witness: component_count_star; Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21209
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
open SimpleGraph
variable {ι A : Type*}
theorem embed_injective (i : ι) : Function.Injective ((Option.map (Prod.mk i) : Option A → Option (ι × A))) := by
  exact Option.map_injective (Prod.mk_right_injective i)
def starGraph (F : ι → SimpleGraph (Option A)) : SimpleGraph (Option (ι × A)) where
  Adj x y := ∃ i u v, (F i).Adj u v ∧ x = (Option.map (Prod.mk i)) u ∧ y = (Option.map (Prod.mk i)) v
  symm := ⟨by
    rintro x y ⟨i,u,v,h,rfl,rfl⟩
    exact ⟨i,v,u,h.symm,rfl,rfl⟩⟩
  loopless := ⟨by
    rintro x ⟨i,u,v,h,hx,hy⟩
    exact h.ne (embed_injective i (hx.symm.trans hy))⟩
private def project [DecidableEq ι] (i : ι) (x : Option (ι × A)) : Option A :=
  Option.map Prod.snd (x.filter (fun p => p.1 = i))
@[simp] private theorem project_embed [DecidableEq ι] (i : ι) (u : Option A) :
    project i ((Option.map (Prod.mk i)) u) = u := by cases u <;> simp [project, Option.filter_some]
@[simp] private theorem project_embed_other [DecidableEq ι] (i j : ι) (h : j ≠ i) (u : Option A) :
    project i ((Option.map (Prod.mk j)) u) = none := by cases u <;> simp [project,Option.filter_some,h]
private def blockHom (F : ι → SimpleGraph (Option A)) (i : ι) : F i →g starGraph F where
  toFun := (Option.map (Prod.mk i))
  map_rel' := fun {u v} h => ⟨i,u,v,h,rfl,rfl⟩
theorem reachable_map_of_adj {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (h : ∀ {u v}, G.Adj u v → H.Reachable (f u) (f v))
    {u v} (huv : G.Reachable u v) : H.Reachable (f u) (f v)  := by
  rw [H.reachable_iff_reflTransGen]
  exact Relation.ReflTransGen.lift' f
    (fun _ _ ha => (H.reachable_iff_reflTransGen _ _).mp (h ha)) u v
    ((G.reachable_iff_reflTransGen _ _).mp huv)
private theorem project_reachable [DecidableEq ι] (F : ι → SimpleGraph (Option A)) (i : ι)
    {x y} (h : (starGraph F).Reachable x y) :
    (F i).Reachable (project i x) (project i y) := by
  apply reachable_map_of_adj (project i) ?_ h
  rintro x y ⟨j,u,v,huv,rfl,rfl⟩
  by_cases hji : j = i
  · subst j
    simpa using huv.reachable
  · simp only [project_embed_other i j hji]
    exact .rfl
private theorem reachable_embed_iff (F : ι → SimpleGraph (Option A)) (i : ι) (u v : Option A) :
    (starGraph F).Reachable ((Option.map (Prod.mk i)) u) ((Option.map (Prod.mk i)) v) ↔ (F i).Reachable u v := by
  classical
  constructor
  · intro h
    simpa using project_reachable F i h
  · exact fun h => h.map (blockHom F i)
theorem connected_star_iff (F : ι → SimpleGraph (Option A)) :
    (starGraph F).Connected ↔ ∀ i, (F i).Connected := by
  constructor
  · intro h i
    exact ⟨fun u v => (reachable_embed_iff F i u v).mp (h _ _ )⟩
  · intro h
    apply (connected_iff_exists_forall_reachable (starGraph F)).mpr
    refine ⟨none, ?_⟩
    intro x
    cases x with
    | none => exact .rfl
    | some x =>
      rcases x with ⟨i,a⟩
      exact (h i none (some a)).map (blockHom F i)
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
open SimpleGraph
variable {ι A : Type*}
private noncomputable def localCode (F : ι → SimpleGraph (Option A)) (i : ι)
    (c : (F i).ConnectedComponent) : Option (Σ j, {c : (F j).ConnectedComponent // c ≠ (F j).connectedComponentMk none}) := by
  classical
  exact if h : c = (F i).connectedComponentMk none then none else some ⟨i,⟨c,h⟩⟩
private noncomputable def vertexCode (F : ι → SimpleGraph (Option A)) :
    Option (ι × A) → Option (Σ j, {c : (F j).ConnectedComponent // c ≠ (F j).connectedComponentMk none})
  | none => none
  | some (i,a) => localCode F i ((F i).connectedComponentMk (some a))
@[simp] private theorem localCode_root (F : ι → SimpleGraph (Option A)) (i : ι) :
    localCode F i ((F i).connectedComponentMk none) = none := by
  classical
  simp [localCode]
@[simp] private theorem vertexCode_embed (F : ι → SimpleGraph (Option A)) (i : ι) (u : Option A) :
    vertexCode F ((Option.map (Prod.mk i)) u) = localCode F i ((F i).connectedComponentMk u) := by
  cases u <;> simp [vertexCode]
private theorem vertexCode_eq_of_reachable (F : ι → SimpleGraph (Option A)) {x y}
    (h : (starGraph F).Reachable x y) : vertexCode F x = vertexCode F y := by
  have hh : Relation.ReflTransGen Eq (vertexCode F x) (vertexCode F y) :=
    Relation.ReflTransGen.lift (vertexCode F) (by
      rintro u v ⟨i,a,b,hab,rfl,rfl⟩
      change vertexCode F (Option.map (Prod.mk i) a) = vertexCode F (Option.map (Prod.mk i) b)
      rw [vertexCode_embed F i a, vertexCode_embed F i b,
        ConnectedComponent.sound hab.reachable]) _ _
      (((starGraph F).reachable_iff_reflTransGen _ _).mp h)
  simpa only [Relation.reflTransGen_eq_self] using hh
private noncomputable def componentCode (F : ι → SimpleGraph (Option A)) :
    (starGraph F).ConnectedComponent → Option (Σ j, {c : (F j).ConnectedComponent // c ≠ (F j).connectedComponentMk none}) :=
  Quot.lift (vertexCode F) (fun _ _ h => vertexCode_eq_of_reachable F h)
private noncomputable def componentDecode (F : ι → SimpleGraph (Option A)) :
    Option (Σ j, {c : (F j).ConnectedComponent // c ≠ (F j).connectedComponentMk none}) → (starGraph F).ConnectedComponent
  | none => (starGraph F).connectedComponentMk none
  | some ⟨i,c⟩ => (ConnectedComponent.map (blockHom F i)) c.val
@[simp] private theorem componentCode_lift (F : ι → SimpleGraph (Option A)) (i : ι)
    (c : (F i).ConnectedComponent) :
    componentCode F ((ConnectedComponent.map (blockHom F i)) c) = localCode F i c := by
  induction c using ConnectedComponent.ind with
  | _ u => exact vertexCode_embed F i u
@[simp] private theorem componentDecode_localCode (F : ι → SimpleGraph (Option A)) (i : ι)
    (c : (F i).ConnectedComponent) :
    componentDecode F (localCode F i c) = (ConnectedComponent.map (blockHom F i)) c := by
  classical
  by_cases h : c = (F i).connectedComponentMk none
  · subst c
    simp only [localCode_root, componentDecode]; rfl
  · simp [localCode,h,componentDecode]
private theorem componentDecode_code (F : ι → SimpleGraph (Option A))
    (c : (starGraph F).ConnectedComponent) :
    componentDecode F (componentCode F c) = c := by
  induction c using ConnectedComponent.ind with
  | _ x =>
    cases x with
    | none => rfl
    | some x =>
      rcases x with ⟨i,a⟩
      change componentDecode F (localCode F i ((F i).connectedComponentMk (some a))) = _
      rw [componentDecode_localCode]
      rfl
private theorem componentCode_decode (F : ι → SimpleGraph (Option A))
    (c : Option (Σ j, {c : (F j).ConnectedComponent // c ≠ (F j).connectedComponentMk none})) :
    componentCode F (componentDecode F c) = c := by
  classical
  cases c with
  | none => rfl
  | some c =>
    rcases c with ⟨i,c⟩
    change componentCode F ((ConnectedComponent.map (blockHom F i)) c.val) = _
    rw [componentCode_lift]
    simp [localCode,c.property]
private noncomputable def componentEquiv (F : ι → SimpleGraph (Option A)) :
    (starGraph F).ConnectedComponent ≃ Option (Σ j, {c : (F j).ConnectedComponent // c ≠ (F j).connectedComponentMk none}) where
  toFun := componentCode F
  invFun := componentDecode F
  left_inv := componentDecode_code F
  right_inv := componentCode_decode F
private theorem card_nonrootComponent [Finite A] (F : ι → SimpleGraph (Option A)) (i : ι) :
    Nat.card ({c : (F i).ConnectedComponent // c ≠ (F i).connectedComponentMk none}) + 1 = Nat.card (F i).ConnectedComponent := by
  classical
  letI := Fintype.ofFinite (F i).ConnectedComponent
  let p := fun c : (F i).ConnectedComponent => c = (F i).connectedComponentMk none
  have heq : Fintype.card {c // p c} = 1 := Fintype.card_subtype_eq _
  have hpos : 0 < Fintype.card (F i).ConnectedComponent := Fintype.card_pos
  have hc := Fintype.card_subtype_compl p
  simp only [Nat.card_eq_fintype_card]
  change Fintype.card {c : (F i).ConnectedComponent // ¬ p c} + 1 = _
  rw [hc,heq]
  omega
private theorem component_count_star [Fintype ι] [Finite A] (F : ι → SimpleGraph (Option A)) :
    Nat.card (starGraph F).ConnectedComponent =
      1 + ∑ i : ι, (Nat.card (F i).ConnectedComponent - 1) := by
  classical
  letI : ∀ i, Fintype ((F i).ConnectedComponent) := fun i => Fintype.ofFinite _
  rw [Nat.card_congr (componentEquiv F)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_option,Fintype.card_sigma]
  have hh (i : ι) : Fintype.card ({c : (F i).ConnectedComponent // c ≠ (F i).connectedComponentMk none}) =
      Fintype.card (F i).ConnectedComponent - 1 := by
    have h := card_nonrootComponent F i
    simpa only [Nat.card_eq_fintype_card] using Nat.eq_sub_of_add_eq h
  simp_rw [hh]
  exact Nat.add_comm _ _
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
open SimpleGraph
variable {ι A : Type*}
theorem liftEdge_injective (i : ι) : Function.Injective ((Sym2.map (Option.map (Prod.mk i)) : Sym2 (Option A) → Sym2 (Option (ι × A)))) :=
  Sym2.map.injective (embed_injective i)
theorem liftEdge_block_unique {i j : ι} {e f : Sym2 (Option A)}
    (he : ¬e.IsDiag) (h : (Sym2.map (Option.map (Prod.mk i))) e = (Sym2.map (Option.map (Prod.mk j))) f) : i = j := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    induction f using Sym2.inductionOn with
    | _ x y =>
      simp only [Sym2.map_mk,Sym2.eq_iff] at h
      simp only [Sym2.mk_isDiag_iff] at he
      rcases h with ⟨hux,hvy⟩ | ⟨huy,hvx⟩
      · cases u <;> cases v <;> cases x <;> cases y <;> simp_all []
      · cases u <;> cases v <;> cases x <;> cases y <;> simp_all []
theorem liftEdgeMem (B : ι → SimpleGraph (Option A)) (i : ι) {e : Sym2 (Option A)}
    (he : e ∈ (B i).edgeSet) : (Sym2.map (Option.map (Prod.mk i))) e ∈ (starGraph B).edgeSet := by
  induction e using Sym2.inductionOn with
  | _ u v => exact ⟨i,u,v,he,rfl,rfl⟩
theorem star_edge_decomp (B : ι → SimpleGraph (Option A)) {e : Sym2 (Option (ι × A))} :
    e ∈ (starGraph B).edgeSet ↔ ∃ i f, f ∈ (B i).edgeSet ∧ (Sym2.map (Option.map (Prod.mk i))) f = e := by
  constructor
  · induction e using Sym2.inductionOn with
    | _ x y =>
      rintro ⟨i,u,v,huv,rfl,rfl⟩
      exact ⟨i,s(u,v),huv,rfl⟩
  · rintro ⟨i,f,hf,rfl⟩
    exact liftEdgeMem B i hf
def edgeForward (B : ι → SimpleGraph (Option A)) :
    (Σ i, (B i).edgeSet) → (starGraph B).edgeSet :=
  fun e => ⟨(Sym2.map (Option.map (Prod.mk e.1))) e.2.val,liftEdgeMem B e.1 e.2.property⟩
theorem edgeForwardBijective (B : ι → SimpleGraph (Option A)) :
    Function.Bijective (edgeForward B) := by
  constructor
  · rintro ⟨i,e⟩ ⟨j,f⟩ h
    have he : ¬ e.val.IsDiag := (B i).not_isDiag_of_mem_edgeSet e.property
    have hv := congrArg Subtype.val h
    have hij : i = j := liftEdge_block_unique he hv
    subst j
    have hef : e = f := Subtype.ext (liftEdge_injective i hv)
    subst f
    rfl
  · intro e
    obtain ⟨i,f,hf,heq⟩ := star_edge_decomp B |>.mp e.property
    exact ⟨⟨i,⟨f,hf⟩⟩,Subtype.ext heq⟩
noncomputable def edgeEquiv (B : ι → SimpleGraph (Option A)) :
    (Σ i, (B i).edgeSet) ≃ (starGraph B).edgeSet :=
  Equiv.ofBijective (edgeForward B) (edgeForwardBijective B)
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
open SimpleGraph
variable {ι A : Type*} [Fintype ι] [Finite A]
theorem component_count_star_difference
    (F F' : ι → SimpleGraph (Option A)) (i : ι) (h : ∀ j, j ≠ i → F j = F' j) :
    Nat.card (starGraph F).ConnectedComponent - Nat.card (starGraph F').ConnectedComponent =
      Nat.card (F i).ConnectedComponent - Nat.card (F' i).ConnectedComponent := by
  classical
  have hs : (∑ j ∈ Finset.univ.erase i, (Nat.card (F j).ConnectedComponent - 1)) =
      ∑ j ∈ Finset.univ.erase i, (Nat.card (F' j).ConnectedComponent - 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [h j (Finset.mem_erase.mp hj).1]
  have hF := Finset.sum_erase_add Finset.univ
    (fun j => Nat.card (F j).ConnectedComponent - 1) (Finset.mem_univ i)
  have hF' := Finset.sum_erase_add Finset.univ
    (fun j => Nat.card (F' j).ConnectedComponent - 1) (Finset.mem_univ i)
  have hi := card_nonrootComponent F i
  have hi' := card_nonrootComponent F' i
  rw [component_count_star,component_count_star]
  omega
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
