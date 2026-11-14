/- GID: D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CoreArchitecture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Two actual dissociation witnesses in arbitrary shared-port core architectures. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodPorts
import D5.S3.Combinatorics.Graph.StarForming.HeawoodInterfaces
import D5.S3.Combinatorics.Graph.StarForming.RegularCompensation
import Mathlib.Data.Finset.Sum

/-! CORE_BLOCK_GAP_BARRIER at subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
High cycles, hub groupings and repeated core attachments are parameters.
The two witnesses are alternatives in the same graph, not combined sets. -/
namespace D5.S3.Combinatorics.Graph.StarForming.CoreArchitecture
open StarFormingDissociationRefutation Cubic
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

abbrev Vertex (H Y B : Type) := H ⊕ (H ⊕ (H ⊕ (Y ⊕ (B × Fin 14))))
abbrev high {H Y B : Type} (h : H) : Vertex H Y B := .inl h
abbrev leaf {H Y B : Type} (h : H) : Vertex H Y B := .inr (.inl h)
abbrev outside {H Y B : Type} (h : H) : Vertex H Y B := .inr (.inr (.inl h))
abbrev hub {H Y B : Type} (y : Y) : Vertex H Y B := .inr (.inr (.inr (.inl y)))
abbrev block {H Y B : Type} (b : B) (v : Fin 14) : Vertex H Y B :=
  .inr (.inr (.inr (.inr (b,v))))

variable {H Y B : Type}

def adjacency (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) : Vertex H Y B → Vertex H Y B → Prop
  | .inl h,.inl k => Q.Adj h k
  | .inl h,.inr (.inl k) => h = k
  | .inr (.inl h),.inl k => h = k
  | .inr (.inl h),.inr (.inr (.inl k)) => h = k
  | .inr (.inr (.inl h)),.inr (.inl k) => h = k
  | .inr (.inl h),.inr (.inr (.inr (.inl y))) => group h = y
  | .inr (.inr (.inr (.inl y))),.inr (.inl h) => group h = y
  | .inr (.inr (.inl h)),.inr (.inr (.inl k)) => X.Adj h k
  | .inr (.inr (.inl h)),.inr (.inr (.inr (.inr (b,v)))) =>
      ∃ p : Fin 2, v = HeawoodInterfaces.port p ∧ attach (b,p) = h
  | .inr (.inr (.inr (.inr (b,v)))),.inr (.inr (.inl h)) =>
      ∃ p : Fin 2, v = HeawoodInterfaces.port p ∧ attach (b,p) = h
  | .inr (.inr (.inr (.inr (b,v)))),.inr (.inr (.inr (.inr (c,w)))) =>
      b = c ∧ BrokenAdj v w
  | _,_ => False

/-- The graph contains exactly the specified architecture edges. -/
def graph (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) : SimpleGraph (Vertex H Y B) where
  Adj := adjacency Q X group attach
  symm := ⟨by
    intro v w h
    rcases v with h | h | h | y | ⟨b,v⟩ <;>
      rcases w with k | k | k | z | ⟨c,w⟩ <;>
      simp only [adjacency] at h ⊢ <;> try tauto
    all_goals exact ⟨h.1.symm,(broken_simple.2 _ _).mp h.2⟩⟩
  loopless := ⟨by
    intro v hn
    rcases v with h | h | h | y | ⟨b,v⟩ <;>
      simp only [adjacency] at hn
    all_goals first | exact Q.irrefl hn | exact X.irrefl hn | exact broken_simple.1 _ hn.2⟩

noncomputable instance (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) : DecidableRel (graph Q X group attach).Adj := Classical.decRel _

/-- First witness: every leaf, odd highs, even X, and the point side of each block. -/
def first (color : H → Bool) : Vertex H Y B → Prop
  | .inl h => color h = true
  | .inr (.inl _) => True
  | .inr (.inr (.inl h)) => color h = false
  | .inr (.inr (.inr (.inl _))) => False
  | .inr (.inr (.inr (.inr (_,v)))) => v.val < 7

/-- Second witness: every leaf, odd highs and the original four-edge block eight-set. -/
def second (color : H → Bool) : Vertex H Y B → Prop
  | .inl h => color h = true
  | .inr (.inl _) => True
  | .inr (.inr (.inl _)) => False
  | .inr (.inr (.inr (.inl _))) => False
  | .inr (.inr (.inr (.inr (_,v)))) => v ∈ HeawoodPorts.eightSet

private theorem port_color : ∀ p : Fin 2,
    ((HeawoodInterfaces.port p).val < 7 ↔ p = 0) := by decide +kernel

private theorem broken_opposite : ∀ v w : Fin 14,
    BrokenAdj v w → ¬ (v.val < 7 ↔ w.val < 7) := by
  unfold BrokenAdj brokenNeighbors fanoNeighbors
  decide +kernel

private theorem first_neighbor (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (color : H → Bool)
    (hQ : ∀ h k, Q.Adj h k → color h ≠ color k)
    (hX : ∀ h k, X.Adj h k → color h ≠ color k)
    (ha : ∀ b p, color (attach (b,p)) = decide (p = 0))
    (v w : Vertex H Y B) (hv : first color v) (hw : first color w)
    (hadj : (graph Q X group attach).Adj v w) :
    (∃ h, color h = true ∧
      ((v = high h ∧ w = leaf h) ∨ (v = leaf h ∧ w = high h))) ∨
    (∃ h, color h = false ∧
      ((v = outside h ∧ w = leaf h) ∨ (v = leaf h ∧ w = outside h))) := by
  rcases v with h | h | h | y | ⟨b,v⟩ <;>
    rcases w with k | k | k | z | ⟨c,w⟩ <;>
    simp only [first,graph,adjacency] at hv hw hadj
  all_goals first
    | contradiction
    | (exact (hQ _ _ hadj (hv.trans hw.symm)).elim)
    | (exact (hX _ _ hadj (hv.trans hw.symm)).elim)
    | (subst k; exact Or.inl ⟨h,hv,Or.inl ⟨rfl,rfl⟩⟩)
    | (subst k; exact Or.inl ⟨h,hw,Or.inr ⟨rfl,rfl⟩⟩)
    | (subst k; exact Or.inr ⟨h,hw,Or.inr ⟨rfl,rfl⟩⟩)
    | (subst k; exact Or.inr ⟨h,hv,Or.inl ⟨rfl,rfl⟩⟩)
    | skip
  · obtain ⟨p,hp,he⟩ := hadj
    have hc := ha c p
    have hpc : p = 0 := (port_color p).mp (hp ▸ hw)
    subst p
    simp only [he,decide_true] at hc
    simp_all
  · obtain ⟨p,hp,he⟩ := hadj
    have hc := ha b p
    have hpc : p = 0 := (port_color p).mp (hp ▸ hv)
    subst p
    simp only [he,decide_true] at hc
    simp_all
  · exact (broken_opposite v w hadj.2 (iff_of_true hv hw)).elim

/-- Both appearances of any selected edge in the first witness share one mate. -/
theorem first_dissociation (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (color : H → Bool)
    (hQ : ∀ h k, Q.Adj h k → color h ≠ color k)
    (hX : ∀ h k, X.Adj h k → color h ≠ color k)
    (ha : ∀ b p, color (attach (b,p)) = decide (p = 0)) :
    DissociationCover.Dissociates (graph Q X group attach).Adj (first color) := by
  intro v a b hv ha' hb hva hvb
  have h1 := first_neighbor Q X group attach color hQ hX ha v a hv ha' hva
  have h2 := first_neighbor Q X group attach color hQ hX ha v b hv hb hvb
  rcases h1 with ⟨h,hc,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ | ⟨h,hc,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ <;>
    rcases h2 with ⟨k,hk,(⟨he,rfl⟩ | ⟨he,rfl⟩)⟩ | ⟨k,hk,(⟨he,rfl⟩ | ⟨he,rfl⟩)⟩ <;>
    simp_all [high,leaf,outside]

private theorem second_high_neighbor (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (color : H → Bool)
    (hQ : ∀ h k, Q.Adj h k → color h ≠ color k)
    (h : H) (hc : color h = true) (w : Vertex H Y B)
    (hw : second color w) (hadj : (graph Q X group attach).Adj (high h) w) :
    w = leaf h := by
  rcases w with k | k | k | y | ⟨b,v⟩ <;>
    simp only [second,graph,adjacency,high] at hw hadj
  · exact (hQ _ _ hadj (hc.trans hw.symm)).elim
  · subst k; rfl
  all_goals contradiction

private theorem second_leaf_neighbor (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (color : H → Bool)
    (h : H) (w : Vertex H Y B) (hw : second color w)
    (hadj : (graph Q X group attach).Adj (leaf h) w) : w = high h := by
  rcases w with k | k | k | y | ⟨b,v⟩ <;>
    simp only [second,graph,adjacency,leaf] at hw hadj
  · subst k; rfl
  all_goals contradiction

private theorem second_block_neighbor (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (color : H → Bool)
    (b : B) (v : Fin 14) (w : Vertex H Y B) (hw : second color w)
    (hadj : (graph Q X group attach).Adj (block b v) w) :
    ∃ t : Fin 14, w = block b t ∧ t ∈ HeawoodPorts.eightSet ∧ BrokenAdj v t := by
  rcases w with k | k | k | y | ⟨c,t⟩ <;>
    simp only [second,graph,adjacency,block] at hw hadj
  all_goals try contradiction
  obtain ⟨rfl,hvt⟩ := hadj
  exact ⟨t,rfl,hw,hvt⟩

/-- The second witness is valid even when many block ports share one X vertex. -/
theorem second_dissociation (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (color : H → Bool)
    (hQ : ∀ h k, Q.Adj h k → color h ≠ color k) :
    DissociationCover.Dissociates (graph Q X group attach).Adj (second color) := by
  intro v a b hv ha hb hva hvb
  rcases v with h | h | h | y | ⟨c,v⟩
  · have he1 := second_high_neighbor Q X group attach color hQ h hv a ha hva
    have he2 := second_high_neighbor Q X group attach color hQ h hv b hb hvb
    exact he1.trans he2.symm
  · have he1 := second_leaf_neighbor Q X group attach color h a ha hva
    have he2 := second_leaf_neighbor Q X group attach color h b hb hvb
    exact he1.trans he2.symm
  · exact hv.elim
  · exact hv.elim
  · obtain ⟨s,rfl,hs,hvs⟩ := second_block_neighbor Q X group attach color c v a ha hva
    obtain ⟨t,rfl,ht,hvt⟩ := second_block_neighbor Q X group attach color c v b hb hvb
    have hl := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp
      HeawoodPorts.selections.1 v hv s hs t ht hvs hvt
    exact congrArg (block c) hl

/-- The canonical forming witness omits every attachment endpoint. -/
def forming : Vertex H Y B → Prop
  | .inl _ => True
  | .inr (.inl _) => True
  | .inr (.inr (.inl _)) => False
  | .inr (.inr (.inr (.inl _))) => False
  | .inr (.inr (.inr (.inr (_,v)))) => fanoSelected v

private theorem selected_fano_broken : ∀ a b : Fin 14,
    fanoSelected a ∨ fanoSelected b → (FanoAdj a b ↔ BrokenAdj a b) := by
  unfold FanoAdj BrokenAdj fanoSelected brokenNeighbors fanoNeighbors
  decide +kernel

private theorem forming_block_neighbor (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (b : B) (v : Fin 14) (w : Vertex H Y B)
    (hw : forming w) (hadj : (graph Q X group attach).Adj (block b v) w) :
    ∃ t, w = block b t ∧ fanoSelected t ∧ FanoAdj v t := by
  rcases w with k | k | k | y | ⟨c,t⟩ <;>
    simp only [forming,graph,adjacency,block] at hw hadj
  all_goals try contradiction
  obtain ⟨rfl,hvt⟩ := hadj
  exact ⟨t,rfl,hw,(selected_fano_broken v t (Or.inr hw)).mpr hvt⟩

private theorem forming_X_neighbor (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (h : H) (w : Vertex H Y B)
    (hw : forming w) (hadj : (graph Q X group attach).Adj (outside h) w) :
    w = leaf h := by
  rcases w with k | k | k | y | ⟨b,v⟩ <;>
    simp only [forming,graph,adjacency,outside] at hw hadj
  all_goals try contradiction
  · subst k; rfl
  · obtain ⟨p,rfl,_⟩ := hadj
    have hp : ∀ p : Fin 2, ¬ fanoSelected (HeawoodInterfaces.port p) := by decide +kernel
    exact (hp p hw).elim

private theorem forming_U_neighbor (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (h : H) (w : Vertex H Y B)
    (hw : forming w) (hadj : (graph Q X group attach).Adj (leaf h) w) :
    w = high h := by
  rcases w with k | k | k | y | ⟨b,v⟩ <;>
    simp only [forming,graph,adjacency,leaf] at hw hadj
  · subst k; rfl
  all_goals contradiction

/-- Every high/leaf deletion fails at its own X vertex; the received local
Heawood certificates handle every block deletion. Attachments may repeat. -/
theorem forming_minimal (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (hgroup : Function.Surjective group) :
    Regular.Minimal (graph Q X group attach).Adj forming := by
  apply Subcubic.minimal_of_deletion_failures
  · intro v hv
    rcases v with h | h | h | y | ⟨b,v⟩
    · exact (hv trivial).elim
    · exact (hv trivial).elim
    · exact Or.inr ⟨leaf h,high h,trivial,trivial,rfl,rfl⟩
    · obtain ⟨h,rfl⟩ := hgroup y
      exact Or.inr ⟨leaf h,high h,trivial,trivial,rfl,rfl⟩
    · rcases fano_forms v hv with ⟨a,c,ha,hc,hne,hva,hvc⟩ | ⟨c,l,hc,hl,hvc,hcl⟩
      · exact Or.inl ⟨block b a,block b c,ha,hc,
          by intro he; exact hne (by simpa [block] using he),
          ⟨rfl,(selected_fano_broken v a (Or.inr ha)).mp hva⟩,
          ⟨rfl,(selected_fano_broken v c (Or.inr hc)).mp hvc⟩⟩
      · exact Or.inr ⟨block b c,block b l,hc,hl,
          ⟨rfl,(selected_fano_broken v c (Or.inr hc)).mp hvc⟩,
          ⟨rfl,(selected_fano_broken c l (Or.inl hc)).mp hcl⟩⟩
  · intro d hd
    rcases d with h | h | h | y | ⟨b,v⟩
    · refine ⟨outside h,by simp [forming,outside],?_⟩
      rintro (⟨a,c,ha,hc,he,hxa,hxc⟩ | ⟨c,l,hc,hl,hxc,hcl⟩)
      · exact he ((forming_X_neighbor Q X group attach h a ha.1 hxa).trans
          (forming_X_neighbor Q X group attach h c hc.1 hxc).symm)
      · have hcu := forming_X_neighbor Q X group attach h c hc.1 hxc
        subst c
        exact hl.2 (forming_U_neighbor Q X group attach h l hl.1 hcl)
    · refine ⟨outside h,by simp [forming,outside],?_⟩
      rintro (⟨a,c,ha,hc,he,hxa,hxc⟩ | ⟨c,l,hc,hl,hxc,hcl⟩)
      · exact ha.2 (forming_X_neighbor Q X group attach h a ha.1 hxa)
      · exact hc.2 (forming_X_neighbor Q X group attach h c hc.1 hxc)
    · exact hd.elim
    · exact hd.elim
    · refine ⟨block b (fanoFailure v),?_,?_⟩
      · rintro ⟨hs,he⟩
        exact (fano_deletion_failures v hd).1 ⟨hs,fun hv => he (congrArg (block b) hv)⟩
      · intro ht
        apply (fano_deletion_failures v hd).2
        rcases ht with ⟨a,c,ha,hc,he,hxa,hxc⟩ | ⟨c,l,hc,hl,hxc,hcl⟩
        · obtain ⟨a,rfl,has,hva⟩ := forming_block_neighbor Q X group attach b _ a ha.1 hxa
          obtain ⟨c,rfl,hcs,hvc⟩ := forming_block_neighbor Q X group attach b _ c hc.1 hxc
          exact Or.inl ⟨a,c,⟨has,fun he => ha.2 (congrArg (block b) he)⟩,
            ⟨hcs,fun he => hc.2 (congrArg (block b) he)⟩,
            fun he' => he (congrArg (block b) he'),hva,hvc⟩
        · obtain ⟨c,rfl,hcs,hvc⟩ := forming_block_neighbor Q X group attach b _ c hc.1 hxc
          obtain ⟨l,rfl,hls,hcl⟩ := forming_block_neighbor Q X group attach b _ l hl.1 hcl
          exact Or.inr ⟨c,l,⟨hcs,fun he => hc.2 (congrArg (block b) he)⟩,
            ⟨hls,fun he => hl.2 (congrArg (block b) he)⟩,hvc,hcl⟩

variable [Fintype H] [Fintype Y] [Fintype B]
variable [DecidableEq H] [DecidableEq Y] [DecidableEq B]

noncomputable def firstSet (color : H → Bool) : Finset (Vertex H Y B) :=
  by classical exact Finset.univ.filter (first color)
noncomputable def secondSet (color : H → Bool) : Finset (Vertex H Y B) :=
  by classical exact Finset.univ.filter (second color)

noncomputable def formingSet : Finset (Vertex H Y B) :=
  by classical exact Finset.univ.filter forming

private theorem group_surjective_of_regular (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H)
    (hregular : ∀ v, DegreeCapacity.degree (graph Q X group attach) v = 3) :
    Function.Surjective group := by
  classical
  intro y
  by_contra hn
  have hempty : (Finset.univ.filter ((graph Q X group attach).Adj (hub y))) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have he := (Finset.mem_filter.mp hw).2
    rcases w with h | h | h | z | ⟨b,v⟩ <;>
      simp only [graph,adjacency,hub] at he
    all_goals first | contradiction | exact hn ⟨h,he⟩
  have hc := hregular (hub y)
  change (Finset.univ.filter ((graph Q X group attach).Adj (hub y))).card = 3 at hc
  rw [hempty,Finset.card_empty] at hc
  omega

private theorem forming_card : (formingSet (H := H) (Y := Y) (B := B)).card =
    2*Fintype.card H + 8*Fintype.card B := by
  classical
  have h8 : (Finset.univ.filter fanoSelected).card = 8 := by decide +kernel
  have he : formingSet (H := H) (Y := Y) (B := B) =
      (Finset.univ : Finset H).disjSum
      ((Finset.univ : Finset H).disjSum
      ((∅ : Finset H).disjSum ((∅ : Finset Y).disjSum
      (Finset.univ.product (Finset.univ.filter fanoSelected))))) := by
    ext v
    rcases v with h | h | h | y | ⟨b,v⟩ <;>
      simp [formingSet,forming,Finset.product_eq_sprod]
  rw [he]
  simp only [Finset.product_eq_sprod,Finset.card_disjSum,Finset.card_product,
    Finset.card_univ,Finset.card_empty,h8]
  omega

private theorem blocks_le_highs (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H)
    (hregular : ∀ v, DegreeCapacity.degree (graph Q X group attach) v = 3) :
    Fintype.card B ≤ Fintype.card H := by
  classical
  let fiber (h : H) := Finset.univ.filter (fun bp : B × Fin 2 => attach bp = h)
  let f : B × Fin 2 → Vertex H Y B := fun bp => block bp.1 (HeawoodInterfaces.port bp.2)
  have hf : Function.Injective f := by
    intro a b he
    have hp : Function.Injective HeawoodInterfaces.port := by decide +kernel
    have he' : (a.1,HeawoodInterfaces.port a.2) =
        (b.1,HeawoodInterfaces.port b.2) := by simpa [f,block] using he
    have h1 : a.1 = b.1 := congrArg (fun x : B × Fin 14 => x.1) he'
    have h2 : a.2 = b.2 := hp (congrArg (fun x : B × Fin 14 => x.2) he')
    exact Prod.ext h1 h2
  have hcap (h : H) : (fiber h).card ≤ 2 := by
    have hnot : leaf h ∉ (fiber h).image f := by simp [f,block,leaf]
    have hsub : insert (leaf h) ((fiber h).image f) ⊆
        Finset.univ.filter ((graph Q X group attach).Adj (outside h)) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Finset.mem_filter.mpr ⟨by simp,rfl⟩
      · obtain ⟨⟨b,p⟩,hbp,rfl⟩ := Finset.mem_image.mp hw
        exact Finset.mem_filter.mpr ⟨by simp,p,rfl,(Finset.mem_filter.mp hbp).2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot,Finset.card_image_of_injective _ hf] at hc
    have hr := hregular (outside h)
    change (Finset.univ.filter ((graph Q X group attach).Adj (outside h))).card = 3 at hr
    omega
  have hsum : Fintype.card (B × Fin 2) = ∑ h : H, (fiber h).card := by
    simpa only [Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (B × Fin 2)))
        (f := attach) (t := Finset.univ) (by intro x _; exact Finset.mem_univ _))
  have hbound : (∑ h : H, (fiber h).card) ≤ ∑ _h : H, 2 :=
    Finset.sum_le_sum (fun h _ => hcap h)
  simp only [Fintype.card_prod,Fintype.card_fin] at hsum
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hbound
  omega

/-- Cubic regularity itself supplies every hub with a preimage. The actual
minimal forming witness therefore gives this lower bound without an additional
surjectivity premise. -/
theorem sf_lower (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H)
    (hregular : ∀ v, DegreeCapacity.degree (graph Q X group attach) v = 3) :
    2*Fintype.card H + 8*Fintype.card B ≤ SF (graph Q X group attach) 2 := by
  classical
  have hm : IsMinimalStarForming (graph Q X group attach) 2
      (formingSet (H := H) (Y := Y) (B := B)) := by
    apply (regular_minimal_iff _ _).mp
    simpa [formingSet] using
      forming_minimal Q X group attach (group_surjective_of_regular Q X group attach hregular)
  rw [← forming_card (H := H) (Y := Y) (B := B)]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hm⟩)

/-- Exact counts of the two actual witnesses, with the high color counts
separate until the displayed architecture balance is imposed. -/
theorem witness_cardinalities (color : H → Bool) :
    (firstSet (Y := Y) (B := B) color).card =
      (Finset.univ.filter (fun h => color h = true)).card + Fintype.card H +
      (Finset.univ.filter (fun h => color h = false)).card + 7*Fintype.card B ∧
    (secondSet (Y := Y) (B := B) color).card =
      (Finset.univ.filter (fun h => color h = true)).card + Fintype.card H +
      8*Fintype.card B := by
  classical
  have h7 : (Finset.univ.filter (fun v : Fin 14 => v.val < 7)).card = 7 := by decide +kernel
  have h8 : (Finset.univ.filter (fun v : Fin 14 => v ∈ HeawoodPorts.eightSet)).card = 8 := by
    decide +kernel
  have he1 : firstSet (Y := Y) (B := B) color =
      (Finset.univ.filter (fun h => color h = true)).disjSum
      ((Finset.univ : Finset H).disjSum
      ((Finset.univ.filter (fun h => color h = false)).disjSum
      ((∅ : Finset Y).disjSum
      (Finset.univ.product (Finset.univ.filter (fun v : Fin 14 => v.val < 7)))))) := by
    ext v
    rcases v with h | h | h | y | ⟨b,v⟩ <;>
      simp [firstSet, first, Finset.product_eq_sprod]
  have he2 : secondSet (Y := Y) (B := B) color =
      (Finset.univ.filter (fun h => color h = true)).disjSum
      ((Finset.univ : Finset H).disjSum
      ((∅ : Finset H).disjSum
      ((∅ : Finset Y).disjSum
      (Finset.univ.product (Finset.univ.filter (fun v : Fin 14 =>
        v ∈ HeawoodPorts.eightSet)))))) := by
    ext v
    rcases v with h | h | h | y | ⟨b,v⟩ <;>
      simp [secondSet, second, Finset.product_eq_sprod]
  rw [he1, he2]
  simp only [Finset.product_eq_sprod, Finset.card_disjSum, Finset.card_product, Finset.card_univ,
    Finset.card_empty, h7, h8]
  constructor <;> omega

/-- The two lower bounds use actual dissociation selections, with no port
injectivity assumption and no restriction on the number of high cycles. -/
theorem beta_lower_bounds (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (color : H → Bool)
    (hQ : ∀ h k, Q.Adj h k → color h ≠ color k)
    (hX : ∀ h k, X.Adj h k → color h ≠ color k)
    (ha : ∀ b p, color (attach (b,p)) = decide (p = 0))
    (r : ℕ) (hH : Fintype.card H = 6*r)
    (ht : (Finset.univ.filter (fun h => color h = true)).card = 3*r)
    (hf : (Finset.univ.filter (fun h => color h = false)).card = 3*r) :
    12*r + 7*Fintype.card B ≤ beta (graph Q X group attach) 2 ∧
      9*r + 8*Fintype.card B ≤ beta (graph Q X group attach) 2 := by
  classical
  have hcard := witness_cardinalities (Y := Y) (B := B) color
  have h1 : IsKIndependent (graph Q X group attach) 2 (firstSet color) := by
    apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
    intro v hv a ha' b hb hva hvb
    exact first_dissociation Q X group attach color hQ hX ha v a b
      (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp ha').2 (Finset.mem_filter.mp hb).2 hva hvb
  have h2 : IsKIndependent (graph Q X group attach) 2 (secondSet color) := by
    apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
    intro v hv a ha' b hb hva hvb
    exact second_dissociation Q X group attach color hQ v a b
      (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp ha').2 (Finset.mem_filter.mp hb).2 hva hvb
  have hc1 : (firstSet (Y := Y) (B := B) color).card = 12*r + 7*Fintype.card B := by
    rw [hcard.1,hH,ht,hf]; omega
  have hc2 : (secondSet (Y := Y) (B := B) color).card = 9*r + 8*Fintype.card B := by
    rw [hcard.2,hH,ht]; omega
  letI : DecidablePred (IsKIndependent (graph Q X group attach) 2) :=
    instDecidableIsKIndependent _ _
  constructor
  · rw [← hc1]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,h1⟩)
  · rw [← hc2]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,h2⟩)

/-- The enlarged architecture's sharp upper coefficient, extracted from the
actual graph and the two displayed witnesses. Cubic bipartiteness is an explicit
construction requirement; attachments may repeat. -/
theorem architecture_bounds (Q X : SimpleGraph H) (group : H → Y)
    (attach : B × Fin 2 → H) (color : H → Bool)
    (hQ : ∀ h k, Q.Adj h k → color h ≠ color k)
    (hX : ∀ h k, X.Adj h k → color h ≠ color k)
    (ha : ∀ b p, color (attach (b,p)) = decide (p = 0))
    (r : ℕ) (hH : Fintype.card H = 6*r) (hY : Fintype.card Y = 2*r)
    (ht : (Finset.univ.filter (fun h => color h = true)).card = 3*r)
    (hf : (Finset.univ.filter (fun h => color h = false)).card = 3*r)
    (hG : (graph Q X group attach).Colorable 2)
    (hregular : ∀ v, DegreeCapacity.degree (graph Q X group attach) v = 3) :
    let G := graph Q X group attach
    let n := Fintype.card (Vertex H Y B)
    let g := SF G 2 - beta G 2
    n = 20*r + 14*Fintype.card B ∧
    Fintype.card B ≤ 6*r ∧
    12*r + 8*Fintype.card B ≤ SF G 2 ∧
    33*n ≤ 62*beta G 2 ∧
    g ≤ Fintype.card B ∧ 7*g ≤ 15*r+2*Fintype.card B ∧ 62*g ≤ 3*n ∧
    (62*g = 3*n → Fintype.card B = 3*r ∧ beta G 2 = 33*r ∧
      SF G 2 = 36*r ∧ n = 62*r) ∧
    (Fintype.card B ≤ 3*r → 62*g+20*(3*r-Fintype.card B) ≤ 3*n) ∧
    (3*r ≤ Fintype.card B → 170*(Fintype.card B-3*r) ≤ 7*(3*n-62*g)) ∧
    (62*g = 3*n ↔ Fintype.card B = 3*r ∧ beta G 2 = 33*r) ∧
    (Fintype.card B ≤ 3*r →
      7*(3*n-62*g) = 140*(3*r-Fintype.card B) +
        310*(beta G 2-(12*r+7*Fintype.card B)) +
        62*(3*n+2*beta G 2-7*SF G 2)) ∧
    (3*r ≤ Fintype.card B →
      7*(3*n-62*g) = 170*(Fintype.card B-3*r) +
        310*(beta G 2-(9*r+8*Fintype.card B)) +
        62*(3*n+2*beta G 2-7*SF G 2)) := by
  classical
  dsimp only
  have horder : Fintype.card (Vertex H Y B) = 20*r + 14*Fintype.card B := by
    simp only [Vertex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,hH,hY]
    omega
  have hb := beta_lower_bounds Q X group attach color hQ hX ha r hH ht hf
  have hc := RegularCompensation.sf_regular_bound (graph Q X group attach) hG 3 hregular
  have hl := sf_lower Q X group attach hregular
  have hbl := blocks_le_highs Q X group attach hregular
  rw [hH] at hl
  rw [hH] at hbl
  have hs := beta_le_sf (graph Q X group attach)
  have hg : SF (graph Q X group attach) 2 = beta (graph Q X group attach) 2 +
      (SF (graph Q X group attach) 2 - beta (graph Q X group attach) 2) := by omega
  have hgap : 62*(SF (graph Q X group attach) 2 - beta (graph Q X group attach) 2) ≤
      3*Fintype.card (Vertex H Y B) := by omega
  refine ⟨horder,hbl,?_,?_,?_,?_,hgap,?_,?_,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · intro he; constructor <;> omega
  · intro he; omega
  · intro he; omega
  · constructor
    · intro he; constructor <;> omega
    · rintro ⟨he1,he2⟩; omega
  · intro he; omega
  · intro he; omega

end D5.S3.Combinatorics.Graph.StarForming.CoreArchitecture
