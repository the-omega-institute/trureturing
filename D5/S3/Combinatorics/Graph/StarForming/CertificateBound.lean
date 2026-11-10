/- GID: D5/S3/Combinatorics/Graph/StarForming/CertificateBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CertificateBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Disjoint high-degree certificates bound minimal two-star-forming sets in every finite simple graph. -/

import D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation
import Mathlib.Tactic.Push

/-!
The complete certificate argument received from docs/STAR_FORMING_CERTIFICATES.md
at subquorum-colorings revision 2e430b6481d4959f05f6d805871117261257e39d.
The saved proof body is reused without an exchange-preserves-dissociation assumption.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.CertificateBound

open D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices with at least two neighbours in the selected set. -/
def high (S : Finset V) : Finset V :=
  S.filter fun s => 2 ≤ (S.filter (G.Adj s)).card

/-- An outside vertex left on no (non-induced) two-leaf star after deleting s. -/
def Certificate (S : Finset V) (s x : V) : Prop :=
  x ∉ S ∧ ¬ ∃ (c : V) (L : Finset V), L.card = 2 ∧ c ∉ L ∧
    insert c L ⊆ insert x (S.erase s) ∧ (∀ y ∈ L, G.Adj c y) ∧ x ∈ insert c L

private theorem centered_path (S : Finset V) (s : V)
    (hs : 2 ≤ (S.filter (G.Adj s)).card) :
    ∃ L : Finset V, L.card = 2 ∧ s ∉ L ∧
      insert s L ⊆ insert s S ∧ (∀ y ∈ L, G.Adj s y) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
    1 < (S.filter (G.Adj s)).card)
  rcases Finset.mem_filter.mp ha with ⟨ha, hsa⟩
  rcases Finset.mem_filter.mp hb with ⟨hb, hsb⟩
  refine ⟨{a,b}, by simp [hab], ?_, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl) <;> exact G.irrefl (by assumption)
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ha
    · exact Or.inr hb
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption

/-- Inclusion-minimality supplies a certificate outside S for every high vertex. -/
theorem certificate_exists (S : Finset V) (hS : IsMinimalStarForming G 2 S)
    (s : V) (hs : s ∈ high G S) : ∃ x, Certificate G S s x := by
  classical
  rcases Finset.mem_filter.mp hs with ⟨hs, hd⟩
  have hn := hS.2 (S.erase s) (Finset.erase_ssubset hs)
  unfold IsStarForming at hn
  push Not at hn
  obtain ⟨x, hx, hbad⟩ := hn
  have hxs : x ≠ s := by
    intro he
    subst x
    obtain ⟨L, hL, hc, hsub, ha⟩ := centered_path G S s hd
    apply hbad s L hL hc
    · simpa [Finset.insert_erase hs, hs] using hsub
    · exact ha
    · simp
  refine ⟨x, ?_, ?_⟩
  · intro hmem
    exact hx (Finset.mem_erase.mpr ⟨hxs, hmem⟩)
  · rintro ⟨c,L,hL,hc,hsub,ha,hx'⟩
    exact hbad c L hL hc hsub ha hx'

private theorem certificate_forces_mem (S : Finset V) (s x c : V) (L : Finset V)
    (hcert : Certificate G S s x) (hL : L.card = 2) (hc : c ∉ L)
    (hsub : insert c L ⊆ insert x S) (ha : ∀ y ∈ L, G.Adj c y)
    (hx : x ∈ insert c L) : s ∈ insert c L := by
  by_contra hs
  apply hcert.2
  refine ⟨c,L,hL,hc,?_,ha,hx⟩
  intro y hy
  rcases Finset.mem_insert.mp (hsub hy) with he | he
  · exact Finset.mem_insert.mpr (Or.inl he)
  · exact Finset.mem_insert.mpr (Or.inr
      (Finset.mem_erase.mpr ⟨by intro e; subst y; exact hs hy, he⟩))

private theorem contradict_certificate (S : Finset V) (s t x : V)
    (hs : s ∈ S) (hst : s ≠ t) (hd : 2 ≤ (S.filter (G.Adj s)).card)
    (hxs : G.Adj x s) (hcert : Certificate G S t x) : False := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
    1 < (S.filter (G.Adj s)).card)
  have hy : ∃ y ∈ S, G.Adj s y ∧ y ≠ t := by
    by_cases hat : a = t
    · exact ⟨b,(Finset.mem_filter.mp hb).1,(Finset.mem_filter.mp hb).2,
        by intro hbt; exact hab (hat.trans hbt.symm)⟩
    · exact ⟨a,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp ha).2,hat⟩
  obtain ⟨y,hy,hsy,hyt⟩ := hy
  have hxy : x ≠ y := fun e => hcert.1 (e ▸ hy)
  have hsx : s ≠ x := G.ne_of_adj (G.adj_symm hxs)
  have hsyn : s ≠ y := G.ne_of_adj hsy
  apply hcert.2
  refine ⟨s,{x,y},by simp [hxy],by simp [hsx,hsyn],?_,?_,by simp⟩
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl | rfl
    · exact Or.inr (Finset.mem_erase.mpr ⟨hst,hs⟩)
    · exact Or.inl rfl
    · exact Or.inr (Finset.mem_erase.mpr ⟨hyt,hy⟩)
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact G.adj_symm hxs
    · exact hsy

/-- The same outside vertex cannot certify two distinct high vertices. -/
theorem certificate_unique (S : Finset V) (hS : IsStarForming G 2 S)
    (s t x : V) (hs : s ∈ high G S) (ht : t ∈ high G S)
    (hcs : Certificate G S s x) (hct : Certificate G S t x) : s = t := by
  by_contra hst
  rcases Finset.mem_filter.mp hs with ⟨hs, hds⟩
  rcases Finset.mem_filter.mp ht with ⟨ht, hdt⟩
  obtain ⟨c,L,hL,hc,hsub,ha,hx⟩ := hS x hcs.1
  have hsm := certificate_forces_mem G S s x c L hcs hL hc hsub ha hx
  have htm := certificate_forces_mem G S t x c L hct hL hc hsub ha hx
  have heq : insert c L = {x,s,t} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    · have hxs : x ≠ s := fun e => hcs.1 (e ▸ hs)
      have hxt : x ≠ t := fun e => hcs.1 (e ▸ ht)
      simp [Finset.card_insert_of_notMem hc,hL,hxs,hxt,hst]
  have hxadj : ∃ y ∈ insert c L, G.Adj x y := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega : 0 < L.card)
      exact ⟨y,Finset.mem_insert_of_mem hy,ha y hy⟩
    · exact ⟨c,by simp,G.adj_symm (ha x hx)⟩
  obtain ⟨y,hy,hxy⟩ := hxadj
  rw [heq] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with hy | hy | hy
  · subst y; exact G.irrefl hxy
  · subst y; exact contradict_certificate G S s t x hs hst hds hxy hct
  · subst y; exact contradict_certificate G S t s x ht (Ne.symm hst) hdt hxy hcs

/-- Certificate sets of distinct high vertices are disjoint. -/
theorem certificates_disjoint (S : Finset V) (hS : IsStarForming G 2 S)
    (s t : V) (hs : s ∈ high G S) (ht : t ∈ high G S) (hst : s ≠ t) :
    Disjoint {x | Certificate G S s x} {x | Certificate G S t x} := by
  apply Set.disjoint_left.mpr
  intro x hxs hxt
  exact hst (certificate_unique G S hS s t x hs ht hxs hxt)

/-- Choosing certificates yields an actual injection into the complement. -/
theorem certificate_injection (S : Finset V) (hS : IsMinimalStarForming G 2 S) :
    ∃ f : ↥(high G S) → ↥(Finset.univ \ S), Function.Injective f := by
  classical
  choose f hf using fun s : ↥(high G S) => certificate_exists G S hS s s.property
  refine ⟨fun s => ⟨f s,by simp [(hf s).1]⟩, ?_⟩
  intro s t he
  apply Subtype.ext
  have he' : f s = f t := congrArg Subtype.val he
  by_contra hne
  have hd := certificates_disjoint G S hS.1 s t s.property t.property hne
  exact (Set.disjoint_left.mp hd) (hf s) (he'.symm ▸ hf t)

/-- At most one high vertex can be assigned to each outside vertex. -/
theorem high_card_le (S : Finset V) (hS : IsMinimalStarForming G 2 S) :
    (high G S).card ≤ (Finset.univ \ S).card := by
  obtain ⟨f,hf⟩ := certificate_injection G S hS
  exact Finset.card_le_card_of_injective hf

/-- Removing the high vertices leaves a genuine dissociation set. -/
theorem low_independent (S : Finset V) : IsKIndependent G 2 (S \ high G S) := by
  intro v hv
  rcases Finset.mem_sdiff.mp hv with ⟨hv, hnot⟩
  have hd : (S.filter (G.Adj v)).card < 2 := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hv,by omega⟩)
  exact lt_of_le_of_lt (Finset.card_le_card
    (Finset.filter_subset_filter _ Finset.sdiff_subset)) hd

/-- The elementary global inequality, without any graph-class assumptions. -/
theorem minimal_card_bound (S : Finset V) (hS : IsMinimalStarForming G 2 S) :
    2 * S.card ≤ Fintype.card V + beta G 2 := by
  have hh := high_card_le G S hS
  have hi : (S \ high G S).card ≤ beta G 2 :=
    Finset.le_sup (by simp [beta,low_independent G S])
  have he := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset
    (fun s => 2 ≤ (S.filter (G.Adj s)).card) S)
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ] at hc
  change (S \ high G S).card + (high G S).card = S.card at he
  omega

/-- Natural division is the required floor, including empty graphs and sets. -/
theorem minimal_card_le_floor (S : Finset V) (hS : IsMinimalStarForming G 2 S) :
    S.card ≤ (Fintype.card V + beta G 2) / 2 := by
  have h := minimal_card_bound G S hS
  omega

/-- The same bound holds for the maximum over all inclusion-minimal sets. -/
theorem sf_le_floor : SF G 2 ≤ (Fintype.card V + beta G 2) / 2 := by
  classical
  apply Finset.sup_le
  intro S hS
  exact minimal_card_le_floor G S (Finset.mem_filter.mp hS).2

end D5.S3.Combinatorics.Graph.StarForming.CertificateBound
