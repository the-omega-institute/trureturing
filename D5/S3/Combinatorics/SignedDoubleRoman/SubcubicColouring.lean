/- GID: D5/S3/Combinatorics/SignedDoubleRoman/SubcubicColouring
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/SubcubicColouring
   mirror-E: none(waiver:direct-colouring-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Greedy three-colouring rooted at a deficient vertex or a precoloured pair. -/

import D5.S3.Combinatorics.SignedDoubleRoman.CubicDefs
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.SubcubicColouring

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Reverse greedy colouring with an independent set assigned the fixed colour zero. -/
theorem colour_with_fixed_independent (A S : Finset V)
    (hA : G.IsIndepSet (A : Set V)) (hdisj : Disjoint A S)
    (helim : ∀ T ⊆ S, T.Nonempty → ∃ v ∈ T,
      (G.neighborFinset v ∩ T).card +
        (if ∃ a ∈ A, G.Adj v a then 1 else 0) < 3) :
    ∃ f : V → Fin 3, (∀ a ∈ A, f a = 0) ∧
      ∀ u ∈ S ∪ A, ∀ v ∈ S ∪ A, G.Adj u v → f u ≠ f v := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨v, hv, hbound⟩ := helim S subset_rfl hS
      have hvA : v ∉ A := fun hvA => Finset.disjoint_left.mp hdisj hvA hv
      obtain ⟨f, hfA, hf⟩ := ih (S.erase v) (Finset.erase_ssubset hv)
        (hdisj.mono_right (Finset.erase_subset _ _))
        (fun T hT hTne => helim T (hT.trans (Finset.erase_subset _ _)) hTne)
      let B : Finset (Fin 3) := ((G.neighborFinset v ∩ S.erase v).image f) ∪
        (if ∃ a ∈ A, G.Adj v a then {0} else ∅)
      have hB : B.card < 3 := by
        have h₁ := Finset.card_union_le
          ((G.neighborFinset v ∩ S.erase v).image f)
          (if ∃ a ∈ A, G.Adj v a then {0} else ∅)
        have h₂ := Finset.card_image_le (s := G.neighborFinset v ∩ S.erase v) (f := f)
        have h₃ := Finset.card_le_card
          (Finset.inter_subset_inter_left (s := G.neighborFinset v)
            (Finset.erase_subset v S))
        dsimp [B]
        split_ifs at * <;> simp only [card_singleton, card_empty] at * <;> omega
      obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (show B.card < (Finset.univ : Finset (Fin 3)).card by simpa using hB)
      have hcF : ∀ w ∈ S.erase v, G.Adj v w → c ≠ f w := by
        intro w hw hadj heq
        apply hc
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        exact ⟨w, Finset.mem_inter.mpr ⟨by simpa using hadj, hw⟩, heq.symm⟩
      have hcA : ∀ a ∈ A, G.Adj v a → c ≠ 0 := by
        intro a ha hadj hc0
        apply hc
        apply Finset.mem_union_right
        simp [show ∃ a ∈ A, G.Adj v a from ⟨a, ha, hadj⟩, hc0]
      refine ⟨Function.update f v c, ?_, ?_⟩
      · intro a ha
        rw [Function.update_of_ne (show a ≠ v from fun h => hvA (h ▸ ha))]
        exact hfA a ha
      · intro u hu w hw hadj
        by_cases huv : u = v
        · subst u
          rw [Function.update_self,
            Function.update_of_ne (show w ≠ v from (G.ne_of_adj hadj).symm)]
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hcF w (Finset.mem_erase.mpr ⟨(G.ne_of_adj hadj).symm, hw⟩) hadj
          · rw [hfA w hw]
            exact hcA w hw hadj
        · by_cases hwv : w = v
          · subst w
            rw [Function.update_of_ne huv, Function.update_self]
            rcases Finset.mem_union.mp hu with hu | hu
            · exact (hcF u (Finset.mem_erase.mpr ⟨huv, hu⟩) hadj.symm).symm
            · rw [hfA u hu]
              exact (hcA u hu hadj.symm).symm
          · rw [Function.update_of_ne huv, Function.update_of_ne hwv]
            apply hf u _ w _ hadj
            · rcases Finset.mem_union.mp hu with hu | hu
              · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨huv, hu⟩)
              · exact Finset.mem_union_right _ hu
            · rcases Finset.mem_union.mp hw with hw | hw
              · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwv, hw⟩)
              · exact Finset.mem_union_right _ hw
    · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      refine ⟨fun _ => 0, by simp, ?_⟩
      intro u hu v hv hadj
      have hne := G.ne_of_adj hadj
      exact False.elim (hA (by simpa using hu) (by simpa using hv) hne hadj)

/-- A walk leaving a vertex set supplies an edge crossing its boundary. -/
theorem reachable_boundary (T : Finset V) {u v : V} (h : G.Reachable u v)
    (hu : u ∈ T) (hv : v ∉ T) :
    ∃ x ∈ T, ∃ y ∉ T, G.Adj x y := by
  obtain ⟨p⟩ := h
  obtain ⟨d, _, hdT, hdout⟩ := p.exists_boundary_dart (T : Set V) hu hv
  exact ⟨d.fst, hdT, d.snd, hdout, d.adj⟩

/-- A connected subcubic graph with a deficient vertex admits a reverse greedy colouring. -/
theorem colorable_of_preconnected_deficient (hconn : G.Preconnected)
    (hdeg : ∀ v, (G.neighborFinset v).card ≤ 3)
    (r : V) (hr : (G.neighborFinset r).card ≤ 2) : G.Colorable 3 := by
  classical
  have he : ∀ T ⊆ (Finset.univ : Finset V), T.Nonempty → ∃ v ∈ T,
      (G.neighborFinset v ∩ T).card +
        (if ∃ a ∈ (∅ : Finset V), G.Adj v a then 1 else 0) < 3 := by
    intro T hT hTne
    by_cases hrT : r ∈ T
    · refine ⟨r, hrT, ?_⟩
      have hcard := Finset.card_le_card
        (Finset.inter_subset_left : G.neighborFinset r ∩ T ⊆ G.neighborFinset r)
      simp only [Finset.notMem_empty, false_and, exists_false, ↓reduceIte]
      omega
    · obtain ⟨u, hu⟩ := hTne
      obtain ⟨x, hx, y, hy, hxy⟩ := reachable_boundary G T (hconn u r) hu hrT
      refine ⟨x, hx, ?_⟩
      have hproper : G.neighborFinset x ∩ T ⊂ G.neighborFinset x := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
        intro heq
        have hyN : y ∈ G.neighborFinset x := by simpa using hxy
        have hyI : y ∈ G.neighborFinset x ∩ T := heq.symm ▸ hyN
        exact hy (Finset.mem_inter.mp hyI).2
      have hcard := Finset.card_lt_card hproper
      simp only [Finset.notMem_empty, false_and, exists_false, ↓reduceIte]
      have := hdeg x
      omega
  obtain ⟨f, _, hf⟩ := colour_with_fixed_independent G ∅ Finset.univ
    (by simp) (by simp) he
  exact ⟨SimpleGraph.Coloring.mk f (fun {u v} h => hf u (by simp) v (by simp) h)⟩

/-- A boundary edge leaves at most two forbidden colours, counting a fixed colour once. -/
theorem boundary_forbidden_card (A T : Finset V) (v y : V)
    (hdeg : (G.neighborFinset v).card ≤ 3) (hdisj : Disjoint A T)
    (hvy : G.Adj v y) (hyT : y ∉ T) (hyA : y ∉ A) :
    (G.neighborFinset v ∩ T).card +
      (if ∃ a ∈ A, G.Adj v a then 1 else 0) < 3 := by
  classical
  have hyN : y ∈ G.neighborFinset v := by simpa using hvy
  have hyI : y ∉ G.neighborFinset v ∩ T := by simp [hyT]
  split_ifs with ha
  · obtain ⟨a, haA, hva⟩ := ha
    have haN : a ∈ G.neighborFinset v := by simpa using hva
    have haT : a ∉ T := fun haT => Finset.disjoint_left.mp hdisj haA haT
    have hay : a ≠ y := fun h => hyA (h ▸ haA)
    have haI : a ∉ insert y (G.neighborFinset v ∩ T) := by simp [hay, haT]
    have hsub : insert a (insert y (G.neighborFinset v ∩ T)) ⊆
        G.neighborFinset v := by
      intro z hz
      simp only [mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact haN
      · exact hyN
      · exact (Finset.mem_inter.mp hz).1
    have hh := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem haI, Finset.card_insert_of_notMem hyI] at hh
    omega
  · have hsub : insert y (G.neighborFinset v ∩ T) ⊆ G.neighborFinset v := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hyN
      · exact (Finset.mem_inter.mp hz).1
    have hh := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hyI] at hh
    omega

/-- Nonadjacent neighbours of a root may receive colour zero when their deletion is connected. -/
theorem colorable_of_preconnected_pair (hdeg : ∀ v, (G.neighborFinset v).card ≤ 3)
    (r a b : V) (hab : a ≠ b) (hnab : ¬G.Adj a b)
    (hra : G.Adj r a) (hrb : G.Adj r b)
    (hconn : (G.induce ({a, b} : Set V)ᶜ).Preconnected) : G.Colorable 3 := by
  classical
  let A : Finset V := {a, b}
  let S : Finset V := Finset.univ \ A
  have hrA : r ∉ A := by simp [A, G.ne_of_adj hra, G.ne_of_adj hrb]
  have hrS : r ∈ S := by simp [S, hrA]
  have hAS : Disjoint A S := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvS
    exact (Finset.mem_sdiff.mp hvS).2 hvA
  have hA : G.IsIndepSet (A : Set V) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, A, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact G.irrefl
    · exact hnab
    · exact fun h => hnab h.symm
    · exact G.irrefl
  have hc : (G.induce (S : Set V)).Preconnected := by
    have hset : (S : Set V) = ({a, b} : Set V)ᶜ := by ext v; simp [S, A]
    rw [hset]
    exact hconn
  have he : ∀ T ⊆ S, T.Nonempty → ∃ v ∈ T,
      (G.neighborFinset v ∩ T).card + (if ∃ z ∈ A, G.Adj v z then 1 else 0) < 3 := by
    intro T hT hTne
    have hAT : Disjoint A T := hAS.mono_right hT
    by_cases hrT : r ∈ T
    · refine ⟨r, hrT, ?_⟩
      have haT : a ∉ T := fun haT =>
        Finset.disjoint_left.mp hAT (by simp [A]) haT
      have hbT : b ∉ T := fun hbT =>
        Finset.disjoint_left.mp hAT (by simp [A]) hbT
      have haI : a ∉ insert b (G.neighborFinset r ∩ T) := by simp [hab, haT]
      have hbI : b ∉ G.neighborFinset r ∩ T := by simp [hbT]
      have hsub : insert a (insert b (G.neighborFinset r ∩ T)) ⊆
          G.neighborFinset r := by
        intro z hz
        simp only [mem_insert] at hz
        rcases hz with rfl | rfl | hz
        · simpa using hra
        · simpa using hrb
        · exact (Finset.mem_inter.mp hz).1
      have hh := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem haI, Finset.card_insert_of_notMem hbI] at hh
      have := hdeg r
      simp only [show ∃ z ∈ A, G.Adj r z from ⟨a, by simp [A], hra⟩, ↓reduceIte]
      omega
    · obtain ⟨t, ht⟩ := hTne
      let P : Finset S := Finset.univ.filter fun v => v.val ∈ T
      obtain ⟨x, hx, y, hy, hxy⟩ := reachable_boundary (G.induce (S : Set V)) P
        (hc ⟨t, hT ht⟩ ⟨r, hrS⟩) (by simp [P, ht]) (by simp [P, hrT])
      have hxT : x.val ∈ T := by simpa [P] using hx
      have hyT : y.val ∉ T := by simpa [P] using hy
      have hyA : y.val ∉ A := (Finset.mem_sdiff.mp y.property).2
      exact ⟨x.val, hxT, boundary_forbidden_card G A T x.val y.val
        (hdeg x.val) hAT hxy hyT hyA⟩
  obtain ⟨f, _, hf⟩ := colour_with_fixed_independent G A S hA hAS he
  have hall : ∀ v, v ∈ S ∪ A := by
    intro v
    by_cases hv : v ∈ A <;> simp [S, hv]
  exact ⟨SimpleGraph.Coloring.mk f (fun {u v} h => hf u (hall u) v (hall v) h)⟩

/-- Colourings of pieces meeting only at one vertex combine after aligning its colour. -/
theorem colorable_of_vertex_separation {I : Type*} (r : V) (part : V → I)
    (hedge : ∀ u v, G.Adj u v → u ≠ r → v ≠ r → part u = part v)
    (hpieces : ∀ i, (G.induce {v | v = r ∨ part v = i}).Colorable 3) :
    G.Colorable 3 := by
  classical
  let c (i : I) : (G.induce {v | v = r ∨ part v = i}).Coloring (Fin 3) :=
    (hpieces i).some
  let q (i : I) : {v | v = r ∨ part v = i} := ⟨r, Or.inl rfl⟩
  let d (i : I) := Equiv.swap (c i (q i)) (0 : Fin 3)
  let f (v : V) : Fin 3 := if h : v = r then 0 else d (part v) (c (part v) ⟨v, Or.inr rfl⟩)
  have hfroot : f r = 0 := by simp [f]
  have hfd (i : I) (v : V) (hv : v = r ∨ part v = i) :
      f v = d i (c i ⟨v, hv⟩) := by
    by_cases hvr : v = r
    · subst v
      simp [f, d, q]
    · have hpart : part v = i := hv.resolve_left hvr
      subst i
      simp [f, hvr]
  refine ⟨SimpleGraph.Coloring.mk f ?_⟩
  intro u v huv heq
  by_cases hur : u = r
  · subst u
    have hvi : v = r ∨ part v = part v := Or.inr rfl
    rw [hfd (part v) r (Or.inl rfl), hfd (part v) v hvi] at heq
    exact (c (part v)).valid (v := ⟨r, Or.inl rfl⟩)
      (w := ⟨v, Or.inr rfl⟩) huv ((d (part v)).injective heq)
  · by_cases hvr : v = r
    · subst v
      rw [hfd (part u) u (Or.inr rfl), hfd (part u) r (Or.inl rfl)] at heq
      exact (c (part u)).valid (v := ⟨u, Or.inr rfl⟩)
        (w := ⟨r, Or.inl rfl⟩) huv ((d (part u)).injective heq)
    · have hp : part u = part v := hedge u v huv hur hvr
      rw [hfd (part u) u (Or.inr rfl), hfd (part u) v (Or.inr hp.symm)] at heq
      exact (c (part u)).valid (v := ⟨u, Or.inr rfl⟩)
        (w := ⟨v, Or.inr hp.symm⟩) huv ((d (part u)).injective heq)

/-- Each component left by deleting a root contains a neighbour of the root. -/
theorem component_attaches_to_root (hconn : G.Preconnected) (r : V)
    (c : (G.induce {v | v ≠ r}).ConnectedComponent) :
    ∃ v : {v : V | v ≠ r}, (G.induce {v | v ≠ r}).connectedComponentMk v = c ∧
      G.Adj v.val r := by
  classical
  let H := G.induce {v | v ≠ r}
  let K : Finset V := Finset.univ.filter fun v =>
    ∃ hv : v ≠ r, H.connectedComponentMk ⟨v, hv⟩ = c
  have hout : c.out.val ∈ K := by simp [K]; exact ⟨c.out.property, c.out_eq⟩
  have hrK : r ∉ K := by simp [K]
  obtain ⟨x, hx, y, hy, hxy⟩ := reachable_boundary G K (hconn c.out.val r) hout hrK
  have hxK : ∃ hx : x ≠ r, H.connectedComponentMk ⟨x, hx⟩ = c := by
    simpa [K] using hx
  obtain ⟨hxr, hxc⟩ := hxK
  have hyr : y = r := by
    by_contra hyr
    apply hy
    have he : H.connectedComponentMk ⟨x, hxr⟩ = H.connectedComponentMk ⟨y, hyr⟩ :=
      SimpleGraph.ConnectedComponent.sound
        (show H.Adj ⟨x, hxr⟩ ⟨y, hyr⟩ from hxy).reachable
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hyr, he.symm.trans hxc⟩
  subst y
  exact ⟨⟨x, hxr⟩, hxc, hxy⟩

/-- At a cut vertex, align the greedy colourings of all components with the root. -/
theorem colorable_of_cut_vertex (hconn : G.Preconnected)
    (hdeg : ∀ v, (G.neighborFinset v).card ≤ 3) (r : V)
    (hcut : ¬(G.induce {v | v ≠ r}).Preconnected) : G.Colorable 3 := by
  classical
  let H := G.induce {v | v ≠ r}
  change ¬H.Preconnected at hcut
  have hbad : ∃ p q, ¬H.Reachable p q := by
    by_contra! hh
    exact hcut hh
  obtain ⟨p, q, hpq⟩ := hbad
  have hpqc : H.connectedComponentMk p ≠ H.connectedComponentMk q :=
    fun he => hpq (SimpleGraph.ConnectedComponent.exact he)
  let part (v : V) : H.ConnectedComponent :=
    if hv : v ≠ r then H.connectedComponentMk ⟨v, hv⟩ else H.connectedComponentMk p
  apply colorable_of_vertex_separation G r part
  · intro u v huv hur hvr
    simp only [part, dif_pos hur, dif_pos hvr]
    exact SimpleGraph.ConnectedComponent.sound
      (show H.Adj ⟨u, hur⟩ ⟨v, hvr⟩ from huv).reachable
  · intro c
    let P : Set V := {v | v = r ∨ part v = c}
    obtain ⟨u, huc, hur⟩ := component_attaches_to_root G hconn r c
    have huP : u.val ∈ P := by
      apply Or.inr
      dsimp [part]
      rw [dif_pos (show u.val ≠ r from u.property)]
      exact huc
    let root : P := ⟨r, Or.inl rfl⟩
    let inc : c.toSimpleGraph →g G.induce P :=
      { toFun := fun v => ⟨v.val.val, Or.inr (by
          dsimp [part]
          rw [dif_pos (show v.val.val ≠ r from v.val.property)]
          exact v.property)⟩
        map_rel' := fun h => h }
    have hc : (G.induce P).Preconnected := by
      have hreach : ∀ v : P, (G.induce P).Reachable root v := by
        intro v
        by_cases hvr : v.val = r
        · have hvroot : v = root := Subtype.ext hvr
          subst v
          exact SimpleGraph.Reachable.rfl
        · have hvc : H.connectedComponentMk ⟨v.val, hvr⟩ = c := by
            have hh := v.property.resolve_left hvr
            simpa only [part, dif_pos hvr] using hh
          have hpath := (c.reachable_toSimpleGraph huc hvc).map inc
          have hru : (G.induce P).Adj root (inc ⟨u, huc⟩) := hur.symm
          exact hru.reachable.trans hpath
      intro v w
      exact (hreach v).symm.trans (hreach w)
    have hsmall : ∀ v : P, ((G.induce P).neighborFinset v).card ≤ 3 := by
      intro v
      have hh := Finset.card_le_card
        (Finset.inter_subset_left : G.neighborFinset v.val ∩ P.toFinset ⊆
          G.neighborFinset v.val)
      rw [← G.map_neighborFinset_induce v, Finset.card_map] at hh
      exact hh.trans (hdeg v.val)
    have hother : ∃ j : H.ConnectedComponent, j ≠ c := by
      by_cases hp : H.connectedComponentMk p = c
      · exact ⟨H.connectedComponentMk q, fun hq => hpqc (hp.trans hq.symm)⟩
      · exact ⟨H.connectedComponentMk p, hp⟩
    obtain ⟨j, hj⟩ := hother
    obtain ⟨z, hzj, hzr⟩ := component_attaches_to_root G hconn r j
    have hzP : z.val ∉ P := by
      intro hz
      rcases hz with hz | hz
      · exact z.property hz
      · have hzc : H.connectedComponentMk z = c := by
          simpa only [part, dif_pos (show z.val ≠ r from z.property)] using hz
        exact hj (hzj.symm.trans hzc)
    have hproper : G.neighborFinset r ∩ P.toFinset ⊂ G.neighborFinset r := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
      intro heq
      have hzN : z.val ∈ G.neighborFinset r := by simpa using hzr.symm
      have hzI : z.val ∈ G.neighborFinset r ∩ P.toFinset := heq.symm ▸ hzN
      exact hzP (by simpa using (Finset.mem_inter.mp hzI).2)
    have hrsmall : ((G.induce P).neighborFinset root).card ≤ 2 := by
      have hh := Finset.card_lt_card hproper
      rw [← G.map_neighborFinset_induce root, Finset.card_map] at hh
      have := hdeg r
      omega
    exact colorable_of_preconnected_deficient (G.induce P) hc hsmall root hrsmall

/-- A degree-three vertex outside every four-clique has nonadjacent neighbours. -/
theorem nonadjacent_neighbours (hclique : G.CliqueFree 4) (r : V)
    (hr : (G.neighborFinset r).card = 3) :
    ∃ a b, a ≠ b ∧ G.Adj r a ∧ G.Adj r b ∧ ¬G.Adj a b := by
  classical
  by_contra! h
  have hN : G.IsClique (G.neighborSet r) := by
    intro a ha b hb hab
    exact h a b hab ha hb
  have hK : G.IsClique (insert r (G.neighborSet r)) :=
    hN.insert (fun b hb _ => hb)
  apply hclique (insert r (G.neighborFinset r))
  apply (G.isNClique_iff).mpr
  constructor
  · simpa only [Finset.coe_insert, SimpleGraph.coe_neighborFinset] using hK
  · rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self r), hr]

/-- The case where deleting any pair leaves a connected graph uses the precoloured pair. -/
theorem colorable_of_pair_deletions_preconnected (hconn : G.Preconnected)
    (hdeg : ∀ v, (G.neighborFinset v).card ≤ 3) (hclique : G.CliqueFree 4)
    (hpairs : ∀ a b, a ≠ b → (G.induce ({a, b} : Set V)ᶜ).Preconnected) :
    G.Colorable 3 := by
  classical
  by_cases hdef : ∃ r, (G.neighborFinset r).card ≤ 2
  · obtain ⟨r, hr⟩ := hdef
    exact colorable_of_preconnected_deficient G hconn hdeg r hr
  · by_cases hn : Nonempty V
    · let r : V := hn.some
      have hr : (G.neighborFinset r).card = 3 := by
        have hnot : ¬(G.neighborFinset r).card ≤ 2 := fun h => hdef ⟨r, h⟩
        have := hdeg r
        omega
      obtain ⟨a, b, hab, hra, hrb, hnab⟩ := nonadjacent_neighbours G hclique r hr
      exact colorable_of_preconnected_pair G hdeg r a b hab hnab hra hrb (hpairs a b hab)
    · let : IsEmpty V := not_nonempty_iff.mp hn
      exact SimpleGraph.Colorable.of_isEmpty 3

#print axioms colour_with_fixed_independent
#print axioms colorable_of_preconnected_deficient
#print axioms colorable_of_preconnected_pair
#print axioms colorable_of_vertex_separation
#print axioms colorable_of_cut_vertex
#print axioms colorable_of_pair_deletions_preconnected

end D5.S3.Combinatorics.SignedDoubleRoman.SubcubicColouring
