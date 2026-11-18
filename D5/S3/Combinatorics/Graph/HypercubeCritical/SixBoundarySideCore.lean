/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Private auxiliary graph extracted from the actual six-boundary incidences. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCounting
import D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure

/-! Ordinary left vertices label the edges between their two degree-three right
neighbors. Girth supplies edge uniqueness and forbids triangles. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap

open scoped BigOperators Classical
open SimpleGraph GirthSliceCounting
attribute [local instance] Classical.propDecidable
open private core middle_unique two_neighbor_table from
  D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure
open private three_walk_endpoint_injective one_three_cross_impossible from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private def edgeLabels (G : SimpleGraph V) (L : Finset V) : Finset V :=
  L.filter fun x => (degreeThree G (G.neighborFinset x)).card = 2

private def sideCore (G : SimpleGraph V) (L R : Finset V) :
    SimpleGraph (degreeThree G R : Set V) :=
  core G (degreeThree G R) (edgeLabels G L)

private theorem high_neighbor_mem
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V)) {e y : V}
    (he : e ∈ L) (hy : y ∈ degreeThree G (G.neighborFinset e)) :
    y ∈ degreeThree G R := by
  obtain ⟨hy, h3⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_filter.mpr
    ⟨hb.mem_of_mem_adj he ((G.mem_neighborFinset _ _).mp hy), h3⟩

private theorem high_core_other
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (x : (degreeThree G R : Set V)) {e : V}
    (he : e ∈ edgeLabels G L) (hxe : G.Adj x.val e) :
    ∃ y : (degreeThree G R : Set V), y ≠ x ∧ G.Adj y.val e ∧
      degreeThree G (G.neighborFinset e) = {x.val, y.val} := by
  have heL := (Finset.mem_filter.mp he).1
  have he2 := (Finset.mem_filter.mp he).2
  have hx : x.val ∈ degreeThree G (G.neighborFinset e) :=
    Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxe.symm,
      (Finset.mem_filter.mp x.property).2⟩
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (by omega :
    1 < (degreeThree G (G.neighborFinset e)).card) x.val
  refine ⟨⟨y, high_neighbor_mem hb heL hy⟩, ?_,
    ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hy).1).symm, ?_⟩
  · exact fun h => hyx (congrArg Subtype.val h)
  · apply (Finset.eq_of_subset_of_card_le
      (show ({x.val, y} : Finset V) ⊆ degreeThree G (G.neighborFinset e) from by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hx, hy⟩) ?_).symm
    simp [he2, hyx.symm]

private theorem high_core_third
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    {x y z : (degreeThree G R : Set V)} {e : V}
    (he : e ∈ edgeLabels G L) (hxy : x ≠ y)
    (hxe : G.Adj x.val e) (hye : G.Adj y.val e) (hze : G.Adj z.val e) :
    z = x ∨ z = y := by
  have hx : x.val ∈ degreeThree G (G.neighborFinset e) :=
    Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxe.symm,
      (Finset.mem_filter.mp x.property).2⟩
  have hy : y.val ∈ degreeThree G (G.neighborFinset e) :=
    Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hye.symm,
      (Finset.mem_filter.mp y.property).2⟩
  have hz : z.val ∈ degreeThree G (G.neighborFinset e) :=
    Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hze.symm,
      (Finset.mem_filter.mp z.property).2⟩
  have hn : degreeThree G (G.neighborFinset e) = {x.val, y.val} := by
    apply (Finset.eq_of_subset_of_card_le (by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hx, hy⟩) ?_).symm
    have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    simp [hxy', (Finset.mem_filter.mp he).2]
  rw [hn] at hz
  simpa only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] using hz

private theorem side_core_triangle_free
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) :
    ∀ x y z, (sideCore G L R).Adj x y → (sideCore G L R).Adj y z →
      (sideCore G L R).Adj z x → False := by
  intro x y z hxy hyz hzx
  obtain ⟨hxy, a, ha, hxa, hya⟩ := hxy
  obtain ⟨hyz, b, hb', hyb, hzb⟩ := hyz
  obtain ⟨hzx, c, hc, hzc, hxc⟩ := hzx
  have hab : a ≠ b := by
    intro he
    rcases high_core_third hb ha hxy hxa hya (he ▸ hzb) with h | h
    · exact hzx h
    · exact hyz h.symm
  have hcb : c ≠ b := by
    intro he
    rcases high_core_third hb hc hzx hzc hxc (he ▸ hyb) with h | h
    · exact hyz h
    · exact hxy h.symm
  have hac : a ≠ c := by
    intro he
    rcases high_core_third hb ha hxy hxa hya (he ▸ hzc) with h | h
    · exact hzx h
    · exact hyz h.symm
  have he := three_walk_endpoint_injective hb.symm hg
    (Finset.mem_filter.mp x.property).1 (Finset.mem_filter.mp x.property).1
    hxa hya.symm hyb hxc hzc.symm hzb
    (fun h => hxy (Subtype.ext h)) hab (fun h => hzx (Subtype.ext h).symm) hcb ⟨rfl, rfl⟩
  exact hac he.2.1

private theorem side_core_degree
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (x : (degreeThree G R : Set V)) :
    (sideCore G L R).degree x =
      ((G.neighborFinset x.val).filter (fun e => e ∈ edgeLabels G L)).card := by
  let E := (G.neighborFinset x.val).filter (fun e => e ∈ edgeLabels G L)
  have ho (e : V) (he : e ∈ E) := high_core_other hb x
    (Finset.mem_filter.mp he).2 ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp he).1)
  have hcard : E.card = ((sideCore G L R).neighborFinset x).card := by
    apply Finset.card_bij (fun e he => Classical.choose (ho e he))
    · intro e he
      have hy := Classical.choose_spec (ho e he)
      apply ((sideCore G L R).mem_neighborFinset _ _).mpr
      exact ⟨hy.1.symm, e, (Finset.mem_filter.mp he).2,
        (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp he).1, hy.2.1⟩
    · intro e he f hf hef
      have hy := Classical.choose_spec (ho e he)
      have hz := Classical.choose_spec (ho f hf)
      have hyf : G.Adj (Classical.choose (ho e he)).val f := by
        simpa only [hef] using hz.2.1
      exact middle_unique hb.symm hg (Finset.mem_filter.mp x.property).1
        (fun h => hy.1 (Subtype.ext h).symm)
        ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp he).1) hy.2.1
        ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hf).1) hyf
    · intro y hy
      obtain ⟨hxy, e, he, hxe, hye⟩ :=
        ((sideCore G L R).mem_neighborFinset _ _).mp hy
      have heE : e ∈ E := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxe, he⟩
      have hz := Classical.choose_spec (ho e heE)
      have hym : y.val ∈ degreeThree G (G.neighborFinset e) :=
        Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hye.symm,
          (Finset.mem_filter.mp y.property).2⟩
      rw [hz.2.2] at hym
      rcases Finset.mem_insert.mp hym with h | h
      · exact (hxy (Subtype.ext h).symm).elim
      · exact ⟨e, heE, (Subtype.ext (Finset.mem_singleton.mp h)).symm⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hcard]

private theorem low_partner
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hd : ∀ x ∈ L, G.degree x = 3)
    (hr : ∀ y ∈ R, G.degree y = 2 ∨ G.degree y = 3)
    {e : V} (he : e ∈ edgeLabels G L) :
    ∃ m ∈ degreeTwo G R, ∃ f ∈ L, f ≠ e ∧
      G.Adj e m ∧ G.Adj f m ∧ G.neighborFinset m = {e, f} := by
  have heL := (Finset.mem_filter.mp he).1
  have he2 := (Finset.mem_filter.mp he).2
  have he3 := hd e heL
  obtain ⟨m, hm, hmnot⟩ : ∃ m ∈ G.neighborFinset e,
      m ∉ degreeThree G (G.neighborFinset e) := by
    by_contra h
    push_neg at h
    have hh := Finset.card_le_card h
    rw [SimpleGraph.card_neighborFinset_eq_degree, he3, he2] at hh
    omega
  have hem := (G.mem_neighborFinset _ _).mp hm
  have hmR := hb.mem_of_mem_adj heL hem
  have hm3 : G.degree m ≠ 3 := fun h => hmnot (Finset.mem_filter.mpr ⟨hm, h⟩)
  have hm2 : G.degree m = 2 := (hr m hmR).resolve_right hm3
  obtain ⟨f, hfe, hfm, hN⟩ := two_neighbor_table hm2 hem
  exact ⟨m, Finset.mem_filter.mpr ⟨hmR, hm2⟩, f,
    hb.mem_of_mem_adj' hmR hfm, hfe, hem, hfm, hN⟩

private theorem partner_no_shared_high
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {e f m : V}
    (he : e ∈ L) (hef : e ≠ f) (hm2 : G.degree m = 2)
    (hem : G.Adj e m) (hfm : G.Adj f m)
    (x : (degreeThree G R : Set V)) (hxe : G.Adj x.val e)
    (hxf : G.Adj x.val f) : False := by
  have hmx : m ≠ x.val := by
    have hx3 := (Finset.mem_filter.mp x.property).2
    intro h; rw [h] at hm2; omega
  exact one_three_cross_impossible hb hg he he hxe.symm
    hem hfm.symm hxf.symm hef hmx ⟨rfl, rfl⟩

private theorem partner_no_cross_edge
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {e f m : V}
    (he : e ∈ L) (hef : e ≠ f) (hm2 : G.degree m = 2)
    (hem : G.Adj e m) (hfm : G.Adj f m)
    (x y : (degreeThree G R : Set V))
    (hxe : G.Adj x.val e) (hyf : G.Adj y.val f) :
    ¬ (sideCore G L R).Adj x y := by
  rintro ⟨hxy, t, ht, hxt, hyt⟩
  have het : e ≠ t := by
    intro h
    exact partner_no_shared_high hb hg he hef hm2 hem hfm y (h ▸ hyt) hyf
  have hmy : m ≠ y.val := by
    have hy3 := (Finset.mem_filter.mp y.property).2
    intro h; rw [h] at hm2; omega
  have hmx : m ≠ x.val := by
    have hx3 := (Finset.mem_filter.mp x.property).2
    intro h; rw [h] at hm2; omega
  have hh := three_walk_endpoint_injective hb hg he he
    hxe.symm hxt hyt.symm hem hfm.symm hyf.symm
    het (fun h => hxy (Subtype.ext h)) hef hmy ⟨rfl, rfl⟩
  exact hmx hh.2.1.symm

private theorem twelve_core_data
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hleft : ∀ x ∈ L, (degreeThree G (G.neighborFinset x)).card = 2) :
    edgeLabels G L = L ∧ ∀ x, (sideCore G L R).degree x = 3 := by
  have hE : edgeLabels G L = L := Finset.filter_eq_self.mpr hleft
  refine ⟨hE, ?_⟩
  intro x
  rw [side_core_degree hb hg]
  have hn : ((G.neighborFinset x.val).filter fun e => e ∈ edgeLabels G L) =
      G.neighborFinset x.val := by
    apply Finset.filter_eq_self.mpr
    intro e he
    rw [hE]
    exact hb.mem_of_mem_adj' (Finset.mem_filter.mp x.property).1
      ((G.mem_neighborFinset _ _).mp he).symm
  rw [hn, SimpleGraph.card_neighborFinset_eq_degree]
  exact (Finset.mem_filter.mp x.property).2

private theorem side_core_partner
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {e f m : V} (he : e ∈ edgeLabels G L) (hfE : f ∈ edgeLabels G L)
    (hfe : f ≠ e) (hm : G.degree m = 2)
    (hem : G.Adj e m) (hfm : G.Adj f m)
    (x y : (degreeThree G R : Set V)) (hxe : G.Adj x.val e) (hye : G.Adj y.val e) :
    ∃ a b, (sideCore G L R).Adj a b ∧
      (∀ s ∈ ({x, y} : Finset _), ∀ t ∈ ({a, b} : Finset _),
        s ≠ t ∧ ¬ (sideCore G L R).Adj s t) := by
  have hf := (Finset.mem_filter.mp hfE).1
  have hfc := (Finset.mem_filter.mp hfE).2
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hfc
  have ha : a ∈ degreeThree G (G.neighborFinset f) := by rw [hN]; simp
  have hb' : b ∈ degreeThree G (G.neighborFinset f) := by rw [hN]; simp
  let a' : (degreeThree G R : Set V) := ⟨a, high_neighbor_mem hb hf ha⟩
  let b' : (degreeThree G R : Set V) := ⟨b, high_neighbor_mem hb hf hb'⟩
  have haf : G.Adj a'.val f :=
    ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp ha).1).symm
  have hbf : G.Adj b'.val f :=
    ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hb').1).symm
  refine ⟨a', b', ⟨fun h => hab (congrArg Subtype.val h), f, hfE, haf, hbf⟩, ?_⟩
  intro s hs t ht
  have hse : G.Adj s.val e := by
    rcases Finset.mem_insert.mp hs with h | h
    · simpa only [h] using hxe
    · simpa only [Finset.mem_singleton.mp h] using hye
  have htf : G.Adj t.val f := by
    rcases Finset.mem_insert.mp ht with h | h
    · simpa only [h] using haf
    · simpa only [Finset.mem_singleton.mp h] using hbf
  refine ⟨?_, partner_no_cross_edge hb hg (Finset.mem_filter.mp he).1
    hfe.symm hm hem hfm s t hse htf⟩
  intro hst
  exact partner_no_shared_high hb hg (Finset.mem_filter.mp he).1
    hfe.symm hm hem hfm s hse (hst ▸ htf)

private theorem twelve_core_partners
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hd : ∀ x ∈ L, G.degree x = 3)
    (hr : ∀ y ∈ R, G.degree y = 2 ∨ G.degree y = 3)
    (hleft : ∀ x ∈ L, (degreeThree G (G.neighborFinset x)).card = 2) :
    ∀ x y, (sideCore G L R).Adj x y →
      ∃ a b, (sideCore G L R).Adj a b ∧
        (∀ s ∈ ({x, y} : Finset _), ∀ t ∈ ({a, b} : Finset _),
          s ≠ t ∧ ¬ (sideCore G L R).Adj s t) := by
  intro x y hxy
  obtain ⟨hxy, e, he, hxe, hye⟩ := hxy
  obtain ⟨m, hm, f, hf, hfe, hem, hfm, _⟩ := low_partner hb hd hr he
  exact side_core_partner hb hg he (Finset.mem_filter.mpr ⟨hf, hleft f hf⟩)
    hfe (Finset.mem_filter.mp hm).2 hem hfm x y hxe hye

private theorem eleven_core_data
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {r : V} (hr : r ∈ L) (hr1 : (degreeThree G (G.neighborFinset r)).card = 1)
    (hleft : ∀ x ∈ L, x ≠ r → (degreeThree G (G.neighborFinset x)).card = 2) :
    ∃ v : (degreeThree G R : Set V), G.Adj v.val r ∧
      (∀ x : (degreeThree G R : Set V), G.Adj x.val r → x = v) ∧
      (sideCore G L R).degree v = 2 ∧
      ∀ x, x ≠ v → (sideCore G L R).degree x = 3 := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hr1
  have hvhigh : v ∈ degreeThree G (G.neighborFinset r) := by rw [hv]; simp
  let v' : (degreeThree G R : Set V) := ⟨v, high_neighbor_mem hb hr hvhigh⟩
  have hvr : G.Adj v'.val r :=
    ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hvhigh).1).symm
  have huniq (x : (degreeThree G R : Set V)) (hxr : G.Adj x.val r) : x = v' := by
    have hx : x.val ∈ degreeThree G (G.neighborFinset r) :=
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxr.symm,
        (Finset.mem_filter.mp x.property).2⟩
    rw [hv] at hx
    exact Subtype.ext (Finset.mem_singleton.mp hx)
  have hE : edgeLabels G L = L.erase r := by
    ext e
    simp only [edgeLabels, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨he, he2⟩
      exact ⟨fun h => by subst e; omega, he⟩
    · rintro ⟨her, he⟩
      exact ⟨he, hleft e he her⟩
  have hdegree (x : (degreeThree G R : Set V)) :
      (sideCore G L R).degree x = ((G.neighborFinset x.val).erase r).card := by
    rw [side_core_degree hb hg]
    congr 1
    ext e
    simp only [hE, Finset.mem_filter, Finset.mem_erase]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · rintro ⟨her, he⟩
      exact ⟨he, her, hb.mem_of_mem_adj' (Finset.mem_filter.mp x.property).1
        ((G.mem_neighborFinset _ _).mp he).symm⟩
  refine ⟨v', hvr, huniq, ?_, ?_⟩
  · rw [hdegree, Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hvr),
      SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp v'.property).2]
  · intro x hx
    have hrnot : r ∉ G.neighborFinset x.val :=
      fun h => hx (huniq x ((G.mem_neighborFinset _ _).mp h))
    rw [hdegree, Finset.erase_eq_of_notMem hrnot, SimpleGraph.card_neighborFinset_eq_degree]
    exact (Finset.mem_filter.mp x.property).2

end D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap
