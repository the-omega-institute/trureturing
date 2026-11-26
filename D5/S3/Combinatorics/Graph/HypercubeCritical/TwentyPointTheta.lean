/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointTheta
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointTheta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: The actual 11/9 twenty-point branch forces its seven-high-vertex theta incidence. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression

/-! The seven-point incidence is derived from actual short paths and degree tables. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta

open SimpleGraph GirthSliceCounting
open private SideHigh compressed compressed_degree compressed_triangle_free
  nine_side_no_high_wedge eleven_nine_central_obstruction from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private neighbor_parts_card three_walk_endpoint_injective
  one_three_cross_impossible from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private two_neighbor_table from
  D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure

attribute [local instance] Classical.propDecidable

private theorem high_neighbors_compressed_separated
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {r : V} (hrL : r ∈ L) (hr3 : G.degree r = 3)
    {x y : SideHigh G R} (hrx : G.Adj r x.val) (hry : G.Adj r y.val)
    (hxy : x ≠ y) :
    ¬ (compressed G R).Adj x y ∧
      ∀ t, (compressed G R).Adj x t → (compressed G R).Adj y t → False := by
  constructor
  · rintro ⟨_, m, hm2, hxm, hym⟩
    have hrm : r ≠ m := by intro he; have h := he ▸ hr3; omega
    exact one_three_cross_impossible hpart hg hrL hrL
      hry hrx hxm hym.symm hrm (fun he => hxy (Subtype.ext he)) ⟨rfl, rfl⟩
  · intro t hxt hyt
    obtain ⟨hxt, m, hm2, hxm, htm⟩ := hxt
    obtain ⟨hyt, k, hk2, hyk, htk⟩ := hyt
    have hrm : r ≠ m := by intro he; have h := he ▸ hr3; omega
    have hrk : r ≠ k := by intro he; have h := he ▸ hr3; omega
    have he := three_walk_endpoint_injective hpart hg hrL hrL
      hrx hxm htm.symm hry hyk htk.symm hrm
      (fun he => hxt (Subtype.ext he)) hrk
      (fun he => hyt (Subtype.ext he)) ⟨rfl, rfl⟩
    exact hxy (Subtype.ext he.2.1)

private theorem high_roots_low_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {u v w a b : V} (huL : u ∈ L) (hwL : w ∈ L)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hab : a ≠ b)
    (hlo : degreeTwo G R = {a, b})
    (hNa : G.neighborFinset a = {u, v})
    (hNb : G.neighborFinset b = {v, w}) :
    degreeTwo G (G.neighborFinset u) = {a} ∧
      degreeTwo G (G.neighborFinset w) = {b} := by
  have hal : G.degree a = 2 := (Finset.mem_filter.mp
    (show a ∈ degreeTwo G R by rw [hlo]; simp)).2
  have hbl : G.degree b = 2 := (Finset.mem_filter.mp
    (show b ∈ degreeTwo G R by rw [hlo]; simp)).2
  have htable (x : V) (hx : x ∈ L) :
      degreeTwo G (G.neighborFinset x) =
        (degreeTwo G R).filter (fun m => x ∈ G.neighborFinset m) := by
    ext m
    simp only [degreeTwo, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hxm, hm⟩
      exact ⟨⟨hpart.mem_of_mem_adj hx hxm, hm⟩, hxm.symm⟩
    · rintro ⟨⟨_, hm⟩, hmx⟩
      exact ⟨hmx.symm, hm⟩
  constructor
  · rw [htable u huL, hlo]
    ext x
    simp only [Finset.mem_filter]
    by_cases hxa : x = a
    · subst x; rw [show u ∈ G.neighborFinset a ↔ u ∈ ({u, v} : Finset V) by rw [hNa]]; simp
    · by_cases hxb : x = b
      · subst x; rw [show u ∈ G.neighborFinset b ↔ u ∈ ({v, w} : Finset V) by rw [hNb]]
        simp [hab.symm, huv, huw]
      · simp [hxa, hxb]
  · rw [htable w hwL, hlo]
    ext x
    simp only [Finset.mem_filter]
    by_cases hxb : x = b
    · subst x; rw [show w ∈ G.neighborFinset b ↔ w ∈ ({v, w} : Finset V) by rw [hNb]]; simp
    · by_cases hxa : x = a
      · subst x; rw [show w ∈ G.neighborFinset a ↔ w ∈ ({u, v} : Finset V) by rw [hNa]]
        simp [hab, huw.symm, hvw.symm]
      · simp [hxa, hxb]

private theorem side_high_neighbors_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {x : V} (hxL : x ∈ L) :
    ((Finset.univ : Finset (SideHigh G R)).filter (fun y => G.Adj x y.val)).card =
      (degreeThree G (G.neighborFinset x)).card := by
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
      (Finset.mem_filter.mp hy).2, (Finset.mem_filter.mp y.property).2⟩
  · intro y _ z _ he; exact Subtype.ext he
  · intro y hy
    have hy0 := Finset.mem_filter.mp hy
    have hxy := (G.mem_neighborFinset _ _).mp hy0.1
    exact ⟨⟨y, Finset.mem_filter.mpr ⟨hpart.mem_of_mem_adj hxL hxy, hy0.2⟩⟩,
      by simpa using hxy, rfl⟩

private theorem eleven_nine_blocks
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL3 : (degreeThree G L).card = 3) (hR2 : (degreeTwo G R).card = 2)
    (hR3 : (degreeThree G R).card = 7) (hR : R.card = 9) :
    ∃ u v w a b : V, ∃ Z P Q : SideHigh G R,
      ∃ U W : Finset (SideHigh G R),
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ a ≠ b ∧
      degreeThree G L = {u, v, w} ∧ degreeTwo G R = {a, b} ∧
      G.neighborFinset a = {u, v} ∧ G.neighborFinset b = {v, w} ∧
      degreeThree G (G.neighborFinset v) = {Z.val} ∧
      U = Finset.univ.filter (fun y => G.Adj u y.val) ∧
      W = Finset.univ.filter (fun y => G.Adj w y.val) ∧
      U.card = 2 ∧ W.card = 2 ∧ Disjoint U W ∧
      Z ∉ U ∧ Z ∉ W ∧ P ≠ Q ∧
      (compressed G R).neighborFinset Z = {P, Q} ∧
      (compressed G R).degree P = 3 ∧ (compressed G R).degree Q = 3 ∧
      (∀ x ∈ U ∪ W, (compressed G R).degree x = 2) ∧
      (∀ x ∈ ({P, Q} : Finset (SideHigh G R)),
        degreeThree G (G.neighborFinset x.val) = ∅) ∧
      Finset.univ = insert Z (U ∪ W) ∪ {P, Q} ∧
      (∀ r ∈ ({u, w} : Finset V),
        ∀ x y : SideHigh G R, G.Adj r x.val → G.Adj r y.val → x ≠ y →
          ¬ (compressed G R).Adj x y ∧
            ∀ t, (compressed G R).Adj x t → (compressed G R).Adj y t → False) := by
  obtain ⟨u, v, w, a, b, Z, huv, huw, hvw, hab, hhi, hlo, hNa, hNb,
    hNv, hZd, hZzero⟩ := eleven_nine_central_obstruction hpart hdeg hlow hg hL3 hR2 hR
  have hm (x : V) (hx : x ∈ ({u, v, w} : Finset V)) : x ∈ L ∧ G.degree x = 3 := by
    have hxhi : x ∈ degreeThree G L := by rw [hhi]; exact hx
    exact Finset.mem_filter.mp hxhi
  have hu := hm u (by simp)
  have hv := hm v (by simp)
  have hw := hm w (by simp)
  obtain ⟨hNu, hNw⟩ := high_roots_low_neighbors hpart hu.1 hw.1
    huv huw hvw hab hlo hNa hNb
  have huc : (degreeThree G (G.neighborFinset u)).card = 2 := by
    have hp := neighbor_parts_card hdeg u
    rw [hNu, Finset.card_singleton, hu.2] at hp
    omega
  have hwc : (degreeThree G (G.neighborFinset w)).card = 2 := by
    have hp := neighbor_parts_card hdeg w
    rw [hNw, Finset.card_singleton, hw.2] at hp
    omega
  let U := (Finset.univ : Finset (SideHigh G R)).filter (fun y => G.Adj u y.val)
  let W := (Finset.univ : Finset (SideHigh G R)).filter (fun y => G.Adj w y.val)
  have hU : U.card = 2 := (side_high_neighbors_card hpart hu.1).trans huc
  have hW : W.card = 2 := (side_high_neighbors_card hpart hw.1).trans hwc
  have hvZ : G.Adj v Z.val := by
    apply (G.mem_neighborFinset _ _).mp
    apply (Finset.mem_filter.mp (show Z.val ∈ degreeThree G (G.neighborFinset v) by
      rw [hNv]; simp)).1
  have hF (r : V) (hrL : r ∈ L) (hr3 : G.degree r = 3)
      (x : SideHigh G R) (hrx : G.Adj r x.val) :
      degreeThree G (G.neighborFinset x.val) = {r} :=
    (nine_side_no_high_wedge hpart hdeg hlow hg hR hrL hr3).2
      x.val hrx (Finset.mem_filter.mp x.property).2
  have hFZ := hF v hv.1 hv.2 Z hvZ
  have hdis : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxW
    have hxu := hF u hu.1 hu.2 x (Finset.mem_filter.mp hxU).2
    have hxw : w ∈ degreeThree G (G.neighborFinset x.val) :=
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        (Finset.mem_filter.mp hxW).2.symm, hw.2⟩
    rw [hxu, Finset.mem_singleton] at hxw
    exact huw hxw.symm
  have hZU : Z ∉ U := by
    intro hz
    have hm : u ∈ degreeThree G (G.neighborFinset Z.val) :=
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        (Finset.mem_filter.mp hz).2.symm, hu.2⟩
    rw [hFZ, Finset.mem_singleton] at hm
    exact huv hm
  have hZW : Z ∉ W := by
    intro hz
    have hm : w ∈ degreeThree G (G.neighborFinset Z.val) :=
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        (Finset.mem_filter.mp hz).2.symm, hw.2⟩
    rw [hFZ, Finset.mem_singleton] at hm
    exact hvw hm.symm
  obtain ⟨P, Q, hPQ, hNZ⟩ := Finset.card_eq_two.mp
    (show ((compressed G R).neighborFinset Z).card = 2 by simpa using hZd)
  have hZP : (compressed G R).Adj Z P := by
    apply ((compressed G R).mem_neighborFinset _ _).mp
    rw [hNZ]; simp
  have hZQ : (compressed G R).Adj Z Q := by
    apply ((compressed G R).mem_neighborFinset _ _).mp
    rw [hNZ]; simp
  have hzero (x : SideHigh G R) (hx : x ∈ ({P, Q} : Finset (SideHigh G R))) :
      degreeThree G (G.neighborFinset x.val) = ∅ := by
    rcases Finset.mem_insert.mp hx with hxp | hx
    · rw [hxp]; exact hZzero P hZP
    · exact Finset.mem_singleton.mp hx ▸ hZzero Q hZQ
  have hzdis : Disjoint (insert Z (U ∪ W)) ({P, Q} : Finset (SideHigh G R)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxO
    have hx0 := hzero x hxO
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rw [hFZ] at hx0
      exact Finset.singleton_ne_empty _ hx0
    · rcases Finset.mem_union.mp hx with hx | hx
      · have h := hF u hu.1 hu.2 x (Finset.mem_filter.mp hx).2
        rw [h] at hx0
        exact Finset.singleton_ne_empty _ hx0
      · have h := hF w hw.1 hw.2 x (Finset.mem_filter.mp hx).2
        rw [h] at hx0
        exact Finset.singleton_ne_empty _ hx0
  have hcover : Finset.univ = insert Z (U ∪ W) ∪ {P, Q} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_union_of_disjoint hzdis,
      Finset.card_insert_of_notMem (by simpa using And.intro hZU hZW),
      Finset.card_union_of_disjoint hdis, hU, hW, Finset.card_pair hPQ]
    have hc : Fintype.card (SideHigh G R) = 7 := by
      simpa only [SideHigh, Fintype.card_coe] using hR3
    simp only [Finset.card_univ, hc]
    norm_num
  have htwo (x : SideHigh G R) (hx : x ∈ U ∪ W) : (compressed G R).degree x = 2 := by
    have hd := compressed_degree hpart.symm hdeg hlow hg x
    rcases Finset.mem_union.mp hx with hx | hx
    · rw [hF u hu.1 hu.2 x (Finset.mem_filter.mp hx).2, Finset.card_singleton] at hd
      omega
    · rw [hF w hw.1 hw.2 x (Finset.mem_filter.mp hx).2, Finset.card_singleton] at hd
      omega
  have hthree (x : SideHigh G R) (hx : x ∈ ({P, Q} : Finset (SideHigh G R))) :
      (compressed G R).degree x = 3 := by
    have hd := compressed_degree hpart.symm hdeg hlow hg x
    rwa [hzero x hx, Finset.card_empty, Nat.add_zero] at hd
  refine ⟨u, v, w, a, b, Z, P, Q, U, W, huv, huw, hvw, hab,
    hhi, hlo, hNa, hNb, hNv, rfl, rfl, hU, hW, hdis, hZU, hZW, hPQ, hNZ,
    hthree P (by simp), hthree Q (by simp), htwo, hzero, hcover, ?_⟩
  intro r hr x y hrx hry hxy
  rcases Finset.mem_insert.mp hr with rfl | hr
  · exact high_neighbors_compressed_separated hpart hg hu.1 hu.2 hrx hry hxy
  · have he := Finset.mem_singleton.mp hr
    subst r
    exact high_neighbors_compressed_separated hpart hg hw.1 hw.2 hrx hry hxy

private theorem split_three_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {U W : Finset V} {x Z : V}
    (hx3 : H.degree x = 3) (hxZ : H.Adj x Z)
    (hcover : ∀ t, H.Adj x t → t = Z ∨ t ∈ U ∨ t ∈ W)
    (hsep : ∀ X ∈ ({U, W} : Finset (Finset V)),
      ∀ a ∈ X, ∀ b ∈ X, a ≠ b →
        ∀ t, H.Adj a t → H.Adj b t → False) :
    ∃ A C, A ∈ U ∧ C ∈ W ∧ H.neighborFinset x = {Z, A, C} := by
  have hZmem := (H.mem_neighborFinset _ _).mpr hxZ
  have hc : ((H.neighborFinset x).erase Z).card = 2 := by
    rw [Finset.card_erase_of_mem hZmem, SimpleGraph.card_neighborFinset_eq_degree, hx3]
  obtain ⟨a, c, hac, hN⟩ := Finset.card_eq_two.mp hc
  have ha : a ∈ (H.neighborFinset x).erase Z := by rw [hN]; simp
  have hc : c ∈ (H.neighborFinset x).erase Z := by rw [hN]; simp
  have hxa := (H.mem_neighborFinset _ _).mp (Finset.mem_erase.mp ha).2
  have hxc := (H.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hc).2
  have haUW : a ∈ U ∨ a ∈ W := (hcover a hxa).resolve_left (Finset.mem_erase.mp ha).1
  have hcUW : c ∈ U ∨ c ∈ W := (hcover c hxc).resolve_left (Finset.mem_erase.mp hc).1
  have hNall : H.neighborFinset x = {Z, a, c} := by
    rw [← Finset.insert_erase hZmem, hN]
  rcases haUW with haU | haW <;> rcases hcUW with hcU | hcW
  · exact (hsep U (by simp) a haU c hcU hac x hxa.symm hxc.symm).elim
  · exact ⟨a, c, haU, hcW, hNall⟩
  · exact ⟨c, a, hcU, haW, by simpa only [Finset.pair_comm a c] using hNall⟩
  · exact (hsep W (by simp) a haW c hcW hac x hxa.symm hxc.symm).elim

private theorem centers_choose_distinct
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {U W : Finset V} {Z P Q A C D B : V}
    (hU2 : U.card = 2) (hW2 : W.card = 2) (hUW : Disjoint U W)
    (hZ : Z ∉ U ∪ W) (hP : P ∉ U ∪ W) (hQ : Q ∉ U ∪ W)
    (hA : A ∈ U) (hC : C ∈ W) (hD : D ∈ U) (hB : B ∈ W)
    (hcover : Finset.univ = insert Z (U ∪ W) ∪ {P, Q})
    (hNZ : H.neighborFinset Z = {P, Q})
    (hNP : H.neighborFinset P = {Z, A, C})
    (hNQ : H.neighborFinset Q = {Z, D, B})
    (hdeg : ∀ x ∈ U ∪ W, H.degree x = 2)
    (hsep : ∀ X ∈ ({U, W} : Finset (Finset V)),
      ∀ a ∈ X, ∀ b ∈ X, a ≠ b →
        ¬ H.Adj a b ∧ ∀ t, H.Adj a t → H.Adj b t → False) : A ≠ D := by
  intro hAD
  obtain ⟨E, hEU, hEA⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) A
  have hEUW : E ∈ U ∪ W := Finset.mem_union_left _ hEU
  have hEZ : E ≠ Z := fun he => hZ (he ▸ hEUW)
  have hEP : E ≠ P := fun he => hP (he ▸ hEUW)
  have hEQ : E ≠ Q := fun he => hQ (he ▸ hEUW)
  have hEC : E ≠ C := fun he => Finset.disjoint_left.mp hUW (he ▸ hEU) hC
  have hEB : E ≠ B := fun he => Finset.disjoint_left.mp hUW (he ▸ hEU) hB
  have hsub : H.neighborFinset E ⊆ W := by
    intro t ht
    have hEt := (H.mem_neighborFinset _ _).mp ht
    have hall : t ∈ insert Z (U ∪ W) ∪ {P, Q} := by rw [← hcover]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hall with ht0 | ht0
    · rcases Finset.mem_insert.mp ht0 with htZ | ht0
      · have he : E ∈ H.neighborFinset Z := (H.mem_neighborFinset _ _).mpr
          (htZ ▸ hEt.symm)
        rw [hNZ] at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        exact (he.elim hEP hEQ).elim
      · rcases Finset.mem_union.mp ht0 with htU | htW
        · exact ((hsep U (by simp) E hEU t htU (H.ne_of_adj hEt)).1 hEt).elim
        · exact htW
    · rcases Finset.mem_insert.mp ht0 with htP | htQ
      · have he : E ∈ H.neighborFinset P := (H.mem_neighborFinset _ _).mpr
          (htP ▸ hEt.symm)
        rw [hNP] at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        exact (he.elim hEZ (fun he => he.elim hEA hEC)).elim
      · have he : t = Q := Finset.mem_singleton.mp htQ
        subst t
        have he : E ∈ H.neighborFinset Q := (H.mem_neighborFinset _ _).mpr hEt.symm
        rw [hNQ, ← hAD] at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        exact (he.elim hEZ (fun he => he.elim hEA hEB)).elim
  have hNE : H.neighborFinset E = W :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [hW2, SimpleGraph.card_neighborFinset_eq_degree, hdeg E hEUW])
  obtain ⟨s, t, hst, hW⟩ := Finset.card_eq_two.mp hW2
  have hs : s ∈ W := by rw [hW]; simp
  have ht : t ∈ W := by rw [hW]; simp
  have hEs : H.Adj E s := (H.mem_neighborFinset _ _).mp (hNE ▸ hs)
  have hEt : H.Adj E t := (H.mem_neighborFinset _ _).mp (hNE ▸ ht)
  exact (hsep W (by simp) s hs t ht hst).2 E hEs.symm hEt.symm

private theorem seven_high_theta
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {U W : Finset V} {Z P Q : V}
    (hU2 : U.card = 2) (hW2 : W.card = 2) (hUW : Disjoint U W)
    (hZ : Z ∉ U ∪ W) (hPQ : P ≠ Q)
    (hcover : Finset.univ = insert Z (U ∪ W) ∪ {P, Q})
    (hNZ : H.neighborFinset Z = {P, Q}) (hP3 : H.degree P = 3) (hQ3 : H.degree Q = 3)
    (hdeg : ∀ x ∈ U ∪ W, H.degree x = 2)
    (htri : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False)
    (hsep : ∀ X ∈ ({U, W} : Finset (Finset V)),
      ∀ a ∈ X, ∀ b ∈ X, a ≠ b →
        ¬ H.Adj a b ∧ ∀ t, H.Adj a t → H.Adj b t → False) :
    ∃ A B C D, U = {A, D} ∧ W = {B, C} ∧
      H.neighborFinset P = {Z, A, C} ∧ H.neighborFinset Q = {Z, B, D} ∧
      H.Adj A B ∧ H.Adj D C := by
  have hP : P ∉ U ∪ W := by intro hm; have h := hdeg P hm; omega
  have hQ : Q ∉ U ∪ W := by intro hm; have h := hdeg Q hm; omega
  have hZ2 : H.degree Z = 2 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hNZ, Finset.card_pair hPQ]
  have hPZ : P ≠ Z := by intro he; have h := he ▸ hP3; omega
  have hQZ : Q ≠ Z := by intro he; have h := he ▸ hQ3; omega
  have hZP : H.Adj Z P := (H.mem_neighborFinset _ _).mp (by rw [hNZ]; simp)
  have hZQ : H.Adj Z Q := (H.mem_neighborFinset _ _).mp (by rw [hNZ]; simp)
  have hnPQ : ¬ H.Adj P Q := fun h => htri Z P Q hZP h hZQ.symm
  have hsmall (x : V) (hx : x = P ∨ x = Q) (t : V) (hxt : H.Adj x t) :
      t = Z ∨ t ∈ U ∨ t ∈ W := by
    have ht : t ∈ insert Z (U ∪ W) ∪ {P, Q} := by rw [← hcover]; exact Finset.mem_univ _
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with (he | hU | hW) | (he | he)
    · exact Or.inl he
    · exact Or.inr (Or.inl hU)
    · exact Or.inr (Or.inr hW)
    · rcases hx with hx | hx
      · exact (H.ne_of_adj hxt (hx.trans he.symm)).elim
      · exact (hnPQ (by simpa only [hx, he] using hxt.symm)).elim
    · rcases hx with hx | hx
      · exact (hnPQ (by simpa only [hx, he] using hxt)).elim
      · exact (H.ne_of_adj hxt (hx.trans he.symm)).elim
  have hsep' : ∀ X ∈ ({U, W} : Finset (Finset V)),
      ∀ a ∈ X, ∀ b ∈ X, a ≠ b → ∀ t, H.Adj a t → H.Adj b t → False := by
    intro X hX a ha b hb hab
    exact (hsep X hX a ha b hb hab).2
  obtain ⟨A, C, hA, hC, hNP⟩ := split_three_neighbors hP3 hZP.symm
    (hsmall P (Or.inl rfl)) hsep'
  obtain ⟨D, B, hD, hB, hNQ⟩ := split_three_neighbors hQ3 hZQ.symm
    (hsmall Q (Or.inr rfl)) hsep'
  have hAD : A ≠ D := centers_choose_distinct hU2 hW2 hUW hZ hP hQ
    hA hC hD hB hcover hNZ hNP hNQ hdeg hsep
  have hCB : C ≠ B := centers_choose_distinct (U := W) (W := U)
    hW2 hU2 hUW.symm (by simpa only [Finset.union_comm] using hZ)
    (by simpa only [Finset.union_comm] using hP)
    (by simpa only [Finset.union_comm] using hQ)
    hC hA hB hD (by simpa only [Finset.union_comm] using hcover) hNZ
    (by simpa only [Finset.pair_comm A C] using hNP)
    (by simpa only [Finset.pair_comm D B] using hNQ)
    (by simpa only [Finset.union_comm] using hdeg)
    (by simpa only [Finset.pair_comm] using hsep)
  have hUs : U = {A, D} := (Finset.eq_of_subset_of_card_le
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hA, hD⟩)
    (by rw [hU2, Finset.card_pair hAD])).symm
  have hWs : W = {B, C} := (Finset.eq_of_subset_of_card_le
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hB, hC⟩)
    (by rw [hW2, Finset.card_pair hCB.symm])).symm
  have hcross (x : V) (hxU : x ∈ U) (y : V) (hyW : y ∈ W) : x ≠ y := by
    intro he
    exact Finset.disjoint_left.mp hUW (he ▸ hxU) hyW
  have hAC := hcross A hA C hC
  have hAB := hcross A hA B hB
  have hDC := hcross D hD C hC
  have hDB := hcross D hD B hB
  have houtside (x : V) (hx : x ∈ U ∪ W) : x ≠ Z ∧ x ≠ P ∧ x ≠ Q :=
    ⟨fun he => hZ (he ▸ hx), fun he => hP (he ▸ hx), fun he => hQ (he ▸ hx)⟩
  have haout := houtside A (Finset.mem_union_left _ hA)
  have hdout := houtside D (Finset.mem_union_left _ hD)
  have force (x y s t p q : V) (hxU : x ∈ U) (hyU : y ∈ U)
      (hsW : s ∈ W) (htW : t ∈ W) (hxy : x ≠ y)
      (hWs' : W = {s, t}) (hNZ' : H.neighborFinset Z = {p, q})
      (hNp : H.neighborFinset p = {Z, x, t})
      (hNq : H.neighborFinset q = {Z, y, s})
      (hcover' : Finset.univ = insert Z (U ∪ W) ∪ {p, q})
      (hxout : x ≠ Z ∧ x ≠ p ∧ x ≠ q) : H.Adj x s := by
    have hxp : H.Adj x p := ((H.mem_neighborFinset _ _).mp (by rw [hNp]; simp)).symm
    have hxt : ¬ H.Adj x t := by
      intro hxt
      have hpt : H.Adj p t := (H.mem_neighborFinset _ _).mp (by rw [hNp]; simp)
      exact htri p x t hxp.symm hxt hpt.symm
    have hxZ : ¬ H.Adj x Z := by
      intro hxZ
      have hm := (H.mem_neighborFinset _ _).mpr hxZ.symm
      rw [hNZ'] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      exact hm.elim hxout.2.1 hxout.2.2
    have hxq : ¬ H.Adj x q := by
      intro hxq
      have hm := (H.mem_neighborFinset _ _).mpr hxq.symm
      rw [hNq] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      exact hm.elim hxout.1 (fun hm => hm.elim hxy (hcross x hxU s hsW))
    have hc : 1 < (H.neighborFinset x).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg x (Finset.mem_union_left _ hxU)]
      norm_num
    obtain ⟨r, hr, hrp⟩ := Finset.exists_mem_ne hc p
    have hxr := (H.mem_neighborFinset _ _).mp hr
    have hall : r ∈ insert Z (U ∪ W) ∪ {p, q} := by rw [← hcover']; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hall with hr0 | hr0
    · rcases Finset.mem_insert.mp hr0 with hrZ | hrUW
      · exact (hxZ (hrZ ▸ hxr)).elim
      · rcases Finset.mem_union.mp hrUW with hrU | hrW
        · exact ((hsep U (by simp) x hxU r hrU (H.ne_of_adj hxr)).1 hxr).elim
        · rw [hWs'] at hrW
          rcases Finset.mem_insert.mp hrW with hrs | hrt
          · exact hrs ▸ hxr
          · exact (hxt (Finset.mem_singleton.mp hrt ▸ hxr)).elim
    · rcases Finset.mem_insert.mp hr0 with hrp' | hrq
      · exact (hrp hrp').elim
      · exact (hxq (Finset.mem_singleton.mp hrq ▸ hxr)).elim
  refine ⟨A, B, C, D, hUs, hWs, hNP,
    by simpa only [Finset.pair_comm D B] using hNQ, ?_, ?_⟩
  · exact force A D B C P Q hA hD hB hC hAD hWs hNZ hNP hNQ hcover haout
  · exact force D A C B Q P hD hA hC hB hAD.symm
      (by simpa only [Finset.pair_comm B C] using hWs)
      (by simpa only [Finset.pair_comm P Q] using hNZ) hNQ hNP
      (by simpa only [Finset.pair_comm P Q] using hcover)
      ⟨hdout.1, hdout.2.2, hdout.2.1⟩

private theorem eleven_nine_theta
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL3 : (degreeThree G L).card = 3) (hR2 : (degreeTwo G R).card = 2)
    (hR3 : (degreeThree G R).card = 7) (hR : R.card = 9) :
    ∃ u v w a b : V, ∃ Z P Q A B C D : SideHigh G R,
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ a ≠ b ∧
      degreeThree G L = {u, v, w} ∧ degreeTwo G R = {a, b} ∧
      G.neighborFinset a = {u, v} ∧ G.neighborFinset b = {v, w} ∧
      degreeThree G (G.neighborFinset u) = {A.val, D.val} ∧
      degreeThree G (G.neighborFinset v) = {Z.val} ∧
      degreeThree G (G.neighborFinset w) = {B.val, C.val} ∧
      [Z, P, Q, A, B, C, D].Nodup ∧
      (compressed G R).neighborFinset Z = {P, Q} ∧
      (compressed G R).neighborFinset P = {Z, A, C} ∧
      (compressed G R).neighborFinset Q = {Z, B, D} ∧
      (compressed G R).Adj A B ∧ (compressed G R).Adj D C ∧
      (∀ x ∈ ({P, Q} : Finset (SideHigh G R)),
        degreeThree G (G.neighborFinset x.val) = ∅) := by
  obtain ⟨u, v, w, a, b, Z, P, Q, U, W, huv, huw, hvw, hab, hhi, hlo,
    hNa, hNb, hNv, hUs, hWs, hU2, hW2, hUW, hZU, hZW, hPQ, hNZ,
    hP3, hQ3, htwo, hzero, hcover, hsep⟩ :=
    eleven_nine_blocks hpart hdeg hlow hg hL3 hR2 hR3 hR
  have hm (x : V) (hx : x ∈ ({u, v, w} : Finset V)) : x ∈ L ∧ G.degree x = 3 := by
    have hxhi : x ∈ degreeThree G L := by rw [hhi]; exact hx
    exact Finset.mem_filter.mp hxhi
  have hu := hm u (by simp)
  have hv := hm v (by simp)
  have hw := hm w (by simp)
  have hZ : Z ∉ U ∪ W := by simpa using And.intro hZU hZW
  have hsep' : ∀ X ∈ ({U, W} : Finset (Finset (SideHigh G R))),
      ∀ a ∈ X, ∀ b ∈ X, a ≠ b →
        ¬ (compressed G R).Adj a b ∧ ∀ t,
          (compressed G R).Adj a t → (compressed G R).Adj b t → False := by
    intro X hX a ha b hb hab
    rcases Finset.mem_insert.mp hX with hXU | hXW
    · rw [hXU, hUs] at ha hb
      exact hsep u (by simp) a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
    · have he := Finset.mem_singleton.mp hXW
      rw [he, hWs] at ha hb
      exact hsep w (by simp) a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  obtain ⟨A, B, C, D, hU, hW, hNP, hNQ, hAB, hDC⟩ :=
    seven_high_theta hU2 hW2 hUW hZ hPQ hcover hNZ hP3 hQ3 htwo
      (compressed_triangle_free hpart.symm hg) hsep'
  have hP : P ∉ U ∪ W := by intro hx; have h := htwo P hx; omega
  have hQ : Q ∉ U ∪ W := by intro hx; have h := htwo Q hx; omega
  have hAD : A ≠ D := by have hh := hU2; rw [hU] at hh; intro he; simp [he] at hh
  have hBC : B ≠ C := by have hh := hW2; rw [hW] at hh; intro he; simp [he] at hh
  have hdist : Disjoint ({A, D} : Finset (SideHigh G R)) {B, C} := by rwa [← hU, ← hW]
  have hA : A ∈ U := by rw [hU]; simp
  have hD : D ∈ U := by rw [hU]; simp
  have hB : B ∈ W := by rw [hW]; simp
  have hC : C ∈ W := by rw [hW]; simp
  have hout (x : SideHigh G R) (hx : x ∈ U ∪ W) :
      Z ≠ x ∧ P ≠ x ∧ Q ≠ x :=
    ⟨fun he => hZ (he.symm ▸ hx), fun he => hP (he.symm ▸ hx),
      fun he => hQ (he.symm ▸ hx)⟩
  have hZA := hout A (Finset.mem_union_left _ hA)
  have hZD := hout D (Finset.mem_union_left _ hD)
  have hZB := hout B (Finset.mem_union_right _ hB)
  have hZC := hout C (Finset.mem_union_right _ hC)
  have hZP : Z ≠ P := (compressed G R).ne_of_adj
    (((compressed G R).mem_neighborFinset _ _).mp (by rw [hNZ]; simp))
  have hZQ : Z ≠ Q := (compressed G R).ne_of_adj
    (((compressed G R).mem_neighborFinset _ _).mp (by rw [hNZ]; simp))
  have hcross (x : SideHigh G R) (hx : x ∈ U) (y : SideHigh G R) (hy : y ∈ W) : x ≠ y := by
    intro he
    exact Finset.disjoint_left.mp hUW (he ▸ hx) hy
  have hnodup : [Z, P, Q, A, B, C, D].Nodup := by
    simp [List.nodup_cons, hZP, hZQ, hPQ, hZA.1, hZB.1, hZC.1, hZD.1,
      hZA.2.1, hZB.2.1, hZC.2.1, hZD.2.1, hZA.2.2, hZB.2.2, hZC.2.2, hZD.2.2,
      hAD, hBC, hcross A hA B hB, hcross A hA C hC,
      (hcross D hD B hB).symm, (hcross D hD C hC).symm]
  have hNactual (r : V) (X : Finset (SideHigh G R))
      (hX : X = Finset.univ.filter (fun y => G.Adj r y.val))
      (hXpair : X = {A, D}) (hrL : r ∈ L) :
      degreeThree G (G.neighborFinset r) = {A.val, D.val} := by
    ext x
    constructor
    · intro hx
      have hx0 := Finset.mem_filter.mp hx
      have hrx := (G.mem_neighborFinset _ _).mp hx0.1
      let t : SideHigh G R := ⟨x, Finset.mem_filter.mpr ⟨hpart.mem_of_mem_adj hrL hrx, hx0.2⟩⟩
      have ht : t ∈ X := by rw [hX]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrx⟩
      rw [hXpair] at ht
      rcases Finset.mem_insert.mp ht with he | he
      · exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val he))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
          (congrArg Subtype.val (Finset.mem_singleton.mp he))))
    · intro hx
      rcases Finset.mem_insert.mp hx with he | he
      · subst x
        have ht : A ∈ X := by rw [hXpair]; simp
        rw [hX] at ht
        exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
          (Finset.mem_filter.mp ht).2, (Finset.mem_filter.mp A.property).2⟩
      · have he := Finset.mem_singleton.mp he
        subst x
        have ht : D ∈ X := by rw [hXpair]; simp
        rw [hX] at ht
        exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
          (Finset.mem_filter.mp ht).2, (Finset.mem_filter.mp D.property).2⟩
  have hNu := hNactual u U hUs hU hu.1
  have hNw : degreeThree G (G.neighborFinset w) = {B.val, C.val} := by
    ext x
    constructor
    · intro hx
      have hx0 := Finset.mem_filter.mp hx
      have hwx := (G.mem_neighborFinset _ _).mp hx0.1
      let t : SideHigh G R := ⟨x, Finset.mem_filter.mpr ⟨hpart.mem_of_mem_adj hw.1 hwx, hx0.2⟩⟩
      have ht : t ∈ W := by rw [hWs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwx⟩
      rw [hW] at ht
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        (show x = B.val ∨ x = C.val from (Finset.mem_insert.mp ht).elim
          (fun he => Or.inl (congrArg Subtype.val he))
          (fun he => Or.inr (congrArg Subtype.val (Finset.mem_singleton.mp he))))
    · intro hx
      rcases Finset.mem_insert.mp hx with he | he
      · subst x
        have ht : B ∈ W := hB
        rw [hWs] at ht
        exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
          (Finset.mem_filter.mp ht).2, (Finset.mem_filter.mp B.property).2⟩
      · have he := Finset.mem_singleton.mp he
        subst x
        have ht : C ∈ W := hC
        rw [hWs] at ht
        exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
          (Finset.mem_filter.mp ht).2, (Finset.mem_filter.mp C.property).2⟩
  exact ⟨u, v, w, a, b, Z, P, Q, A, B, C, D, huv, huw, hvw, hab,
    hhi, hlo, hNa, hNb, hNu, hNv, hNw, hnodup, hNZ, hNP, hNQ, hAB, hDC, hzero⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta
