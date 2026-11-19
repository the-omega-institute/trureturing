/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointCompression
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Actual low-path compression and the central high vertex in the twenty-point slice 11/9 branch. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
import Batteries.Tactic.OpenPrivate

/-! Consumed actual low-path compression and short-path geometry for TwentyPointSlice. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression

open scoped BigOperators Classical
open SimpleGraph GirthSliceCounting
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced)
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private parts_card sum_degrees_parts from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private neighbor_parts_card threePaths onePaths oneEndpoint endpoint
  one_three_paths_card_le_rectangle one_paths_card_eq_three_mul
  three_walk_endpoint_injective one_three_cross_impossible from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private High graph graph_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
open private middle_unique two_neighbor_table from
  D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure
open private other_high_of_low_neighbor from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
open private degree_three_root_identity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoLocal
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

attribute [local instance] Classical.propDecidable

/- Each compressed edge retains an actual degree-two middle.  The vertex type
   restricts only its endpoints; no compressed incidence is supplied as input. -/
private abbrev SideHigh {V : Type*} [Fintype V] (G : SimpleGraph V) (L : Finset V) :=
  {x : V // x ∈ degreeThree G L}

private def compressed {V : Type*} [Fintype V] (G : SimpleGraph V) (L : Finset V) :
    SimpleGraph (SideHigh G L) where
  Adj x y := x ≠ y ∧ ∃ m, G.degree m = 2 ∧ G.Adj x.val m ∧ G.Adj y.val m
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.choose, h.2.choose_spec.1,
    h.2.choose_spec.2.2, h.2.choose_spec.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem compressed_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) (x : SideHigh G L) :
    (compressed G L).degree x + (degreeThree G (G.neighborFinset x.val)).card = 3 := by
  have hxL := (Finset.mem_filter.mp x.property).1
  have hx3 := (Finset.mem_filter.mp x.property).2
  have ho (m : V) (hm : m ∈ degreeTwo G (G.neighborFinset x.val)) :
      ∃ y : SideHigh G L, x ≠ y ∧ G.Adj y.val m ∧
        G.neighborFinset m = {x.val, y.val} := by
    have hm0 := Finset.mem_filter.mp hm
    have hxm := (G.mem_neighborFinset _ _).mp hm0.1
    obtain ⟨y, hxy, hy3, hym, hN⟩ := other_high_of_low_neighbor hdeg hlow hm0.2 hxm
    have hmR := hpart.mem_of_mem_adj hxL hxm
    have hyL := hpart.mem_of_mem_adj' hmR hym
    exact ⟨⟨y, Finset.mem_filter.mpr ⟨hyL, hy3⟩⟩,
      fun he => hxy (congrArg Subtype.val he), hym, hN⟩
  have hc : (degreeTwo G (G.neighborFinset x.val)).card =
      ((compressed G L).neighborFinset x).card := by
    apply Finset.card_bij (fun m hm => Classical.choose (ho m hm))
    · intro m hm
      have hy := Classical.choose_spec (ho m hm)
      exact ((compressed G L).mem_neighborFinset _ _).mpr
        ⟨hy.1, m, (Finset.mem_filter.mp hm).2,
          (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hm).1, hy.2.1⟩
    · intro m hm n hn he
      have hy := Classical.choose_spec (ho m hm)
      have hz := Classical.choose_spec (ho n hn)
      exact middle_unique hpart hg hxL
        (fun hv => hy.1 (Subtype.ext hv))
        ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hm).1) hy.2.1
        ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hn).1)
        (by simpa only [he] using hz.2.1)
    · intro y hy
      obtain ⟨hxy, m, hm2, hxm, hym⟩ := ((compressed G L).mem_neighborFinset _ _).mp hy
      have hm : m ∈ degreeTwo G (G.neighborFinset x.val) :=
        Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxm, hm2⟩
      have hz := Classical.choose_spec (ho m hm)
      have hymem := (G.mem_neighborFinset _ _).mpr hym.symm
      rw [hz.2.2] at hymem
      rcases Finset.mem_insert.mp hymem with he | he
      · exact (hxy (Subtype.ext he).symm).elim
      · exact ⟨m, hm, (Subtype.ext (Finset.mem_singleton.mp he)).symm⟩
  have hp := neighbor_parts_card hdeg x.val
  rw [hc, SimpleGraph.card_neighborFinset_eq_degree, hx3] at hp
  exact hp

private theorem compressed_triangle_free
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) :
    ∀ x y z, (compressed G L).Adj x y → (compressed G L).Adj y z →
      (compressed G L).Adj z x → False := by
  intro x y z hxy hyz hzx
  obtain ⟨hxy, a, ha, hxa, hya⟩ := hxy
  obtain ⟨hyz, b, hb, hyb, hzb⟩ := hyz
  obtain ⟨hzx, c, hc, hzc, hxc⟩ := hzx
  have ht {m : V} (hm : G.degree m = 2)
      (hxm : G.Adj x.val m) (hym : G.Adj y.val m) (hzm : G.Adj z.val m) : False := by
    obtain ⟨w, hwx, hwm, hN⟩ := two_neighbor_table hm hxm
    have hys := (G.mem_neighborFinset _ _).mpr hym.symm
    have hzs := (G.mem_neighborFinset _ _).mpr hzm.symm
    rw [hN] at hys hzs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hys hzs
    rcases hys with he | he
    · exact hxy (Subtype.ext he).symm
    · rcases hzs with hz | hz
      · exact hzx (Subtype.ext hz)
      · exact hyz (Subtype.ext (he.trans hz.symm))
  have hab : a ≠ b := fun he => ht ha hxa hya (he ▸ hzb)
  have hcb : c ≠ b := fun he => ht hc hxc (he ▸ hyb) hzc
  have hac : a ≠ c := fun he => ht ha hxa hya (he ▸ hzc)
  have he := three_walk_endpoint_injective hpart hg
    (Finset.mem_filter.mp x.property).1 (Finset.mem_filter.mp x.property).1
    hxa hya.symm hyb hxc hzc.symm hzb
    (fun h => hxy (Subtype.ext h)) hab (fun h => hzx (Subtype.ext h).symm) hcb ⟨rfl, rfl⟩
  exact hac he.2.1

/- Nine opposite vertices leave precisely six distinct third-layer endpoints.
   In particular every high-high edge has a unique high endpoint on that side:
   a second high neighbor there would overflow the actual third layer. -/
private theorem nine_side_no_high_wedge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) (hR : R.card = 9)
    {x : V} (hxL : x ∈ L) (hx3 : G.degree x = 3) :
    (threePaths G {x}).card = 6 ∧
      ∀ y, G.Adj x y → G.degree y = 3 →
        degreeThree G (G.neighborFinset y) = {x} := by
  have hu := one_three_paths_card_le_rectangle {x} (by simpa using hxL) hpart hg
  rw [one_paths_card_eq_three_mul _ (by simpa using hx3)] at hu
  simp only [Finset.card_singleton, mul_one, one_mul, hR] at hu
  have hi := degree_three_root_identity hdeg hlow hx3
  have hper (y : V) (hy : y ∈ degreeThree G (G.neighborFinset x)) :
      1 ≤ (degreeThree G (G.neighborFinset y)).card := by
    have hxy := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hy).1
    exact Finset.one_le_card.mpr ⟨x,
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy.symm, hx3⟩⟩
  have hs := Finset.sum_le_sum hper
  simp only [Finset.sum_const_nat, mul_one] at hs
  have ht : (threePaths G {x}).card = 6 := by omega
  refine ⟨ht, ?_⟩
  intro y hxy hy3
  have hy : y ∈ degreeThree G (G.neighborFinset x) :=
    Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy, hy3⟩
  have hcy : (degreeThree G (G.neighborFinset y)).card = 1 := by
    have hle := hper y hy
    by_contra hn
    have hlt : 1 < (degreeThree G (G.neighborFinset y)).card := by omega
    have hsum := Finset.sum_lt_sum hper ⟨y, hy, hlt⟩
    simp only [Finset.sum_const_nat, mul_one] at hsum
    omega
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · exact Finset.singleton_subset_iff.mpr
      (Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy.symm, hx3⟩)
  · simp [hcy]

private theorem nine_side_three_step_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) (hR : R.card = 9)
    {x y : V} (hxL : x ∈ L) (hx3 : G.degree x = 3)
    (hyR : y ∈ R) (hxy : ¬ G.Adj x y) :
    ∃ a b, G.Adj x a ∧ G.Adj a b ∧ G.Adj b y ∧ x ≠ b ∧ a ≠ y := by
  let T := (threePaths G {x}).image (fun q => q.endpoint)
  have hinj : Set.InjOn (fun q : ThreeStep V => q.endpoint) (↑(threePaths G {x})) := by
    intro p hp q hq he
    have hp0 : p.root = x ∧ G.Adj p.root p.first ∧ G.Adj p.first p.second ∧
        G.Adj p.second p.endpoint ∧ p.root ≠ p.second ∧ p.first ≠ p.endpoint := by
      simpa [threePaths] using hp
    have hq0 : q.root = x ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
        G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
      simpa [threePaths] using hq
    have hi := three_walk_endpoint_injective hpart hg (hp0.1.symm ▸ hxL)
      (hq0.1.symm ▸ hxL) hp0.2.1 hp0.2.2.1 hp0.2.2.2.1
      hq0.2.1 hq0.2.2.1 hq0.2.2.2.1 hp0.2.2.2.2.1 hp0.2.2.2.2.2
      hq0.2.2.2.2.1 hq0.2.2.2.2.2 ⟨hp0.1.trans hq0.1.symm, he⟩
    cases p; cases q
    simp_all
  have hc : T.card = 6 := by
    rw [Finset.card_image_of_injOn hinj]
    exact (nine_side_no_high_wedge hpart hdeg hlow hg hR hxL hx3).1
  have hsub : G.neighborFinset x ∪ T ⊆ R := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hpart.mem_of_mem_adj hxL ((G.mem_neighborFinset _ _).mp hz)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hq0 : q.root = x ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
          G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
        simpa [threePaths] using hq
      have ha := hpart.mem_of_mem_adj (hq0.1.symm ▸ hxL) hq0.2.1
      have hb := hpart.mem_of_mem_adj' ha hq0.2.2.1.symm
      exact hpart.mem_of_mem_adj hb hq0.2.2.2.1
  have hd : Disjoint (G.neighborFinset x) T := by
    apply Finset.disjoint_left.mpr
    intro z hz hzT
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hzT
    have hq0 : q.root = x ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
        G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
      simpa [threePaths] using hq
    exact one_three_cross_impossible hpart hg hxL (hq0.1.symm ▸ hxL)
      ((G.mem_neighborFinset _ _).mp hz) hq0.2.1 hq0.2.2.1 hq0.2.2.2.1
      hq0.2.2.2.2.1 hq0.2.2.2.2.2 ⟨hq0.1.symm, he.symm⟩
  have hcover : G.neighborFinset x ∪ T = R :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_union_of_disjoint hd, SimpleGraph.card_neighborFinset_eq_degree,
        hx3, hc, hR])
  have hyT : y ∈ T := by
    have hy := hyR
    rw [← hcover] at hy
    exact (Finset.mem_union.mp hy).resolve_left (by simpa using hxy)
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hyT
  have hq0 : q.root = x ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
      G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
    simpa [threePaths] using hq
  exact ⟨q.first, q.second, hq0.1 ▸ hq0.2.1, hq0.2.2.1,
    he ▸ hq0.2.2.2.1, hq0.1 ▸ hq0.2.2.2.2.1, he ▸ hq0.2.2.2.2.2⟩

private theorem selected_three_hamming
    {n : ℕ} {S : Finset (Q n)} (hbal : IsBalanced S)
    {x a b y : (S : Set (Q n))}
    (hxa : ((hypercube n).induce (S : Set (Q n))).Adj x a)
    (hab : ((hypercube n).induce (S : Set (Q n))).Adj a b)
    (hby : ((hypercube n).induce (S : Set (Q n))).Adj b y)
    (hxb : x ≠ b) (hay : a ≠ y) : hammingDist x.val y.val = 3 := by
  obtain ⟨i, hai⟩ := adjacent_exists_flip hxa
  obtain ⟨j, hbj⟩ := adjacent_exists_flip hab
  obtain ⟨k, hyk⟩ := adjacent_exists_flip hby
  change a.val = BalancedCriticalSpectrum.flip x.val i at hai
  change b.val = BalancedCriticalSpectrum.flip a.val j at hbj
  change y.val = BalancedCriticalSpectrum.flip b.val k at hyk
  have hij : i ≠ j := by
    intro he
    have hb : b.val = x.val := by
      rw [hbj, hai, ← he, BalancedCriticalSpectrum.flip_flip]
    exact hxb (Subtype.ext hb.symm)
  have hjk : j ≠ k := by
    intro he
    have hy : y.val = a.val := by
      rw [hyk, hbj, ← he, BalancedCriticalSpectrum.flip_flip]
    exact hay (Subtype.ext hy.symm)
  have hik : i ≠ k := BalancedCubeGirth.three_directions_distinct hbal hij hjk
    x.property (hai ▸ a.property) (by rw [← hai, ← hbj]; exact b.property)
    (by rw [← hai, ← hbj, ← hyk]; exact y.property)
  have he : y.val = BalancedCriticalSpectrum.flip
      (BalancedCriticalSpectrum.flip (BalancedCriticalSpectrum.flip x.val i) j) k := by
    rw [hyk, hbj, hai]
  have hd : Finset.univ.filter (fun r => x.val r ≠ y.val r) = {i, j, k} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [he]
    by_cases hri : r = i
    · subst r
      cases hv : x.val i <;>
        simp [BalancedCriticalSpectrum.flip, hij, hik, hv]
    · by_cases hrj : r = j
      · subst r
        cases hv : x.val j <;>
          simp [BalancedCriticalSpectrum.flip, hri, hjk, hv]
      · by_cases hrk : r = k
        · subst r
          cases hv : x.val k <;>
            simp [BalancedCriticalSpectrum.flip, hri, hrj, hv]
        · simp [BalancedCriticalSpectrum.flip, hri, hrj, hrk]
  change (Finset.univ.filter (fun r => x.val r ≠ y.val r)).card = 3
  rw [hd]
  simp [hij, hik, hjk]

private theorem two_low_path
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL3 : (degreeThree G L).card = 3) (hR2 : (degreeTwo G R).card = 2) :
    ∃ u v w a b, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ a ≠ b ∧
      degreeThree G L = {u, v, w} ∧ degreeTwo G R = {a, b} ∧
      G.neighborFinset a = {u, v} ∧ G.neighborFinset b = {v, w} := by
  obtain ⟨a, b, hab, habR⟩ := Finset.card_eq_two.mp hR2
  have haR : a ∈ degreeTwo G R := by rw [habR]; simp
  have hbR : b ∈ degreeTwo G R := by rw [habR]; simp
  have ha2 := (Finset.mem_filter.mp haR).2
  have hb2 := (Finset.mem_filter.mp hbR).2
  have hsub (m : V) (hm : m ∈ degreeTwo G R) :
      G.neighborFinset m ⊆ degreeThree G L := by
    intro x hx
    have hmx := (G.mem_neighborFinset _ _).mp hx
    have hxL := hpart.mem_of_mem_adj' (Finset.mem_filter.mp hm).1 hmx.symm
    have hx3 : G.degree x = 3 := by
      rcases hdeg x with hx2 | hx3
      · exact (hlow hmx (Finset.mem_filter.mp hm).2 hx2).elim
      · exact hx3
    exact Finset.mem_filter.mpr ⟨hxL, hx3⟩
  have hca : (G.neighborFinset a).card = 2 := by simpa using ha2
  have hcb : (G.neighborFinset b).card = 2 := by simpa using hb2
  have hcU : (G.neighborFinset a ∪ G.neighborFinset b).card ≤ 3 :=
    (Finset.card_le_card (Finset.union_subset (hsub a haR) (hsub b hbR))).trans_eq hL3
  have hci := Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  have hcI : 0 < (G.neighborFinset a ∩ G.neighborFinset b).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hcI
  have hva := ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hv).1).symm
  have hvb := ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hv).2).symm
  obtain ⟨u, huv, hua, hNa⟩ := two_neighbor_table ha2 hva
  obtain ⟨w, hwv, hwb, hNb⟩ := two_neighbor_table hb2 hvb
  have hvL : v ∈ L := (Finset.mem_filter.mp (hsub a haR (Finset.mem_inter.mp hv).1)).1
  have huw : u ≠ w := by
    intro he
    exact hab (middle_unique hpart hg hvL huv.symm hva hua hvb (he ▸ hwb))
  have huL : u ∈ degreeThree G L := hsub a haR ((G.mem_neighborFinset _ _).mpr hua.symm)
  have hvL3 : v ∈ degreeThree G L := hsub a haR (Finset.mem_inter.mp hv).1
  have hwL : w ∈ degreeThree G L := hsub b hbR ((G.mem_neighborFinset _ _).mpr hwb.symm)
  refine ⟨u, v, w, a, b, huv, huw, hwv.symm, hab, ?_, habR, ?_, hNb⟩
  · apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨huL, hvL3, hwL⟩
    · simp [hL3, huv, huw, hwv.symm]
  · simpa only [Finset.pair_comm] using hNa

private theorem eleven_nine_central_obstruction
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL3 : (degreeThree G L).card = 3) (hR2 : (degreeTwo G R).card = 2)
    (hR : R.card = 9) :
    ∃ u v w a b, ∃ Z : SideHigh G R, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ a ≠ b ∧
      degreeThree G L = {u, v, w} ∧ degreeTwo G R = {a, b} ∧
      G.neighborFinset a = {u, v} ∧ G.neighborFinset b = {v, w} ∧
      degreeThree G (G.neighborFinset v) = {Z.val} ∧
      (compressed G R).degree Z = 2 ∧
      ∀ z, (compressed G R).Adj Z z → degreeThree G (G.neighborFinset z.val) = ∅ := by
  obtain ⟨u, v, w, a, b, huv, huw, hvw, hab, hhi, hlo, hNa, hNb⟩ :=
    two_low_path hpart hdeg hlow hg hL3 hR2
  have hm (x : V) (hx : x ∈ ({u, v, w} : Finset V)) : x ∈ L ∧ G.degree x = 3 := by
    have hxhi : x ∈ degreeThree G L := by rw [hhi]; exact hx
    exact Finset.mem_filter.mp hxhi
  have hu := hm u (by simp)
  have hv := hm v (by simp)
  have hw := hm w (by simp)
  have ha2 : G.degree a = 2 := (Finset.mem_filter.mp (show a ∈ degreeTwo G R by rw [hlo]; simp)).2
  have hb2 : G.degree b = 2 := (Finset.mem_filter.mp (show b ∈ degreeTwo G R by rw [hlo]; simp)).2
  have hva : G.Adj v a := by
    apply G.adj_symm
    apply (G.mem_neighborFinset _ _).mp
    rw [hNa]; simp
  have hua : G.Adj u a := by
    apply G.adj_symm
    apply (G.mem_neighborFinset _ _).mp
    rw [hNa]; simp
  have hvb : G.Adj v b := by
    apply G.adj_symm
    apply (G.mem_neighborFinset _ _).mp
    rw [hNb]; simp
  have hwb : G.Adj w b := by
    apply G.adj_symm
    apply (G.mem_neighborFinset _ _).mp
    rw [hNb]; simp
  have hNv : degreeTwo G (G.neighborFinset v) = {a, b} := by
    ext x
    constructor
    · intro hx
      have hx0 := Finset.mem_filter.mp hx
      have hvx := (G.mem_neighborFinset _ _).mp hx0.1
      have hxR := hpart.mem_of_mem_adj hv.1 hvx
      have hxlo : x ∈ degreeTwo G R := Finset.mem_filter.mpr ⟨hxR, hx0.2⟩
      rwa [hlo] at hxlo
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, ha2⟩
      · have he := Finset.mem_singleton.mp hx
        subst x
        exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hb2⟩
  have hc := neighbor_parts_card hdeg v
  rw [hNv, Finset.card_pair hab, hv.2] at hc
  have hc1 : (degreeThree G (G.neighborFinset v)).card = 1 := by omega
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc1
  have hzN : z ∈ degreeThree G (G.neighborFinset v) := by rw [hz]; simp
  have hz0 := Finset.mem_filter.mp hzN
  have hvz := (G.mem_neighborFinset _ _).mp hz0.1
  let Z : SideHigh G R := ⟨z, Finset.mem_filter.mpr ⟨hpart.mem_of_mem_adj hv.1 hvz, hz0.2⟩⟩
  have hNz : degreeThree G (G.neighborFinset z) = {v} :=
    (nine_side_no_high_wedge hpart hdeg hlow hg hR hv.1 hv.2).2 z hvz hz0.2
  have hZdeg : (compressed G R).degree Z = 2 := by
    have hcZ := compressed_degree hpart.symm hdeg hlow hg Z
    change (compressed G R).degree Z + (degreeThree G (G.neighborFinset z)).card = 3 at hcZ
    rw [hNz, Finset.card_singleton] at hcZ
    omega
  refine ⟨u, v, w, a, b, Z, huv, huw, hvw, hab, hhi, hlo, hNa, hNb, hz, hZdeg, ?_⟩
  intro t ht
  obtain ⟨hzt, m, hm2, hzm, htm⟩ := ht
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx0 := Finset.mem_filter.mp hx
  have htx := (G.mem_neighborFinset _ _).mp hx0.1
  have htR := (Finset.mem_filter.mp t.property).1
  have hxL := hpart.mem_of_mem_adj' htR htx.symm
  have hxhi : x ∈ degreeThree G L := Finset.mem_filter.mpr ⟨hxL, hx0.2⟩
  rw [hhi] at hxhi
  have htmne : z ≠ t.val := fun he => hzt (Subtype.ext he)
  have hvm : v ≠ m := by intro he; have h := he ▸ hv.2; omega
  have hbad (r l : V) (hr : v ≠ r) (hl2 : G.degree l = 2)
      (hvl : G.Adj v l) (hrl : G.Adj r l) (hrt : G.Adj r t.val) : False := by
    have hlt : l ≠ t.val := by
      intro he
      have ht3 := (Finset.mem_filter.mp t.property).2
      have h := he ▸ hl2
      omega
    have he := three_walk_endpoint_injective hpart hg hv.1 hv.1
      hvl hrl.symm hrt hvz hzm htm.symm hr hlt hvm htmne ⟨rfl, rfl⟩
    have he' : l = z := he.2.1
    have hh := he' ▸ hl2
    omega
  rcases Finset.mem_insert.mp hxhi with hxu | hxhi
  · exact hbad u a huv.symm ha2 hva hua (hxu ▸ htx.symm)
  · rcases Finset.mem_insert.mp hxhi with hxv | hxhi
    · have htN : t.val ∈ degreeThree G (G.neighborFinset v) :=
        Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr (hxv ▸ htx.symm),
          (Finset.mem_filter.mp t.property).2⟩
      rw [hz] at htN
      exact htmne (Finset.mem_singleton.mp htN).symm
    · have he := Finset.mem_singleton.mp hxhi
      subst x
      exact hbad w b hvw hb2 hvb hwb htx.symm

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
