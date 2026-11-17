/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceLabels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceLabels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Actual high-core and right-vertex labels from slice parameters. -/


import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity
import Batteries.Tactic.OpenPrivate

set_option linter.style.longLine false

open private rootThreeWeight root_three_paths_card root_weight_add_two root_paths_card_of_coverage root_weight_low root_weight_high root_three_paths_two_connectors saturation_count_equalities saturation_local_equality right_high_neighbor_rigidity saturation_endpoint_union high_root_endpoint_coverage low_vertex_high_neighbor_card asymmetric_right_type_counts asymmetric_left_connector_count neighbors_eq_pair complete_pairing c6_core_of_distinguished_pair AsymmetricRigidityCore.c6_core_of_distinguished_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity

/- Compression of actual two-high-neighbor right
vertices. All girth input is used through existing short-path uniqueness. -/

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricCompressedCore

open SimpleGraph GirthSliceCounting
open private one_three_cross_impossible three_walk_endpoint_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

private abbrev High (G : SimpleGraph V) (L : Finset V) :=
  {x : V // x ∈ degreeThree G L}

private def connectors (G : SimpleGraph V) (R : Finset V) : Finset V :=
  (degreeThree G R).filter fun m =>
    (degreeThree G (G.neighborFinset m)).card = 2

private def core (G : SimpleGraph V) (L R : Finset V) : SimpleGraph (High G L) where
  Adj x y := x ≠ y ∧ ∃ m ∈ connectors G R, G.Adj x.val m ∧ G.Adj y.val m
  symm := ⟨fun _ _ h => by
    obtain ⟨hne, m, hm, hxm, hym⟩ := h
    exact ⟨hne.symm, m, hm, hym, hxm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G : SimpleGraph V} {L R : Finset V}

private theorem high_left (x : High G L) : x.val ∈ L :=
  (Finset.mem_filter.mp x.property).1

private theorem high_degree (x : High G L) : G.degree x.val = 3 :=
  (Finset.mem_filter.mp x.property).2

private theorem connector_right {m : V} (hm : m ∈ connectors G R) : m ∈ R :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1

private theorem connector_degree {m : V} (hm : m ∈ connectors G R) :
    G.degree m = 3 :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2

private theorem connector_card {m : V} (hm : m ∈ connectors G R) :
    (degreeThree G (G.neighborFinset m)).card = 2 :=
  (Finset.mem_filter.mp hm).2

private theorem high_neighbor_mem {m : V} (x : High G L) (hxm : G.Adj x.val m) :
    x.val ∈ degreeThree G (G.neighborFinset m) :=
  Finset.mem_filter.mpr
    ⟨(G.mem_neighborFinset m x.val).mpr hxm.symm, high_degree x⟩

/-- This identifies the core input with the actual single-root counting output;
membership in the right part follows from the actual bipartition. -/
private theorem connector_filter_eq
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V)) (x : High G L) :
    ((connectors G R).filter fun m => G.Adj x.val m) =
      (G.neighborFinset x.val).filter (fun m => G.degree m = 3 ∧
        (degreeThree G (G.neighborFinset m)).card = 2) := by
  ext m
  constructor
  · intro hm
    obtain ⟨hmM, hxm⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr
      ⟨(G.mem_neighborFinset x.val m).mpr hxm,
        connector_degree hmM, connector_card hmM⟩
  · intro hm
    obtain ⟨hmN, hm3, hmc⟩ := Finset.mem_filter.mp hm
    have hxm := (G.mem_neighborFinset x.val m).mp hmN
    have hmR : m ∈ R := hpart.mem_of_mem_adj (high_left x) hxm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmR, hm3⟩, hmc⟩, hxm⟩

private theorem connector_third {m : V} (hm : m ∈ connectors G R)
    {x y w : High G L} (hxy : x ≠ y)
    (hxm : G.Adj x.val m) (hym : G.Adj y.val m) (hwm : G.Adj w.val m) :
    w = x ∨ w = y := by
  classical
  have hv : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hs : ({x.val, y.val} : Finset V) ⊆
      degreeThree G (G.neighborFinset m) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · subst z
      exact high_neighbor_mem x hxm
    · subst z
      exact high_neighbor_mem y hym
  have he : degreeThree G (G.neighborFinset m) = {x.val, y.val} := by
    apply (Finset.eq_of_subset_of_card_le hs ?_).symm
    simp [connector_card hm, hv]
  have hw := high_neighbor_mem w hwm
  rw [he] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  exact hw.elim (fun h => Or.inl (Subtype.ext h)) (fun h => Or.inr (Subtype.ext h))

private theorem other_high
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {m : V} (hm : m ∈ connectors G R)
    (x : High G L) (hxm : G.Adj x.val m) :
    ∃ y : High G L, y ≠ x ∧ G.Adj y.val m := by
  classical
  have hc : 1 < (degreeThree G (G.neighborFinset m)).card := by
    rw [connector_card hm]
    decide
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne hc x.val
  have hym : G.Adj y m :=
    ((G.mem_neighborFinset m y).mp (Finset.mem_filter.mp hy).1).symm
  have hyL : y ∈ L := hpart.mem_of_mem_adj' (connector_right hm) hym
  have hyH : y ∈ degreeThree G L :=
    Finset.mem_filter.mpr ⟨hyL, (Finset.mem_filter.mp hy).2⟩
  refine ⟨⟨y, hyH⟩, ?_, hym⟩
  intro h
  exact hyx (congrArg Subtype.val h)

private theorem middle_unique
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {x y : High G L} (hxy : x ≠ y) {m n : V}
    (hxm : G.Adj x.val m) (hym : G.Adj y.val m)
    (hxn : G.Adj x.val n) (hyn : G.Adj y.val n) : m = n := by
  by_contra hmn
  have hv : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  exact one_three_cross_impossible hpart hg (high_left x) (high_left x)
    hxn hxm hym.symm hyn hv hmn ⟨rfl, rfl⟩

private theorem different_middle {x y w : High G L} {m n : V}
    (hm : m ∈ connectors G R) (hn : n ∈ connectors G R)
    (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w)
    (hxm : G.Adj x.val m) (hym : G.Adj y.val m)
    (hyn : G.Adj y.val n) (hwn : G.Adj w.val n) : m ≠ n := by
  intro hmn
  have hwm : G.Adj w.val m := by simpa only [hmn] using hwn
  rcases connector_third hm hxy hxm hym hwm with hwx | hwy
  · exact hxw hwx.symm
  · exact hyw hwy.symm

/-- The saturated actual M-neighbor count becomes degree two in the compressed graph. -/
private theorem core_degree_two
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (htwo : ∀ x : High G L,
      ((connectors G R).filter fun m => G.Adj x.val m).card = 2) :
    ∀ x : High G L, (core G L R).degree x = 2 := by
  classical
  intro x
  let Q := (connectors G R).filter fun m => G.Adj x.val m
  have hQc : Q.card = 2 := htwo x
  obtain ⟨m, n, hmn, hQ⟩ := Finset.card_eq_two.mp hQc
  have hmQ : m ∈ Q := by rw [hQ]; simp
  have hnQ : n ∈ Q := by rw [hQ]; simp
  obtain ⟨hm, hxm⟩ := Finset.mem_filter.mp hmQ
  obtain ⟨hn, hxn⟩ := Finset.mem_filter.mp hnQ
  obtain ⟨y, hyx, hym⟩ := other_high hpart hm x hxm
  obtain ⟨w, hwx, hwn⟩ := other_high hpart hn x hxn
  have hyw : y ≠ w := by
    intro hyw
    have hyn : G.Adj y.val n := by simpa only [hyw] using hwn
    exact hmn (middle_unique hpart hg hyx.symm hxm hym hxn hyn)
  have hxy : (core G L R).Adj x y := ⟨hyx.symm, m, hm, hxm, hym⟩
  have hxw : (core G L R).Adj x w := ⟨hwx.symm, n, hn, hxn, hwn⟩
  have hN : (core G L R).neighborFinset x = {y, w} := by
    ext z
    rw [(core G L R).mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hz
      obtain ⟨hxz, a, ha, hxa, hza⟩ := hz
      have haQ : a ∈ Q := Finset.mem_filter.mpr ⟨ha, hxa⟩
      rw [hQ] at haQ
      simp only [Finset.mem_insert, Finset.mem_singleton] at haQ
      rcases haQ with ham | han
      · subst a
        rcases connector_third hm hyx.symm hxm hym hza with hzx | hzy
        · exact False.elim (hxz hzx.symm)
        · exact Or.inl hzy
      · subst a
        rcases connector_third hn hwx.symm hxn hwn hza with hzx | hzw
        · exact False.elim (hxz hzx.symm)
        · exact Or.inr hzw
    · intro hz
      rcases hz with hzy | hzw
      · subst z
        exact hxy
      · subst z
        exact hxw
  change ((core G L R).neighborFinset x).card = 2
  rw [hN]
  simp [hyw]

/-- A compressed triangle would give two distinct actual three-step paths. -/
private theorem core_triangle_free
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) :
    ∀ x y w : High G L, (core G L R).Adj x y → (core G L R).Adj y w →
      (core G L R).Adj w x → False := by
  intro x y w hxy hyw hwx
  obtain ⟨hxy, a, ha, hxa, hya⟩ := hxy
  obtain ⟨hyw, b, hb, hyb, hwb⟩ := hyw
  obtain ⟨hwx, c, hc, hwc, hxc⟩ := hwx
  have hab := different_middle ha hb hxy hwx.symm hyw hxa hya hyb hwb
  have hcb := different_middle hc hb hwx.symm hxy hyw.symm hxc hwc hwb hyb
  have hac : a ≠ c :=
    different_middle ha hc hxy.symm hyw hwx.symm hya hxa hxc hwc
  have hxyV : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hxwV : x.val ≠ w.val := fun h => hwx (Subtype.ext h).symm
  have he := three_walk_endpoint_injective hpart hg (high_left x) (high_left x)
    hxa hya.symm hyb hxc hwc.symm hwb hxyV hab hxwV hcb ⟨rfl, rfl⟩
  exact hac he.2.1

/-- Any actual right degree-two vertex anchors a nonedge with no common core neighbor. -/
private theorem low_vertex_anchor
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (z : V) (hzR : z ∈ R) (hz2 : G.degree z = 2) :
    ∃ u v : High G L, G.Adj u.val z ∧ G.Adj v.val z ∧ u ≠ v ∧
      ¬ (core G L R).Adj u v ∧
      (∀ w : High G L, (core G L R).Adj u w → (core G L R).Adj v w → False) := by
  classical
  have hzc : (G.neighborFinset z).card = 2 := by
    rw [G.card_neighborFinset_eq_degree, hz2]
  obtain ⟨u0, v0, huv0, hNz⟩ := Finset.card_eq_two.mp hzc
  have hzu : G.Adj z u0 := (G.mem_neighborFinset z u0).mp (by simp [hNz])
  have hzv : G.Adj z v0 := (G.mem_neighborFinset z v0).mp (by simp [hNz])
  have hu3 : G.degree u0 = 3 := by
    rcases hdeg u0 with hu2 | hu3
    · exact False.elim (hlow hzu hz2 hu2)
    · exact hu3
  have hv3 : G.degree v0 = 3 := by
    rcases hdeg v0 with hv2 | hv3
    · exact False.elim (hlow hzv hz2 hv2)
    · exact hv3
  have huH : u0 ∈ degreeThree G L := Finset.mem_filter.mpr
    ⟨hpart.mem_of_mem_adj' hzR hzu.symm, hu3⟩
  have hvH : v0 ∈ degreeThree G L := Finset.mem_filter.mpr
    ⟨hpart.mem_of_mem_adj' hzR hzv.symm, hv3⟩
  let u : High G L := ⟨u0, huH⟩
  let v : High G L := ⟨v0, hvH⟩
  have huv : u ≠ v := fun h => huv0 (congrArg Subtype.val h)
  have huvV : u.val ≠ v.val := huv0
  have huz : G.Adj u.val z := hzu.symm
  have hvz : G.Adj v.val z := hzv.symm
  have hzm : ∀ m ∈ connectors G R, z ≠ m := by
    intro m hm h
    have hm3 := connector_degree hm
    rw [← h, hz2] at hm3
    omega
  have hnot : ¬ (core G L R).Adj u v := by
    intro h
    obtain ⟨_, m, hm, hum, hvm⟩ := h
    exact one_three_cross_impossible hpart hg (high_left u) (high_left u)
      hum huz hvz.symm hvm huvV (hzm m hm) ⟨rfl, rfl⟩
  have hcommon : ∀ w : High G L,
      (core G L R).Adj u w → (core G L R).Adj v w → False := by
    intro w huw hvw
    obtain ⟨huw, a, ha, hua, hwa⟩ := huw
    obtain ⟨hvw, b, hb, hvb, hwb⟩ := hvw
    have hab : a ≠ b :=
      different_middle ha hb huw huv hvw.symm hua hwa hwb hvb
    have huwV : u.val ≠ w.val := fun h => huw (Subtype.ext h)
    have he := three_walk_endpoint_injective hpart hg (high_left u) (high_left u)
      huz hvz.symm hvb hua hwa.symm hwb
      huvV (hzm b hb) huwV hab ⟨rfl, rfl⟩
    exact (hzm a ha) he.2.1
  exact ⟨u, v, huz, hvz, huv, hnot, hcommon⟩

/-- The exact package consumed by the generic six-vertex C6 core lemma. The
two-connector hypothesis is supplied by the separate actual root-path count. -/
private theorem compressed_core_package
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hH : (degreeThree G L).card = 6)
    (htwo : ∀ x : High G L,
      ((connectors G R).filter fun m => G.Adj x.val m).card = 2)
    (z : V) (hzR : z ∈ R) (hz2 : G.degree z = 2) :
    Fintype.card (High G L) = 6 ∧
    (∀ x : High G L, (core G L R).degree x = 2) ∧
    (∀ x y w : High G L, (core G L R).Adj x y → (core G L R).Adj y w →
      (core G L R).Adj w x → False) ∧
    ∃ u v : High G L, G.Adj u.val z ∧ G.Adj v.val z ∧ u ≠ v ∧
      ¬ (core G L R).Adj u v ∧
      (∀ w : High G L, (core G L R).Adj u w → (core G L R).Adj v w → False) := by
  refine ⟨?_, core_degree_two hpart hg htwo, core_triangle_free hpart hg,
    low_vertex_anchor hpart hdeg hlow hg z hzR hz2⟩
  simpa only [High, Fintype.card_coe] using hH

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricCompressedCore

end

/- The actual parameters imply the labeled compressed high skeleton.
The low-vertex pairing and the full induced cube exclusion remain separate obligations. -/

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricHighSkeleton

open SimpleGraph GirthSliceCounting AsymmetricCompressedCore
open private asymmetric_left_connector_count from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity
open private degree_parts_union degree_parts_disjoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

/-- No root-path count, core regularity, cycle certificate or labeling is assumed. -/
private theorem high_skeleton_labels
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1) :
    ∃ z ∈ degreeTwo G R, ∃ u v x1 x2 y1 y2 : High G L,
      G.Adj u.val z ∧ G.Adj v.val z ∧
      ([u, v, x1, x2, y1, y2] : List (High G L)).Nodup ∧
      (∀ w : High G L, w = u ∨ w = v ∨ w = x1 ∨ w = x2 ∨ w = y1 ∨ w = y2) ∧
      (core G L R).neighborFinset u = {x1, x2} ∧
      (core G L R).neighborFinset v = {y1, y2} ∧
      (core G L R).neighborFinset x1 = {u, y1} ∧
      (core G L R).neighborFinset x2 = {u, y2} ∧
      (core G L R).neighborFinset y1 = {v, x1} ∧
      (core G L R).neighborFinset y2 = {v, x2} := by
  classical
  have hLc := congrArg Finset.card (degree_parts_union hdeg L)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint L)] at hLc
  have hH : (degreeThree G L).card = 6 := by omega
  have htwo : ∀ x : High G L,
      ((connectors G R).filter fun m => G.Adj x.val m).card = 2 := by
    intro x
    rw [connector_filter_eq hpart x]
    exact asymmetric_left_connector_count hpart hdeg hlow hg hL hR hL2 hR2 x.property
  have hn : (degreeTwo G R).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z, hz⟩ := hn
  have hz' := Finset.mem_filter.mp hz
  obtain ⟨hcard, hregular, htriangle, u, v, huz, hvz, huv, hnot, hcommon⟩ :=
    compressed_core_package hpart hdeg hlow hg hH htwo z hz'.1 hz'.2
  obtain ⟨x1, x2, y1, y2, hd, hall, hNu, hNv, hNx1, hNx2, hNy1, hNy2⟩ :=
    AsymmetricRigidityCore.c6_core_of_distinguished_pair
      (core G L R) hcard hregular htriangle u v huv hnot hcommon
  exact ⟨z, hz, u, v, x1, x2, y1, y2, huz, hvz, hd, hall,
    hNu, hNv, hNx1, hNx2, hNy1, hNy2⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricHighSkeleton

end

/- Local pairing lemmas for the actual asymmetric-slice classification. -/

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairing

open SimpleGraph GirthSliceCounting
open private three_walk_endpoint_injective one_three_cross_impossible from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private def lowPair (G : SimpleGraph V) (a b : V) : Prop :=
  ∃ w, G.degree w = 2 ∧ G.Adj a w ∧ G.Adj b w

private theorem low_pair_excluded_by_common_high
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {a t p : V} (haR : a ∈ R) (hp3 : G.degree p = 3)
    (hap : G.Adj a p) (htp : G.Adj t p) (hat : a ≠ t) :
    ¬ lowPair G a t := by
  rintro ⟨w, hw2, haw, htw⟩
  have hwp : w ≠ p := by intro he; rw [he, hp3] at hw2; omega
  exact one_three_cross_impossible hpart.symm hg haR haR
    hap haw htw.symm htp hat hwp ⟨rfl, rfl⟩

private theorem low_pair_excluded_by_short_paths
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {a t p m q : V} (haR : a ∈ R)
    (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hap : G.Adj a p) (hpm : G.Adj p m) (hmq : G.Adj m q)
    (htq : G.Adj t q) (hat : a ≠ t) (ham : a ≠ m) (hpq : p ≠ q) :
    ¬ lowPair G a t := by
  rintro ⟨w, hw2, haw, htw⟩
  have hwq : w ≠ q := by intro he; rw [he, hq3] at hw2; omega
  have he := three_walk_endpoint_injective hpart.symm hg haR haR
    haw htw.symm htq hap hpm hmq hat hwq ham hpq ⟨rfl, rfl⟩
  have hwp : w = p := he.2.1
  rw [hwp, hp3] at hw2
  omega

private theorem low_pair_excluded_by_fixed_pair
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {a s t q : V} (hsR : s ∈ R) (hq3 : G.degree q = 3)
    (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
    (hsq : G.Adj s q) (haq : G.Adj a q) (hfixed : lowPair G a t) :
    ¬ lowPair G s t := by
  rcases hfixed with ⟨l, hl2, hal, htl⟩
  have hNl : G.neighborFinset l = {a, t} := by
    have hsub : ({a, t} : Finset V) ⊆ G.neighborFinset l := by
      intro y hy
      rcases Finset.mem_insert.mp hy with hy | hy
      · subst y
        exact (G.mem_neighborFinset _ _).mpr hal.symm
      · have hyt := Finset.mem_singleton.mp hy
        subst y
        exact (G.mem_neighborFinset _ _).mpr htl.symm
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    simp [SimpleGraph.card_neighborFinset_eq_degree, hl2, hat]
  rintro ⟨w, hw2, hsw, htw⟩
  have hwl : w ≠ l := by
    intro he
    have hsN : s ∈ G.neighborFinset l :=
      (G.mem_neighborFinset _ _).mpr (by simpa only [he] using hsw.symm)
    rw [hNl] at hsN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsN
    exact hsN.elim (fun h => has h.symm) hst
  have hql : q ≠ l := by intro he; rw [← he, hq3] at hl2; omega
  have he := three_walk_endpoint_injective hpart.symm hg hsR hsR
    hsw htw.symm htl hsq haq.symm hal hst hwl has.symm hql ⟨rfl, rfl⟩
  have hwq : w = q := he.2.1
  rw [hwq, hq3] at hw2
  omega

private theorem coverage_forces_low_pair
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {x t a b c p q r : V}
    (hN : G.neighborFinset x = {a, b, c})
    (hc2 : G.degree c = 2)
    (haH : degreeThree G (G.neighborFinset a) = {x, q})
    (hbH : degreeThree G (G.neighborFinset b) = {x, r})
    (hcH : degreeThree G (G.neighborFinset c) = {x, p})
    (hxt : ¬ G.Adj x t) (hpt : ¬ G.Adj p t)
    (hqt : ¬ G.Adj q t) (hrt : ¬ G.Adj r t)
    (hcover : G.Adj x t ∨
      ∃ y w, G.Adj x y ∧ G.Adj y w ∧ G.Adj w t ∧ x ≠ w ∧ y ≠ t) :
    lowPair G a t ∨ lowPair G b t := by
  rcases hcover with hxt' | ⟨y, w, hxy, hyw, hwt, hxw, _⟩
  · exact False.elim (hxt hxt')
  have hy : y ∈ ({a, b, c} : Finset V) := by
    rw [← hN]
    exact (G.mem_neighborFinset _ _).mpr hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  have high_case {s j : V} (hsH : degreeThree G (G.neighborFinset s) = {x, j})
      (hsw : G.Adj s w) (hw3 : G.degree w = 3) (hjt : ¬ G.Adj j t) : False := by
    have hwH : w ∈ degreeThree G (G.neighborFinset s) :=
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hsw, hw3⟩
    rw [hsH] at hwH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwH
    rcases hwH with hw | hw
    · exact hxw hw.symm
    · exact hjt (by simpa only [hw] using hwt)
  rcases hy with hy | hy | hy
  · subst y
    rcases hdeg w with hw2 | hw3
    · exact Or.inl ⟨w, hw2, hyw, hwt.symm⟩
    · exact False.elim (high_case haH hyw hw3 hqt)
  · subst y
    rcases hdeg w with hw2 | hw3
    · exact Or.inr ⟨w, hw2, hyw, hwt.symm⟩
    · exact False.elim (high_case hbH hyw hw3 hrt)
  · subst y
    rcases hdeg w with hw2 | hw3
    · exact False.elim (hlow hyw hc2 hw2)
    · exact False.elim (high_case hcH hyw hw3 hpt)

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairing

end

/- Actual right connector labels extracted from the forced high skeleton. -/

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricHighRightLabels

open SimpleGraph GirthSliceCounting AsymmetricCompressedCore
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricCompressedCore (connector_third connector_card high_neighbor_mem connector_right connector_degree middle_unique)
open private asymmetric_right_type_counts from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity

open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricCompressedCore (high_left high_degree)
open private asymmetric_left_connector_count right_high_neighbor_rigidity from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity
open private degree_parts_union degree_parts_disjoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem connector_high_table {m : V} (hm : m ∈ connectors G R)
    {x y : High G L} (hxy : x ≠ y)
    (hxm : G.Adj x.val m) (hym : G.Adj y.val m) :
    degreeThree G (G.neighborFinset m) = {x.val, y.val} := by
  classical
  have hv : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hs : ({x.val, y.val} : Finset V) ⊆
      degreeThree G (G.neighborFinset m) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw
    · subst w
      exact high_neighbor_mem x hxm
    · subst w
      exact high_neighbor_mem y hym
  apply (Finset.eq_of_subset_of_card_le hs ?_).symm
  simp [connector_card hm, hv]

omit [DecidableEq V] in
private theorem ne_of_high_tables {m n w : V} {S T : Finset V}
    (hm : degreeThree G (G.neighborFinset m) = S)
    (hn : degreeThree G (G.neighborFinset n) = T)
    (hw : w ∈ S) (hnot : w ∉ T) : m ≠ n := by
  intro he
  apply hnot
  rw [← hn, ← he, hm]
  exact hw

/-- The witnesses are actual right vertices; only the original slice hypotheses
are inputs. The original low anchor and all six high labels are retained. -/
private theorem high_right_connector_labels
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1) :
    ∃ z ∈ degreeTwo G R, ∃ u v x1 x2 y1 y2 : High G L,
      G.Adj u.val z ∧ G.Adj v.val z ∧
      ([u, v, x1, x2, y1, y2] : List (High G L)).Nodup ∧
      (∀ w : High G L, w = u ∨ w = v ∨ w = x1 ∨ w = x2 ∨ w = y1 ∨ w = y2) ∧
      ∃ a b c d e f : V,
        a ∈ connectors G R ∧ b ∈ connectors G R ∧
        c ∈ connectors G R ∧ d ∈ connectors G R ∧
        e ∈ connectors G R ∧ f ∈ connectors G R ∧
        ([a, b, c, d, e, f] : List V).Nodup ∧
        connectors G R = {a, b, c, d, e, f} ∧
        degreeThree G (G.neighborFinset a) = {u.val, x1.val} ∧
        degreeThree G (G.neighborFinset b) = {u.val, x2.val} ∧
        degreeThree G (G.neighborFinset c) = {v.val, y1.val} ∧
        degreeThree G (G.neighborFinset d) = {v.val, y2.val} ∧
        degreeThree G (G.neighborFinset e) = {x1.val, y1.val} ∧
        degreeThree G (G.neighborFinset f) = {x2.val, y2.val} := by
  classical
  obtain ⟨z, hz, u, v, x1, x2, y1, y2, huz, hvz, hd, hall,
      hNu, hNv, hNx1, hNx2, hNy1, hNy2⟩ :=
    AsymmetricHighSkeleton.high_skeleton_labels hpart hdeg hlow hg hL hR hL2 hR2
  have hux1 : (core G L R).Adj u x1 :=
    ((core G L R).mem_neighborFinset u x1).mp (by rw [hNu]; simp)
  have hux2 : (core G L R).Adj u x2 :=
    ((core G L R).mem_neighborFinset u x2).mp (by rw [hNu]; simp)
  have hvy1 : (core G L R).Adj v y1 :=
    ((core G L R).mem_neighborFinset v y1).mp (by rw [hNv]; simp)
  have hvy2 : (core G L R).Adj v y2 :=
    ((core G L R).mem_neighborFinset v y2).mp (by rw [hNv]; simp)
  have hx1y1 : (core G L R).Adj x1 y1 :=
    ((core G L R).mem_neighborFinset x1 y1).mp (by rw [hNx1]; simp)
  have hx2y2 : (core G L R).Adj x2 y2 :=
    ((core G L R).mem_neighborFinset x2 y2).mp (by rw [hNx2]; simp)
  obtain ⟨hux1', a, ha, hua, hx1a⟩ := hux1
  obtain ⟨hux2', b, hb, hub, hx2b⟩ := hux2
  obtain ⟨hvy1', c, hc, hvc, hy1c⟩ := hvy1
  obtain ⟨hvy2', d, hdM, hvd, hy2d⟩ := hvy2
  obtain ⟨hx1y1', e, he, hx1e, hy1e⟩ := hx1y1
  obtain ⟨hx2y2', f, hf, hx2f, hy2f⟩ := hx2y2
  have haT := connector_high_table ha hux1' hua hx1a
  have hbT := connector_high_table hb hux2' hub hx2b
  have hcT := connector_high_table hc hvy1' hvc hy1c
  have hdT := connector_high_table hdM hvy2' hvd hy2d
  have heT := connector_high_table he hx1y1' hx1e hy1e
  have hfT := connector_high_table hf hx2y2' hx2f hy2f
  have hx1u : x1.val ≠ u.val := fun h => hux1' (Subtype.ext h.symm)
  have hy1v : y1.val ≠ v.val := fun h => hvy1' (Subtype.ext h.symm)
  have hdv : ([u.val, v.val, x1.val, x2.val, y1.val, y2.val] : List V).Nodup :=
    hd.map Subtype.val_injective
  simp only [List.nodup_cons, List.mem_cons,
    List.not_mem_nil, List.nodup_nil, not_or, not_false_eq_true, and_true] at hdv
  have hab : a ≠ b := ne_of_high_tables (w := x1.val) haT hbT (by simp) (by simp_all)
  have hac : a ≠ c := ne_of_high_tables (w := u.val) haT hcT (by simp) (by simp_all)
  have had : a ≠ d := ne_of_high_tables (w := u.val) haT hdT (by simp) (by simp_all)
  have hae : a ≠ e := ne_of_high_tables (w := u.val) haT heT (by simp) (by simp_all)
  have haf : a ≠ f := ne_of_high_tables (w := u.val) haT hfT (by simp) (by simp_all)
  have hbc : b ≠ c := ne_of_high_tables (w := u.val) hbT hcT (by simp) (by simp_all)
  have hbd : b ≠ d := ne_of_high_tables (w := u.val) hbT hdT (by simp) (by simp_all)
  have hbe : b ≠ e := ne_of_high_tables (w := u.val) hbT heT (by simp) (by simp_all)
  have hbf : b ≠ f := ne_of_high_tables (w := u.val) hbT hfT (by simp) (by simp_all)
  have hcd : c ≠ d := ne_of_high_tables (w := y1.val) hcT hdT (by simp) (by simp_all)
  have hce : c ≠ e := ne_of_high_tables (w := v.val) hcT heT (by simp) (by simp_all)
  have hcf : c ≠ f := ne_of_high_tables (w := v.val) hcT hfT (by simp) (by simp_all)
  have hde : d ≠ e := ne_of_high_tables (w := v.val) hdT heT (by simp) (by simp_all)
  have hdf : d ≠ f := ne_of_high_tables (w := v.val) hdT hfT (by simp) (by simp_all)
  have hef : e ≠ f := ne_of_high_tables (w := x1.val) heT hfT (by simp) (by simp_all)
  have hright : ([a, b, c, d, e, f] : List V).Nodup := by
    simp [List.nodup_cons, hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef]
  have hsix : ({a, b, c, d, e, f} : Finset V).card = 6 := by
    simp [hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef]
  have hsub : ({a, b, c, d, e, f} : Finset V) ⊆ connectors G R := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hdM
    · exact he
    · exact hf
  have hcount : (connectors G R).card = 6 :=
    (asymmetric_right_type_counts hpart hdeg hlow hg hL hR hL2 hR2).1
  have hM : connectors G R = {a, b, c, d, e, f} := by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    omega
  exact ⟨z, hz, u, v, x1, x2, y1, y2, huz, hvz, hd, hall,
    a, b, c, d, e, f, ha, hb, hc, hdM, he, hf, hright, hM,
    haT, hbT, hcT, hdT, heT, hfT⟩

private theorem stub_neighbor_table_three {x m n s : V}
    (hx : G.degree x = 3) (hmn : m ≠ n) (hms : m ≠ s) (hns : n ≠ s)
    (hm : G.Adj x m) (hn : G.Adj x n) (hs : G.Adj x s) :
    G.neighborFinset x = {m, n, s} := by
  have hsub : ({m, n, s} : Finset V) ⊆ G.neighborFinset x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr hm
    · exact (G.mem_neighborFinset _ _).mpr hn
    · exact (G.mem_neighborFinset _ _).mpr hs
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  simp [G.card_neighborFinset_eq_degree, hx, hmn, hms, hns]

private theorem third_neighbor {x m n : V} (hx : G.degree x = 3)
    (hmn : m ≠ n) (hm : G.Adj x m) (hn : G.Adj x n) :
    ∃ s, s ≠ m ∧ s ≠ n ∧ G.neighborFinset x = {m, n, s} := by
  have hsub : ({m, n} : Finset V) ⊆ G.neighborFinset x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr hm
    · exact (G.mem_neighborFinset _ _).mpr hn
  have hdiff : (G.neighborFinset x \ {m, n}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, G.card_neighborFinset_eq_degree, hx]
    simp [hmn]
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hdiff
  have hsD : s ∈ G.neighborFinset x \ {m, n} := by rw [hs]; simp
  obtain ⟨hsN, hsnot⟩ := Finset.mem_sdiff.mp hsD
  have hsm : s ≠ m := by intro h; apply hsnot; simp [h]
  have hsn : s ≠ n := by intro h; apply hsnot; simp [h]
  exact ⟨s, hsm, hsn, stub_neighbor_table_three hx hmn hsm.symm hsn.symm
    hm hn ((G.mem_neighborFinset _ _).mp hsN)⟩

omit [DecidableEq V] in
private theorem stub_actual_saturation
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1) :
    15 * (degreeThree G L).card = (degreeThree G L).card * R.card +
      2 * (degreeThree G R).card + 4 * (degreeTwo G R).card := by
  have hLc := congrArg Finset.card (degree_parts_union hdeg L)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint L)] at hLc
  have hRc := congrArg Finset.card (degree_parts_union hdeg R)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint R)] at hRc
  have hL3 : (degreeThree G L).card = 6 := by omega
  have hR3 : (degreeThree G R).card = 10 := by omega
  rw [hL3, hR, hR3, hR2]

private theorem stub_of_two_connectors
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1)
    (x : High G L) {z m n : V} (hz : z ∈ degreeTwo G R)
    (hxz : ¬ G.Adj x.val z) (hm : m ∈ connectors G R)
    (hn : n ∈ connectors G R) (hmn : m ≠ n)
    (hxm : G.Adj x.val m) (hxn : G.Adj x.val n) :
    ∃ s, s ∈ R ∧ G.degree s = 3 ∧ s ∉ connectors G R ∧
      G.neighborFinset x.val = {m, n, s} ∧
      degreeThree G (G.neighborFinset s) = {x.val} := by
  obtain ⟨s, hsm, hsn, hNx⟩ := third_neighbor (high_degree x) hmn hxm hxn
  have hxs : G.Adj x.val s := (G.mem_neighborFinset _ _).mp (by rw [hNx]; simp)
  have hsR : s ∈ R := hpart.mem_of_mem_adj (high_left x) hxs
  have hrowc : ((connectors G R).filter fun t => G.Adj x.val t).card = 2 := by
    rw [connector_filter_eq hpart x]
    exact asymmetric_left_connector_count hpart hdeg hlow hg hL hR hL2 hR2 x.property
  have hrowSub : ({m, n} : Finset V) ⊆
      (connectors G R).filter (fun t => G.Adj x.val t) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hm, hxm⟩
    · exact Finset.mem_filter.mpr ⟨hn, hxn⟩
  have hrow : (connectors G R).filter (fun t => G.Adj x.val t) = {m, n} := by
    apply (Finset.eq_of_subset_of_card_le hrowSub ?_).symm
    simp [hrowc, hmn]
  have hsM : s ∉ connectors G R := by
    intro hsM
    have hsrow := Finset.mem_filter.mpr ⟨hsM, hxs⟩
    rw [hrow] at hsrow
    simp [hsm, hsn] at hsrow
  have hloweq : degreeTwo G R = {z} := by
    apply (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hz) ?_).symm
    simp [hR2]
  have hs3 : G.degree s = 3 := by
    rcases hdeg s with hs2 | hs3
    · have hslo : s ∈ degreeTwo G R := Finset.mem_filter.mpr ⟨hsR, hs2⟩
      rw [hloweq] at hslo
      have hsz : s = z := Finset.mem_singleton.mp hslo
      exact False.elim (hxz (by simpa only [hsz] using hxs))
    · exact hs3
  have hsH : s ∈ degreeThree G R := Finset.mem_filter.mpr ⟨hsR, hs3⟩
  have hsat := stub_actual_saturation hdeg hL hR hL2 hR2
  have hsg : (degreeThree G (G.neighborFinset s)).card = 1 := by
    rcases right_high_neighbor_rigidity hpart hdeg hlow hg hsat hsH with h1 | h2
    · exact h1
    · exact False.elim (hsM (Finset.mem_filter.mpr ⟨hsH, h2⟩))
  have hhigh : degreeThree G (G.neighborFinset s) = {x.val} := by
    apply (Finset.eq_of_subset_of_card_le
      (Finset.singleton_subset_iff.mpr (high_neighbor_mem x hxs)) ?_).symm
    simp [hsg]
  exact ⟨s, hsR, hs3, hsM, hNx, hhigh⟩

omit [DecidableEq V] in
private theorem stub_singleton_ne {s t x y : V}
    (hs : degreeThree G (G.neighborFinset s) = {x})
    (ht : degreeThree G (G.neighborFinset t) = {y}) (hxy : x ≠ y) : s ≠ t := by
  intro hst
  have hx : x ∈ degreeThree G (G.neighborFinset t) := by rw [← hst, hs]; simp
  rw [ht] at hx
  exact hxy (Finset.mem_singleton.mp hx)

private theorem stub_adj_of_high_table {m x y : V}
    (hm : degreeThree G (G.neighborFinset m) = {x, y}) :
    G.Adj x m ∧ G.Adj y m := by
  constructor
  · have hx : x ∈ degreeThree G (G.neighborFinset m) := by rw [hm]; simp
    exact ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hx).1).symm
  · have hy : y ∈ degreeThree G (G.neighborFinset m) := by rw [hm]; simp
    exact ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hy).1).symm

omit [DecidableEq V] in
private theorem stub_low_high_ne {z s : V}
    (hz : G.degree z = 2) (hs : G.degree s = 3) : z ≠ s := by
  intro h
  subst s
  omega

private theorem right_labels_assembly
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1)
    {z a b c d e f : V} (hz : z ∈ degreeTwo G R)
    (u v x1 x2 y1 y2 : High G L)
    (huz : G.Adj u.val z) (hvz : G.Adj v.val z)
    (hhigh : ([u, v, x1, x2, y1, y2] : List (High G L)).Nodup)
    (ha : a ∈ connectors G R) (hb : b ∈ connectors G R)
    (hc : c ∈ connectors G R) (hd : d ∈ connectors G R)
    (he : e ∈ connectors G R) (hf : f ∈ connectors G R)
    (hmiddles : ([a, b, c, d, e, f] : List V).Nodup)
    (hM : connectors G R = {a, b, c, d, e, f})
    (Ta : degreeThree G (G.neighborFinset a) = {u.val, x1.val})
    (Tb : degreeThree G (G.neighborFinset b) = {u.val, x2.val})
    (Tc : degreeThree G (G.neighborFinset c) = {v.val, y1.val})
    (Td : degreeThree G (G.neighborFinset d) = {v.val, y2.val})
    (Te : degreeThree G (G.neighborFinset e) = {x1.val, y1.val})
    (Tf : degreeThree G (G.neighborFinset f) = {x2.val, y2.val}) :
    ∃ X1 X2 Y1 Y2 : V,
      X1 ∈ R ∧ X2 ∈ R ∧ Y1 ∈ R ∧ Y2 ∈ R ∧
      G.degree X1 = 3 ∧ G.degree X2 = 3 ∧ G.degree Y1 = 3 ∧ G.degree Y2 = 3 ∧
      degreeThree G (G.neighborFinset X1) = {x1.val} ∧
      degreeThree G (G.neighborFinset X2) = {x2.val} ∧
      degreeThree G (G.neighborFinset Y1) = {y1.val} ∧
      degreeThree G (G.neighborFinset Y2) = {y2.val} ∧
      G.neighborFinset z = {u.val, v.val} ∧
      G.neighborFinset u.val = {z, a, b} ∧
      G.neighborFinset v.val = {z, c, d} ∧
      G.neighborFinset x1.val = {a, e, X1} ∧
      G.neighborFinset x2.val = {b, f, X2} ∧
      G.neighborFinset y1.val = {c, e, Y1} ∧
      G.neighborFinset y2.val = {d, f, Y2} ∧
      ([z, a, b, c, d, e, f, X1, X2, Y1, Y2] : List V).Nodup ∧
      R = {z, a, b, c, d, e, f, X1, X2, Y1, Y2} := by
  classical
  have hdv : ([u.val, v.val, x1.val, x2.val, y1.val, y2.val] : List V).Nodup :=
    hhigh.map Subtype.val_injective
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    List.nodup_nil, not_or, not_false_eq_true, and_true] at hdv
  obtain ⟨⟨huv, hux1, hux2, huy1, huy2⟩,
    ⟨⟨hvx1, hvx2, hvy1, hvy2⟩,
    ⟨⟨hx1x2, hx1y1, hx1y2⟩, ⟨⟨hx2y1, hx2y2⟩, hy1y2⟩⟩⟩⟩ := hdv
  have hmid := hmiddles
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    List.nodup_nil, not_or, not_false_eq_true, and_true] at hmid
  obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨⟨hbc, hbd, hbe, hbf⟩,
    ⟨⟨hcd, hce, hcf⟩, ⟨⟨hde, hdf⟩, hef⟩⟩⟩⟩ := hmid
  have hzR : z ∈ R := (Finset.mem_filter.mp hz).1
  have hz2 : G.degree z = 2 := (Finset.mem_filter.mp hz).2
  have hNz : G.neighborFinset z = {u.val, v.val} := by
    have hsub : ({u.val, v.val} : Finset V) ⊆ G.neighborFinset z := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact (G.mem_neighborFinset _ _).mpr huz.symm
      · exact (G.mem_neighborFinset _ _).mpr hvz.symm
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    simp [G.card_neighborFinset_eq_degree, hz2, huv]
  have hnz : ∀ w : High G L, w.val ≠ u.val → w.val ≠ v.val → ¬ G.Adj w.val z := by
    intro w hwu hwv hwz
    have hw : w.val ∈ G.neighborFinset z := (G.mem_neighborFinset _ _).mpr hwz.symm
    rw [hNz] at hw
    simp [hwu, hwv] at hw
  have hx1z := hnz x1 (Ne.symm hux1) (Ne.symm hvx1)
  have hx2z := hnz x2 (Ne.symm hux2) (Ne.symm hvx2)
  have hy1z := hnz y1 (Ne.symm huy1) (Ne.symm hvy1)
  have hy2z := hnz y2 (Ne.symm huy2) (Ne.symm hvy2)
  obtain ⟨hua, hx1a⟩ := stub_adj_of_high_table Ta
  obtain ⟨hub, hx2b⟩ := stub_adj_of_high_table Tb
  obtain ⟨hvc, hy1c⟩ := stub_adj_of_high_table Tc
  obtain ⟨hvd, hy2d⟩ := stub_adj_of_high_table Td
  obtain ⟨hx1e, hy1e⟩ := stub_adj_of_high_table Te
  obtain ⟨hx2f, hy2f⟩ := stub_adj_of_high_table Tf
  obtain ⟨X1, hX1R, hX13, hX1M, hNx1, hX1H⟩ :=
    stub_of_two_connectors hpart hdeg hlow hg hL hR hL2 hR2
      x1 hz hx1z ha he hae hx1a hx1e
  obtain ⟨X2, hX2R, hX23, hX2M, hNx2, hX2H⟩ :=
    stub_of_two_connectors hpart hdeg hlow hg hL hR hL2 hR2
      x2 hz hx2z hb hf hbf hx2b hx2f
  obtain ⟨Y1, hY1R, hY13, hY1M, hNy1, hY1H⟩ :=
    stub_of_two_connectors hpart hdeg hlow hg hL hR hL2 hR2
      y1 hz hy1z hc he hce hy1c hy1e
  obtain ⟨Y2, hY2R, hY23, hY2M, hNy2, hY2H⟩ :=
    stub_of_two_connectors hpart hdeg hlow hg hL hR hL2 hR2
      y2 hz hy2z hd hf hdf hy2d hy2f
  have hzm : ∀ m ∈ connectors G R, z ≠ m := by
    intro m hm
    exact stub_low_high_ne hz2 (connector_degree hm)
  have hzM : z ∉ connectors G R := by intro hm; exact hzm z hm rfl
  have hNu : G.neighborFinset u.val = {z, a, b} :=
    stub_neighbor_table_three (high_degree u) (hzm a ha) (hzm b hb) hab huz hua hub
  have hNv : G.neighborFinset v.val = {z, c, d} :=
    stub_neighbor_table_three (high_degree v) (hzm c hc) (hzm d hd) hcd hvz hvc hvd
  have hXX : X1 ≠ X2 := stub_singleton_ne hX1H hX2H hx1x2
  have hXY11 : X1 ≠ Y1 := stub_singleton_ne hX1H hY1H hx1y1
  have hXY12 : X1 ≠ Y2 := stub_singleton_ne hX1H hY2H hx1y2
  have hXY21 : X2 ≠ Y1 := stub_singleton_ne hX2H hY1H hx2y1
  have hXY22 : X2 ≠ Y2 := stub_singleton_ne hX2H hY2H hx2y2
  have hYY : Y1 ≠ Y2 := stub_singleton_ne hY1H hY2H hy1y2
  have hzX1 : z ≠ X1 := stub_low_high_ne hz2 hX13
  have hzX2 : z ≠ X2 := stub_low_high_ne hz2 hX23
  have hzY1 : z ≠ Y1 := stub_low_high_ne hz2 hY13
  have hzY2 : z ≠ Y2 := stub_low_high_ne hz2 hY23
  let S : Finset V := {X1, X2, Y1, Y2}
  have hSc : S.card = 4 := by simp [S, hXX, hXY11, hXY12, hXY21, hXY22, hYY]
  have hSR : S ⊆ R := by
    intro s hs
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact hX1R
    · exact hX2R
    · exact hY1R
    · exact hY2R
  have hdisj : Disjoint (connectors G R) S := by
    apply Finset.disjoint_left.mpr
    intro s hsM hsS
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsS
    rcases hsS with rfl | rfl | rfl | rfl
    · exact hX1M hsM
    · exact hX2M hsM
    · exact hY1M hsM
    · exact hY2M hsM
  have hzS : z ∉ S := by simp [S, hzX1, hzX2, hzY1, hzY2]
  have hMc : (connectors G R).card = 6 :=
    (asymmetric_right_type_counts hpart hdeg hlow hg hL hR hL2 hR2).1
  let J : Finset V := insert z (connectors G R ∪ S)
  have hJc : J.card = 11 := by
    change (insert z (connectors G R ∪ S)).card = 11
    rw [Finset.card_insert_of_notMem (by simp [hzM, hzS]),
      Finset.card_union_of_disjoint hdisj, hMc, hSc]
  have hJR : J ⊆ R := by
    intro s hs
    change s ∈ insert z (connectors G R ∪ S) at hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hzR
    · rcases Finset.mem_union.mp hs with hs | hs
      · exact connector_right hs
      · exact hSR hs
  have hRJ : R = J := by
    apply (Finset.eq_of_subset_of_card_le hJR ?_).symm
    omega
  have hRlabels : R = {z, a, b, c, d, e, f, X1, X2, Y1, Y2} := by
    rw [hRJ]
    dsimp [J, S]
    rw [hM]
    ext w
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    simp only [or_assoc]
  have hlabels : ([z, a, b, c, d, e, f, X1, X2, Y1, Y2] : List V).Nodup := by
    have hznot := hzM
    have hX1not := hX1M
    have hX2not := hX2M
    have hY1not := hY1M
    have hY2not := hY2M
    simp only [hM, Finset.mem_insert, Finset.mem_singleton, not_or] at hznot hX1not hX2not hY1not hY2not
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    grind
  exact ⟨X1, X2, Y1, Y2, hX1R, hX2R, hY1R, hY2R,
    hX13, hX23, hY13, hY23, hX1H, hX2H, hY1H, hY2H,
    hNz, hNu, hNv, hNx1, hNx2, hNy1, hNy2, hlabels, hRlabels⟩


end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricHighRightLabels

end
