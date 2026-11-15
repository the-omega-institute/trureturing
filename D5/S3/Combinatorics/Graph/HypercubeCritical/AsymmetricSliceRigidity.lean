/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Saturated path counts and the six-vertex compressed cycle. -/


import D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
import Batteries.Tactic.OpenPrivate

set_option linter.style.longLine false



/- Single-root nonbacktracking path counts used in the equality-case classification. -/

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity

open scoped BigOperators
open SimpleGraph
open GirthSliceCounting
open private threePaths forwardWeight neighbor_weight_sum neighbor_parts_card
  forwardWeight_add_one one_three_paths_card_le_rectangle one_paths_card_eq_three_mul from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private def rootThreeWeight (G : SimpleGraph V) (x y : V) : ℕ :=
  ∑ w ∈ (G.neighborFinset y).erase x, forwardWeight G y w

private theorem root_three_paths_card (x : V) :
    (threePaths G {x}).card = ∑ y ∈ G.neighborFinset x, rootThreeWeight G x y := by
  let S : Finset (Σ _y : V, Σ _w : V, V) :=
    (G.neighborFinset x).sigma fun y =>
      ((G.neighborFinset y).erase x).sigma fun w => (G.neighborFinset w).erase y
  have hbij : (threePaths G {x}).card = S.card := by
    apply Finset.card_bij (fun q _ => ⟨q.first, q.second, q.endpoint⟩)
    · intro q hq
      have hp : q.root = x ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
          G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
        simpa [threePaths] using hq
      apply Finset.mem_sigma.mpr
      refine ⟨?_, Finset.mem_sigma.mpr ⟨?_, ?_⟩⟩
      · exact (G.mem_neighborFinset _ _).mpr (hp.1 ▸ hp.2.1)
      · exact Finset.mem_erase.mpr ⟨by simpa [hp.1] using hp.2.2.2.2.1.symm,
          (G.mem_neighborFinset _ _).mpr hp.2.2.1⟩
      · exact Finset.mem_erase.mpr ⟨hp.2.2.2.2.2.symm,
          (G.mem_neighborFinset _ _).mpr hp.2.2.2.1⟩
    · intro q hq q' hq' he
      have hr : q.root = x := by simpa [threePaths] using (Finset.mem_filter.mp hq).2.1
      have hr' : q'.root = x := by simpa [threePaths] using (Finset.mem_filter.mp hq').2.1
      have hf := congrArg (fun t : Σ _y : V, Σ _w : V, V => t.1) he
      have hs := congrArg (fun t : Σ _y : V, Σ _w : V, V => t.2.1) he
      have hz := congrArg (fun t : Σ _y : V, Σ _w : V, V => t.2.2) he
      cases q
      cases q'
      simp_all
    · rintro ⟨y, w, z⟩ hx
      rcases Finset.mem_sigma.mp hx with ⟨hy, hx⟩
      rcases Finset.mem_sigma.mp hx with ⟨hw, hz⟩
      have hw' := Finset.mem_erase.mp hw
      have hz' := Finset.mem_erase.mp hz
      refine ⟨⟨x, y, w, z⟩, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, Finset.mem_singleton_self x,
        (G.mem_neighborFinset _ _).mp hy, (G.mem_neighborFinset _ _).mp hw'.2,
        (G.mem_neighborFinset _ _).mp hz'.2, hw'.1.symm, hz'.1.symm⟩
  simpa [S, Finset.card_sigma, rootThreeWeight, forwardWeight] using hbij

private theorem root_weight_add_two
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    {x y : V} (hx : G.degree x = 3) (hxy : G.Adj x y) :
    rootThreeWeight G x y + 2 =
      (degreeTwo G (G.neighborFinset y)).card +
        2 * (degreeThree G (G.neighborFinset y)).card := by
  have hmem : x ∈ G.neighborFinset y := (G.mem_neighborFinset _ _).mpr hxy.symm
  have hfw : forwardWeight G y x = 2 := by
    have h := forwardWeight_add_one (G := G) hmem
    omega
  have he := Finset.sum_erase_add (G.neighborFinset y) (forwardWeight G y) hmem
  simpa [rootThreeWeight, hfw, neighbor_weight_sum hdeg y] using he

private theorem root_paths_card_of_coverage
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {x : V} (hxL : x ∈ L) (hx : G.degree x = 3)
    (hcover : ∀ z ∈ R, G.Adj x z ∨
      ∃ y w, G.Adj x y ∧ G.Adj y w ∧ G.Adj w z ∧ x ≠ w ∧ y ≠ z) :
    3 + (threePaths G {x}).card = R.card := by
  have hroots : ({x} : Finset V) ⊆ L := by simpa
  have hu := one_three_paths_card_le_rectangle {x} hroots hpart hg
  rw [one_paths_card_eq_three_mul _ (by simpa using hx)] at hu
  simp only [Finset.card_singleton, mul_one, one_mul] at hu
  have hsub : R ⊆ G.neighborFinset x ∪
      (threePaths G {x}).image (fun q => q.endpoint) := by
    intro z hz
    rcases hcover z hz with hadj | ⟨y, w, hxy, hyw, hwz, hxw, hyz⟩
    · exact Finset.mem_union.mpr (Or.inl ((G.mem_neighborFinset _ _).mpr hadj))
    · apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_image.mpr
      refine ⟨⟨x, y, w, z⟩, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, Finset.mem_singleton_self x, hxy, hyw, hwz, hxw, hyz⟩
  have hl : R.card ≤ 3 + (threePaths G {x}).card := calc
    R.card ≤ (G.neighborFinset x ∪
        (threePaths G {x}).image (fun q => q.endpoint)).card := Finset.card_le_card hsub
    _ ≤ (G.neighborFinset x).card +
        ((threePaths G {x}).image (fun q => q.endpoint)).card := Finset.card_union_le _ _
    _ ≤ 3 + (threePaths G {x}).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hx]
      exact Nat.add_le_add_left (Finset.card_image_le) 3
  omega

private theorem root_weight_low
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {x y : V} (hx : G.degree x = 3) (hxy : G.Adj x y) (hy : G.degree y = 2) :
    rootThreeWeight G x y = 2 := by
  have hj : (degreeTwo G (G.neighborFinset y)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hm := Finset.mem_filter.mp hw
    exact hlow ((G.mem_neighborFinset _ _).mp hm.1) hy hm.2
  have hp := neighbor_parts_card hdeg y
  have he := root_weight_add_two hdeg hx hxy
  omega

private theorem root_weight_high
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    {x y : V} (hx : G.degree x = 3) (hxy : G.Adj x y) (hy : G.degree y = 3) :
    rootThreeWeight G x y = 1 + (degreeThree G (G.neighborFinset y)).card := by
  have hp := neighbor_parts_card hdeg y
  have he := root_weight_add_two hdeg hx hxy
  omega

private theorem root_three_paths_two_connectors
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {x : V} (hx : G.degree x = 3)
    (hhigh : ∀ y ∈ G.neighborFinset x, G.degree y = 3 →
      (degreeThree G (G.neighborFinset y)).card = 1 ∨
        (degreeThree G (G.neighborFinset y)).card = 2)
    (hpaths : (threePaths G {x}).card = 8) :
    ((G.neighborFinset x).filter fun y =>
      G.degree y = 3 ∧ (degreeThree G (G.neighborFinset y)).card = 2).card = 2 := by
  have hw (y : V) (hy : y ∈ G.neighborFinset x) :
      rootThreeWeight G x y = 2 +
        if G.degree y = 3 ∧ (degreeThree G (G.neighborFinset y)).card = 2 then 1 else 0 := by
    have hxy := (G.mem_neighborFinset _ _).mp hy
    rcases hdeg y with hy2 | hy3
    · have he := root_weight_low hdeg hlow hx hxy hy2
      have hn : G.degree y ≠ 3 := by omega
      simp [he, hn]
    · have he := root_weight_high hdeg hx hxy hy3
      rcases hhigh y hy hy3 with hg | hg <;> simp [he, hy3, hg]
  have hs := Finset.sum_congr (s₁ := G.neighborFinset x) rfl hw
  have hid := root_three_paths_card (G := G) x
  rw [hs, Finset.sum_add_distrib] at hid
  simp only [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hid
  have hb : (∑ y ∈ G.neighborFinset x,
      if G.degree y = 3 ∧ (degreeThree G (G.neighborFinset y)).card = 2 then 1 else 0) =
      ((G.neighborFinset x).filter fun y =>
        G.degree y = 3 ∧ (degreeThree G (G.neighborFinset y)).card = 2).card := by
    simp
  rw [hb] at hid
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity

end

/- Equality in the cubic slice bound forces local rigidity and endpoint coverage. -/

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity

open scoped BigOperators
open SimpleGraph
open D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

open private threePaths onePaths oneEndpoint endpoint localThreeCount
  local_three_count_bound local_three_count_identity neighbor_parts_card
  sum_high_neighbors three_paths_card_eq_sum_local middle_penalty_sum
  high_root_three_paths_bound degree_parts_union degree_parts_disjoint sum_degree_parts
  one_paths_card_eq_three_mul endpoint_images_disjoint three_endpoint_injective
  three_endpoint_mem_rectangle
  from D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity (root_paths_card_of_coverage root_three_paths_two_connectors)

private lemma saturation_count_equalities
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hsat : 15 * (degreeThree G L).card = (degreeThree G L).card * R.card +
      2 * (degreeThree G R).card + 4 * (degreeTwo G R).card) :
    (12 * (degreeThree G L).card =
      (threePaths G (degreeThree G L)).card +
        4 * (degreeTwo G R).card + 2 * (degreeThree G R).card) ∧
    (3 * (degreeThree G L).card + (threePaths G (degreeThree G L)).card =
      (degreeThree G L).card * R.card) := by
  have hsum := Finset.sum_le_sum (s := R)
    (fun y _ => local_three_count_bound hdeg hlow y)
  have hcount : 12 * (degreeThree G L).card ≤
      (threePaths G (degreeThree G L)).card +
        4 * (degreeTwo G R).card + 2 * (degreeThree G R).card := by
    calc
      12 * (degreeThree G L).card = 4 * (3 * (degreeThree G L).card) := by omega
      _ = ∑ y ∈ R, 4 * (degreeThree G (G.neighborFinset y)).card := by
        rw [← sum_high_neighbors hpart, Finset.mul_sum]
      _ ≤ ∑ y ∈ R, (localThreeCount G y + if G.degree y = 2 then 4 else 2) := hsum
      _ = _ := by
        rw [Finset.sum_add_distrib, ← three_paths_card_eq_sum_local hpart,
          middle_penalty_sum hdeg R]
        omega
  have hgeom := high_root_three_paths_bound hpart hg
  constructor <;> omega

private lemma saturation_local_equality
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hsat : 15 * (degreeThree G L).card = (degreeThree G L).card * R.card +
      2 * (degreeThree G R).card + 4 * (degreeTwo G R).card)
    {y : V} (hy : y ∈ R) :
    4 * (degreeThree G (G.neighborFinset y)).card =
      localThreeCount G y + if G.degree y = 2 then 4 else 2 := by
  have hcount := (saturation_count_equalities hpart hdeg hlow hg hsat).1
  have htotal :
      (∑ y ∈ R, 4 * (degreeThree G (G.neighborFinset y)).card) =
        ∑ y ∈ R, (localThreeCount G y + if G.degree y = 2 then 4 else 2) := by
    calc
      (∑ y ∈ R, 4 * (degreeThree G (G.neighborFinset y)).card) =
          12 * (degreeThree G L).card := by
        rw [← Finset.mul_sum, sum_high_neighbors hpart]
        omega
      _ = _ := by
        rw [Finset.sum_add_distrib, ← three_paths_card_eq_sum_local hpart,
          middle_penalty_sum hdeg R]
        omega
  have hle := local_three_count_bound hdeg hlow y
  by_contra hne
  have hlt : 4 * (degreeThree G (G.neighborFinset y)).card <
      localThreeCount G y + if G.degree y = 2 then 4 else 2 := by omega
  have hstrict :
      (∑ y ∈ R, 4 * (degreeThree G (G.neighborFinset y)).card) <
        ∑ y ∈ R, (localThreeCount G y + if G.degree y = 2 then 4 else 2) :=
    Finset.sum_lt_sum (fun y _ => local_three_count_bound hdeg hlow y) ⟨y, hy, hlt⟩
  omega

omit [DecidableEq V] in
private theorem right_high_neighbor_rigidity
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hsat : 15 * (degreeThree G L).card = (degreeThree G L).card * R.card +
      2 * (degreeThree G R).card + 4 * (degreeTwo G R).card)
    {y : V} (hy : y ∈ degreeThree G R) :
    (degreeThree G (G.neighborFinset y)).card = 1 ∨
      (degreeThree G (G.neighborFinset y)).card = 2 := by
  classical
  have hyR := (Finset.mem_filter.mp hy).1
  have hy3 : G.degree y = 3 := (Finset.mem_filter.mp hy).2
  have hy2 : G.degree y ≠ 2 := by omega
  have heq := saturation_local_equality hpart hdeg hlow hg hsat hyR
  rw [ite_eq_right hy2] at heq
  let g := (degreeThree G (G.neighborFinset y)).card
  let j := (degreeTwo G (G.neighborFinset y)).card
  have hd : j + g = 3 := (neighbor_parts_card hdeg y).trans hy3
  have hi : localThreeCount G y + 2 * g = g * (j + 2 * g) :=
    local_three_count_identity hdeg y
  have hm := congrArg (fun n : ℕ => g * n) hd
  have he : localThreeCount G y + j * g = 4 * g := by nlinarith
  have hp : j * g = 2 := by
    change 4 * g = localThreeCount G y + 2 at heq
    omega
  change g = 1 ∨ g = 2
  have hc : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 := by omega
  rcases hc with h0 | h1 | h2 | h3
  · rw [h0] at hp
    omega
  · exact Or.inl h1
  · exact Or.inr h2
  · have hj : j = 0 := by omega
    rw [hj] at hp
    omega

private lemma saturation_endpoint_union
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hsat : 15 * (degreeThree G L).card = (degreeThree G L).card * R.card +
      2 * (degreeThree G R).card + 4 * (degreeTwo G R).card) :
    ((onePaths G (degreeThree G L)).image oneEndpoint) ∪
      ((threePaths G (degreeThree G L)).image endpoint) =
        (degreeThree G L).product R := by
  have hgeom := (saturation_count_equalities hpart hdeg hlow hg hsat).2
  have hroots : degreeThree G L ⊆ L := Finset.filter_subset _ _
  have hone : Function.Injective (oneEndpoint : (Σ a : V, V) → V × V) := by
    intro x y h
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl
  have hthree : Set.InjOn endpoint
      (↑(threePaths G (degreeThree G L)) : Set (ThreeStep V)) := by
    intro q hq q' hq' he
    have hp : q.root ∈ degreeThree G L ∧ G.Adj q.root q.first ∧
        G.Adj q.first q.second ∧ G.Adj q.second q.endpoint ∧
        q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
      simpa [threePaths] using hq
    have hp' : q'.root ∈ degreeThree G L ∧ G.Adj q'.root q'.first ∧
        G.Adj q'.first q'.second ∧ G.Adj q'.second q'.endpoint ∧
        q'.root ≠ q'.second ∧ q'.first ≠ q'.endpoint := by
      simpa [threePaths] using hq'
    exact three_endpoint_injective hpart hg ⟨hroots hp.1, hp.2⟩
      ⟨hroots hp'.1, hp'.2⟩ he
  have hsub : ((onePaths G (degreeThree G L)).image oneEndpoint) ∪
      ((threePaths G (degreeThree G L)).image endpoint) ⊆
        (degreeThree G L).product R := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hqr : q.1 ∈ degreeThree G L ∧ G.Adj q.1 q.2 := by
        simpa [onePaths] using hq
      have hR := hpart.mem_of_mem_adj (hroots hqr.1) hqr.2
      exact Finset.mem_product.mpr ⟨hqr.1, hR⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hp : q.root ∈ degreeThree G L ∧ G.Adj q.root q.first ∧
          G.Adj q.first q.second ∧ G.Adj q.second q.endpoint ∧
          q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
        simpa [threePaths] using hq
      have hrect := three_endpoint_mem_rectangle hpart ⟨hroots hp.1, hp.2⟩
      exact Finset.mem_product.mpr ⟨hp.1, (Finset.mem_product.mp hrect).2⟩
  have hcard :
      (((onePaths G (degreeThree G L)).image oneEndpoint) ∪
        ((threePaths G (degreeThree G L)).image endpoint)).card =
          ((degreeThree G L).product R).card := by
    rw [Finset.card_union_of_disjoint
      (endpoint_images_disjoint (degreeThree G L) hroots hpart hg),
      Finset.card_image_of_injective _ hone, Finset.card_image_of_injOn hthree,
      one_paths_card_eq_three_mul _ (by
        intro v hv
        exact (Finset.mem_filter.mp hv).2)]
    exact hgeom.trans (Finset.card_product (degreeThree G L) R).symm
  exact Finset.eq_of_subset_of_card_le hsub hcard.ge

omit [DecidableEq V] in
private theorem high_root_endpoint_coverage
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hsat : 15 * (degreeThree G L).card = (degreeThree G L).card * R.card +
      2 * (degreeThree G R).card + 4 * (degreeTwo G R).card)
    {a z : V} (ha : a ∈ degreeThree G L) (hz : z ∈ R) :
    G.Adj a z ∨ ∃ b c, G.Adj a b ∧ G.Adj b c ∧ G.Adj c z ∧ a ≠ c ∧ b ≠ z := by
  classical
  have hU := saturation_endpoint_union hpart hdeg hlow hg hsat
  have hm : (a, z) ∈ ((onePaths G (degreeThree G L)).image oneEndpoint) ∪
      ((threePaths G (degreeThree G L)).image endpoint) := by
    rw [hU]
    exact Finset.mem_product.mpr ⟨ha, hz⟩
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨q, hq, hqz⟩ := Finset.mem_image.mp hm
    have hp : q.1 ∈ degreeThree G L ∧ G.Adj q.1 q.2 := by
      simpa [onePaths] using hq
    have he : q.1 = a ∧ q.2 = z := Prod.mk.inj hqz
    exact Or.inl (by simpa only [he.1, he.2] using hp.2)
  · obtain ⟨q, hq, hqz⟩ := Finset.mem_image.mp hm
    have hp : q.root ∈ degreeThree G L ∧ G.Adj q.root q.first ∧
        G.Adj q.first q.second ∧ G.Adj q.second q.endpoint ∧
        q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
      simpa [threePaths] using hq
    have he : q.root = a ∧ q.endpoint = z := Prod.mk.inj hqz
    rcases hp with ⟨_, hab, hbc, hcz, hac, hbz⟩
    refine Or.inr ⟨q.first, q.second, ?_, hbc, ?_, ?_, ?_⟩
    · simpa only [he.1] using hab
    · simpa only [he.2] using hcz
    · simpa only [he.1] using hac
    · simpa only [he.2] using hbz

omit [DecidableEq V] in
private lemma low_vertex_high_neighbor_card
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {y : V} (hy : G.degree y = 2) :
    (degreeThree G (G.neighborFinset y)).card = 2 := by
  classical
  have hempty : degreeTwo G (G.neighborFinset y) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hm := Finset.mem_filter.mp hw
    exact hlow ((G.mem_neighborFinset _ _).mp hm.1) hy hm.2
  have hp := neighbor_parts_card hdeg y
  rw [hempty, Finset.card_empty, hy] at hp
  omega

omit [DecidableEq V] in
private theorem asymmetric_right_type_counts
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1) :
    ((degreeThree G R).filter
      (fun y => (degreeThree G (G.neighborFinset y)).card = 2)).card = 6 ∧
    ((degreeThree G R).filter
      (fun y => (degreeThree G (G.neighborFinset y)).card = 1)).card = 4 := by
  classical
  have hLc := congrArg Finset.card (degree_parts_union hdeg L)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint L)] at hLc
  have hRc := congrArg Finset.card (degree_parts_union hdeg R)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint R)] at hRc
  have hL3 : (degreeThree G L).card = 6 := by omega
  have hR3 : (degreeThree G R).card = 10 := by omega
  have hsat : 15 * (degreeThree G L).card = (degreeThree G L).card * R.card +
      2 * (degreeThree G R).card + 4 * (degreeTwo G R).card := by
    rw [hL3, hR, hR3, hR2]
  let g : V → ℕ := fun y => (degreeThree G (G.neighborFinset y)).card
  let S1 : Finset V := (degreeThree G R).filter (fun y => g y = 1)
  let S2 : Finset V := (degreeThree G R).filter (fun y => g y = 2)
  have hdich : ∀ y ∈ degreeThree G R, g y = 1 ∨ g y = 2 := by
    intro y hy
    exact right_high_neighbor_rigidity hpart hdeg hlow hg hsat hy
  have hunion : S1 ∪ S2 = degreeThree G R := by
    ext y
    simp only [S1, S2, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    · intro hy
      rcases hdich y hy with h1 | h2
      · exact Or.inl ⟨hy, h1⟩
      · exact Or.inr ⟨hy, h2⟩
  have hdisj : Disjoint S1 S2 := by
    apply Finset.disjoint_left.mpr
    intro y hy1 hy2
    have h1 : g y = 1 := (Finset.mem_filter.mp hy1).2
    have h2 : g y = 2 := (Finset.mem_filter.mp hy2).2
    omega
  have hcards : S1.card + S2.card = 10 := by
    calc
      S1.card + S2.card = (S1 ∪ S2).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ = 10 := by rw [hunion, hR3]
  have hlow_sum : (∑ y ∈ degreeTwo G R, g y) = 2 := by
    calc
      (∑ y ∈ degreeTwo G R, g y) = ∑ _y ∈ degreeTwo G R, 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact low_vertex_high_neighbor_card hdeg hlow (Finset.mem_filter.mp hy).2
      _ = 2 := by simp [hR2]
  have hsum1 : (∑ y ∈ S1, g y) = S1.card := by
    calc
      (∑ y ∈ S1, g y) = ∑ _y ∈ S1, 1 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (Finset.mem_filter.mp hy).2
      _ = S1.card := by simp
  have hsum2 : (∑ y ∈ S2, g y) = 2 * S2.card := by
    calc
      (∑ y ∈ S2, g y) = ∑ _y ∈ S2, 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (Finset.mem_filter.mp hy).2
      _ = 2 * S2.card := by simp [Nat.mul_comm]
  have hhigh_sum : (∑ y ∈ degreeThree G R, g y) = S1.card + 2 * S2.card := by
    calc
      (∑ y ∈ degreeThree G R, g y) = ∑ y ∈ S1 ∪ S2, g y := by rw [hunion]
      _ = (∑ y ∈ S1, g y) + ∑ y ∈ S2, g y := Finset.sum_union hdisj
      _ = S1.card + 2 * S2.card := by rw [hsum1, hsum2]
  have htotal : (∑ y ∈ R, g y) = 18 := by
    calc
      (∑ y ∈ R, g y) = 3 * (degreeThree G L).card := sum_high_neighbors hpart
      _ = 18 := by rw [hL3]
  have hsplit := sum_degree_parts hdeg R g
  rw [hlow_sum, hhigh_sum] at hsplit
  have hweighted : S1.card + 2 * S2.card = 16 := by omega
  change S2.card = 6 ∧ S1.card = 4
  constructor <;> omega

omit [DecidableEq V] in
private theorem asymmetric_left_connector_count
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1)
    {x : V} (hx : x ∈ degreeThree G L) :
    ((G.neighborFinset x).filter fun y =>
      G.degree y = 3 ∧ (degreeThree G (G.neighborFinset y)).card = 2).card = 2 := by
  classical
  have hLc := congrArg Finset.card (degree_parts_union hdeg L)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint L)] at hLc
  have hRc := congrArg Finset.card (degree_parts_union hdeg R)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint R)] at hRc
  have hL3 : (degreeThree G L).card = 6 := by omega
  have hR3 : (degreeThree G R).card = 10 := by omega
  have hsat : 15 * (degreeThree G L).card = (degreeThree G L).card * R.card +
      2 * (degreeThree G R).card + 4 * (degreeTwo G R).card := by
    rw [hL3, hR, hR3, hR2]
  have hxL := (Finset.mem_filter.mp hx).1
  have hx3 := (Finset.mem_filter.mp hx).2
  have hcov : ∀ z ∈ R, G.Adj x z ∨
      ∃ y w, G.Adj x y ∧ G.Adj y w ∧ G.Adj w z ∧ x ≠ w ∧ y ≠ z := by
    intro z hz
    exact high_root_endpoint_coverage hpart hdeg hlow hg hsat hx hz
  have hc := root_paths_card_of_coverage hpart hg hxL hx3 hcov
  have hp : (threePaths G {x}).card = 8 := by omega
  apply root_three_paths_two_connectors hdeg hlow hx3 _ hp
  intro y hy hy3
  exact right_high_neighbor_rigidity hpart hdeg hlow hg hsat
    (Finset.mem_filter.mpr ⟨hpart.mem_of_mem_adj hxL
      ((G.mem_neighborFinset _ _).mp hy), hy3⟩)


end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity

end

/- A distinguished nonedge with no common neighbor
labels a triangle-free two-regular graph on six vertices without cycle APIs. -/

set_option autoImplicit false

namespace AsymmetricRigidityCore

open SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (F : SimpleGraph W) [DecidableRel F.Adj]

private theorem neighbors_eq_pair
    (hdeg : ∀ w, F.degree w = 2) {a b c : W}
    (hab : F.Adj a b) (hac : F.Adj a c) (hbc : b ≠ c) :
    F.neighborFinset a = {b, c} := by
  classical
  have hs : ({b, c} : Finset W) ⊆ F.neighborFinset a := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw
    · subst w
      exact (F.mem_neighborFinset a b).mpr hab
    · subst w
      exact (F.mem_neighborFinset a c).mpr hac
  apply (Finset.eq_of_subset_of_card_le hs ?_).symm
  simp [F.card_neighborFinset_eq_degree, hdeg, hbc]

private theorem complete_pairing
    (hdeg : ∀ w, F.degree w = 2)
    (htri : ∀ a b c, F.Adj a b → F.Adj b c → F.Adj c a → False)
    {u v x1 x2 y1 y2 : W}
    (hd : ([u, v, x1, x2, y1, y2] : List W).Nodup)
    (hall : ∀ w, w = u ∨ w = v ∨ w = x1 ∨ w = x2 ∨ w = y1 ∨ w = y2)
    (hNu : F.neighborFinset u = {x1, x2})
    (hNv : F.neighborFinset v = {y1, y2})
    (hcommon : ∀ w, F.Adj u w → F.Adj v w → False)
    (hx1y1 : F.Adj x1 y1) :
    F.neighborFinset x1 = {u, y1} ∧
    F.neighborFinset x2 = {u, y2} ∧
    F.neighborFinset y1 = {v, x1} ∧
    F.neighborFinset y2 = {v, x2} := by
  classical
  have hdist := hd
  simp only [List.nodup_cons, List.mem_cons,
    List.not_mem_nil, List.nodup_nil, not_or, and_true] at hdist
  have hux1 : F.Adj u x1 := (F.mem_neighborFinset u x1).mp (by simp [hNu])
  have hux2 : F.Adj u x2 := (F.mem_neighborFinset u x2).mp (by simp [hNu])
  have hvy1 : F.Adj v y1 := (F.mem_neighborFinset v y1).mp (by simp [hNv])
  have hvy2 : F.Adj v y2 := (F.mem_neighborFinset v y2).mp (by simp [hNv])
  have hNy1 : F.neighborFinset y1 = {v, x1} :=
    neighbors_eq_pair F hdeg hvy1.symm hx1y1.symm (by aesop)
  have hx2y2 : F.Adj x2 y2 := by
    have hc : 1 < (F.neighborFinset x2).card := by
      rw [F.card_neighborFinset_eq_degree, hdeg]
      decide
    obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne hc u
    have hx2w : F.Adj x2 w := (F.mem_neighborFinset x2 w).mp hw
    rcases hall w with hw | hw | hw | hw | hw | hw
    · subst w
      exact False.elim (hwu rfl)
    · subst w
      exact False.elim (hcommon x2 hux2 hx2w.symm)
    · subst w
      exact False.elim (htri u x1 x2 hux1 hx2w.symm hux2.symm)
    · subst w
      exact False.elim ((F.irrefl (v := x2)) hx2w)
    · subst w
      have hm : x2 ∈ F.neighborFinset y1 :=
        (F.mem_neighborFinset y1 x2).mpr hx2w.symm
      rw [hNy1] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      aesop
    · subst w
      exact hx2w
  exact ⟨neighbors_eq_pair F hdeg hux1.symm hx1y1 (by aesop),
    neighbors_eq_pair F hdeg hux2.symm hx2y2 (by aesop),
    hNy1, neighbors_eq_pair F hdeg hvy2.symm hx2y2.symm (by aesop)⟩

/-- The six returned neighbor sets are an exact adjacency table. In particular
the six-vertex graph is the cycle u-x1-y1-v-y2-x2-u. -/
private theorem c6_core_of_distinguished_pair
    (hW : Fintype.card W = 6)
    (hdeg : ∀ w, F.degree w = 2)
    (htri : ∀ a b c, F.Adj a b → F.Adj b c → F.Adj c a → False)
    (u v : W) (huv : u ≠ v) (hnot : ¬ F.Adj u v)
    (hcommon : ∀ w, F.Adj u w → F.Adj v w → False) :
    ∃ x1 x2 y1 y2 : W,
      ([u, v, x1, x2, y1, y2] : List W).Nodup ∧
      (∀ w, w = u ∨ w = v ∨ w = x1 ∨ w = x2 ∨ w = y1 ∨ w = y2) ∧
      F.neighborFinset u = {x1, x2} ∧
      F.neighborFinset v = {y1, y2} ∧
      F.neighborFinset x1 = {u, y1} ∧
      F.neighborFinset x2 = {u, y2} ∧
      F.neighborFinset y1 = {v, x1} ∧
      F.neighborFinset y2 = {v, x2} := by
  classical
  have huc : (F.neighborFinset u).card = 2 := by
    rw [F.card_neighborFinset_eq_degree, hdeg]
  have hvc : (F.neighborFinset v).card = 2 := by
    rw [F.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨x1, x2, hxx, hNu⟩ := Finset.card_eq_two.mp huc
  obtain ⟨y1, y2, hyy, hNv⟩ := Finset.card_eq_two.mp hvc
  have hux1 : F.Adj u x1 := (F.mem_neighborFinset u x1).mp (by simp [hNu])
  have hux2 : F.Adj u x2 := (F.mem_neighborFinset u x2).mp (by simp [hNu])
  have hvy1 : F.Adj v y1 := (F.mem_neighborFinset v y1).mp (by simp [hNv])
  have hvy2 : F.Adj v y2 := (F.mem_neighborFinset v y2).mp (by simp [hNv])
  have hux1n : u ≠ x1 := hux1.ne
  have hux2n : u ≠ x2 := hux2.ne
  have hvy1n : v ≠ y1 := hvy1.ne
  have hvy2n : v ≠ y2 := hvy2.ne
  have hvx1n : v ≠ x1 := by
    intro h
    exact hnot (h.symm ▸ hux1)
  have hvx2n : v ≠ x2 := by
    intro h
    exact hnot (h.symm ▸ hux2)
  have huy1n : u ≠ y1 := by
    intro h
    exact hnot ((h.symm ▸ hvy1).symm)
  have huy2n : u ≠ y2 := by
    intro h
    exact hnot ((h.symm ▸ hvy2).symm)
  have h11 : x1 ≠ y1 := by
    intro h
    exact hcommon x1 hux1 (h.symm ▸ hvy1)
  have h12 : x1 ≠ y2 := by
    intro h
    exact hcommon x1 hux1 (h.symm ▸ hvy2)
  have h21 : x2 ≠ y1 := by
    intro h
    exact hcommon x2 hux2 (h.symm ▸ hvy1)
  have h22 : x2 ≠ y2 := by
    intro h
    exact hcommon x2 hux2 (h.symm ▸ hvy2)
  have hd : ([u, v, x1, x2, y1, y2] : List W).Nodup := by
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil, not_or, and_true]
    tauto
  let A : Finset W := {u, v, x1, x2, y1, y2}
  have hAc : A.card = 6 := by
    simpa [A] using List.toFinset_card_of_nodup hd
  have hAu : A = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ A)
    simp [hW, hAc]
  have hall : ∀ w, w = u ∨ w = v ∨ w = x1 ∨ w = x2 ∨ w = y1 ∨ w = y2 := by
    intro w
    have hw : w ∈ A := by rw [hAu]; exact Finset.mem_univ w
    simpa [A] using hw
  have hxy : F.Adj x1 y1 ∨ F.Adj x1 y2 := by
    have hc : 1 < (F.neighborFinset x1).card := by
      rw [F.card_neighborFinset_eq_degree, hdeg]
      decide
    obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne hc u
    have hx1w : F.Adj x1 w := (F.mem_neighborFinset x1 w).mp hw
    rcases hall w with hw | hw | hw | hw | hw | hw
    · subst w
      exact False.elim (hwu rfl)
    · subst w
      exact False.elim (hcommon x1 hux1 hx1w.symm)
    · subst w
      exact False.elim ((F.irrefl (v := x1)) hx1w)
    · subst w
      exact False.elim (htri u x1 x2 hux1 hx1w hux2.symm)
    · subst w
      exact Or.inl hx1w
    · subst w
      exact Or.inr hx1w
  rcases hxy with hx1y1 | hx1y2
  · exact ⟨x1, x2, y1, y2, hd, hall, hNu, hNv,
      complete_pairing F hdeg htri hd hall hNu hNv hcommon hx1y1⟩
  · have hd' : ([u, v, x1, x2, y2, y1] : List W).Nodup := by
      exact (List.Perm.cons u (List.Perm.cons v (List.Perm.cons x1
        (List.Perm.cons x2 (List.Perm.swap y2 y1 []))))).nodup hd
    have hall' : ∀ w, w = u ∨ w = v ∨ w = x1 ∨ w = x2 ∨ w = y2 ∨ w = y1 := by
      intro w
      simpa only [or_comm (a := w = y1) (b := w = y2)] using hall w
    have hNv' : F.neighborFinset v = {y2, y1} :=
      hNv.trans (Finset.pair_comm y1 y2)
    exact ⟨x1, x2, y2, y1, hd', hall', hNu, hNv',
      complete_pairing F hdeg htri hd' hall' hNu hNv' hcommon hx1y2⟩

end AsymmetricRigidityCore
