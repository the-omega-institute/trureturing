/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.claim
   digest: Actual asymmetric slice parameters force the excluded twenty-four-point graph. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceNonEmbedding

/-! Actual degree-two/three bipartite slices with side counts13/11 and low
counts7/1, independent low vertices and girth at least eight have no induced
realization in any finite cube. Actual saturation forces a six-high core, all
eleven right labels and seven low pairs; actual degrees give an induced copy
of the previously excluded graph. Other parameter cases and Problem2 remain open.
The finite helper checks are consumed by the designated refutation result. -/

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

/- Uncompiled source draft. A distinguished nonedge with no common neighbor
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

/- Uncompiled source draft: compression of actual two-high-neighbor right
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
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity (asymmetric_left_connector_count)
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
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity (asymmetric_right_type_counts)

open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricCompressedCore (high_left high_degree)
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity (asymmetric_left_connector_count right_high_neighbor_rigidity)
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

/- An internal bridge for the actual asymmetric-slice classification.
Only positive high incidences are assumed. The finite lemma checks short-path
witnesses, not a catalog of low pairings or of graphs. -/

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairAllowed

open SimpleGraph AsymmetricLowPairing
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairing (low_pair_excluded_by_common_high low_pair_excluded_by_short_paths)

-- Right labels: z, a, b, c, d, e, f, X1, X2, Y1, Y2.
-- High labels: u, v, x1, x2, y1, y2.
private def highIncidence (i : Fin 11) (p : Fin 6) : Prop :=
  (i, p) ∈ ([(0, 0), (0, 1), (1, 0), (1, 2), (2, 0), (2, 3),
    (3, 1), (3, 4), (4, 1), (4, 5), (5, 2), (5, 4), (6, 3), (6, 5),
    (7, 2), (8, 3), (9, 4), (10, 5)] : List (Fin 11 × Fin 6))

private instance (i : Fin 11) (p : Fin 6) : Decidable (highIncidence i p) := by
  unfold highIncidence
  infer_instance

/-- The fifteen allowed unordered pairs, expressed in both orientations. -/
private def allowedPair (i j : Fin 11) : Prop :=
  (i, j) ∈ ([(1, 4), (1, 10), (2, 3), (2, 9), (3, 8), (4, 7), (5, 6),
    (5, 8), (5, 10), (6, 7), (6, 9), (7, 8), (7, 10), (8, 9), (9, 10)] :
      List (Fin 11 × Fin 11)) ∨
  (j, i) ∈ ([(1, 4), (1, 10), (2, 3), (2, 9), (3, 8), (4, 7), (5, 6),
    (5, 8), (5, 10), (6, 7), (6, 9), (7, 8), (7, 10), (8, 9), (9, 10)] :
      List (Fin 11 × Fin 11))

private instance (i j : Fin 11) : Decidable (allowedPair i j) := by
  unfold allowedPair
  infer_instance

-- The witnesses are common high neighbors or actual four-edge high paths.
-- All quantifiers are finite, and `decide +kernel` builds an ordinary kernel proof.
private theorem forbidden_pair_witness :
    ∀ i j : Fin 11, i ≠ 0 → j ≠ 0 → i ≠ j → ¬ allowedPair i j →
      (∃ p : Fin 6, highIncidence i p ∧ highIncidence j p) ∨
      ∃ (p : Fin 6) (m : Fin 11) (q : Fin 6),
        highIncidence i p ∧ highIncidence m p ∧ highIncidence m q ∧
          highIncidence j q ∧ i ≠ m ∧ p ≠ q := by
  decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

omit [DecidableEq V] in
/-- Actual adjacency and girth exclude every pair outside the fifteen-pair list.
No exhaustive neighbor table or low-pair classification is assumed. -/
private theorem actual_low_pair_allowed
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (r : Fin 11 → V) (h : Fin 6 → V)
    (hr : Function.Injective r) (hh : Function.Injective h)
    (hrR : ∀ i, r i ∈ R) (hh3 : ∀ p, G.degree (h p) = 3)
    (hz2 : G.degree (r 0) = 2)
    (hinc : ∀ i p, highIncidence i p → G.Adj (r i) (h p))
    {i j : Fin 11} (hij : i ≠ j) (hpair : lowPair G (r i) (r j)) :
    allowedPair i j := by
  classical
  have hi0 : i ≠ 0 := by
    intro hi
    obtain ⟨w, hw2, hiw, _⟩ := hpair
    exact hlow hiw (by rw [hi]; exact hz2) hw2
  have hj0 : j ≠ 0 := by
    intro hj
    obtain ⟨w, hw2, _, hjw⟩ := hpair
    exact hlow hjw (by rw [hj]; exact hz2) hw2
  have hrij : r i ≠ r j := fun he => hij (hr he)
  by_contra hbad
  rcases forbidden_pair_witness i j hi0 hj0 hij hbad with
    ⟨p, hip, hjp⟩ | ⟨p, m, q, hip, hmp, hmq, hjq, him, hpq⟩
  · exact (low_pair_excluded_by_common_high hpart hg (hrR i) (hh3 p)
      (hinc i p hip) (hinc j p hjp) hrij) hpair
  · exact (low_pair_excluded_by_short_paths hpart hg (hrR i) (hh3 p) (hh3 q)
      (hinc i p hip) (hinc m p hmp).symm (hinc m q hmq) (hinc j q hjq)
      hrij (fun he => him (hr he)) (fun he => hpq (hh he))) hpair

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairAllowed

end

/- Internal proof source for the actual asymmetric-slice refutation. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairForced

open SimpleGraph GirthSliceCounting AsymmetricLowPairing AsymmetricLowPairAllowed
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairing (coverage_forces_low_pair)
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity (high_root_endpoint_coverage)
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricHighRightLabels (stub_actual_saturation)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem first_four_low_pairs
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1)
    (r : Fin 11 → V) (h : Fin 6 → V)
    (hr : Function.Injective r) (hh : Function.Injective h)
    (hrR : ∀ i, r i ∈ R) (hhL : ∀ p, h p ∈ L)
    (hh3 : ∀ p, G.degree (h p) = 3) (hz2 : G.degree (r 0) = 2)
    (hinc : ∀ i p, G.Adj (r i) (h p) ↔ highIncidence i p)
    (Nu : G.neighborFinset (h 0) = {r 1, r 2, r 0})
    (Nv : G.neighborFinset (h 1) = {r 3, r 4, r 0})
    (Tz : degreeThree G (G.neighborFinset (r 0)) = {h 0, h 1})
    (Ta : degreeThree G (G.neighborFinset (r 1)) = {h 0, h 2})
    (Tb : degreeThree G (G.neighborFinset (r 2)) = {h 0, h 3})
    (Tc : degreeThree G (G.neighborFinset (r 3)) = {h 1, h 4})
    (Td : degreeThree G (G.neighborFinset (r 4)) = {h 1, h 5}) :
    lowPair G (r 1) (r 10) ∧ lowPair G (r 2) (r 9) ∧
      lowPair G (r 3) (r 8) ∧ lowPair G (r 4) (r 7) := by
  classical
  have hsat := stub_actual_saturation hdeg hL hR hL2 hR2
  have cover (p : Fin 6) (i : Fin 11) :=
    high_root_endpoint_coverage hpart hdeg hlow hg hsat
      (Finset.mem_filter.mpr ⟨hhL p, hh3 p⟩) (hrR i)
  have nAdj (i : Fin 11) (p : Fin 6) (hn : ¬ highIncidence i p) :
      ¬ G.Adj (h p) (r i) := fun ha => hn ((hinc i p).mp ha.symm)
  have allowed {i j : Fin 11} (hne : i ≠ j) (hp : lowPair G (r i) (r j)) :=
    actual_low_pair_allowed hpart hlow hg r h hr hh hrR hh3 hz2
      (fun i p hi => (hinc i p).mpr hi) hne hp
  have h10 := coverage_forces_low_pair hdeg hlow Nu hz2 Ta Tb Tz
    (nAdj 10 0 (by decide +kernel)) (nAdj 10 1 (by decide +kernel))
    (nAdj 10 2 (by decide +kernel)) (nAdj 10 3 (by decide +kernel)) (cover 0 10)
  have h9 := coverage_forces_low_pair hdeg hlow Nu hz2 Ta Tb Tz
    (nAdj 9 0 (by decide +kernel)) (nAdj 9 1 (by decide +kernel))
    (nAdj 9 2 (by decide +kernel)) (nAdj 9 3 (by decide +kernel)) (cover 0 9)
  have h8 := coverage_forces_low_pair hdeg hlow Nv hz2 Tc Td
    (by simpa only [Finset.pair_comm] using Tz)
    (nAdj 8 1 (by decide +kernel)) (nAdj 8 0 (by decide +kernel))
    (nAdj 8 4 (by decide +kernel)) (nAdj 8 5 (by decide +kernel)) (cover 1 8)
  have h7 := coverage_forces_low_pair hdeg hlow Nv hz2 Tc Td
    (by simpa only [Finset.pair_comm] using Tz)
    (nAdj 7 1 (by decide +kernel)) (nAdj 7 0 (by decide +kernel))
    (nAdj 7 4 (by decide +kernel)) (nAdj 7 5 (by decide +kernel)) (cover 1 7)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases h10 with hp | hp
    · exact hp
    · exact False.elim ((by decide +kernel : ¬ allowedPair 2 10) (allowed (by decide) hp))
  · rcases h9 with hp | hp
    · exact False.elim ((by decide +kernel : ¬ allowedPair 1 9) (allowed (by decide) hp))
    · exact hp
  · rcases h8 with hp | hp
    · exact hp
    · exact False.elim ((by decide +kernel : ¬ allowedPair 4 8) (allowed (by decide) hp))
  · rcases h7 with hp | hp
    · exact False.elim ((by decide +kernel : ¬ allowedPair 3 7) (allowed (by decide) hp))
    · exact hp

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairForced

end

/- Internal pairing-completion bridge for the actual asymmetric slice.
The two-partner hypothesis is an explicit interface to the actual stub-degree
argument. The finite index checks below belong to the eventual exclusion host;
this source is not a standalone frozen classification result. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairCompletion

open SimpleGraph AsymmetricLowPairing AsymmetricLowPairAllowed
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairing (low_pair_excluded_by_fixed_pair)

private theorem allowed_five :
    ∀ j : Fin 11, allowedPair 5 j → j = 6 ∨ j = 8 ∨ j = 10 := by
  decide +kernel

private theorem allowed_seven :
    ∀ j : Fin 11, allowedPair 7 j → j = 4 ∨ j = 6 ∨ j = 8 ∨ j = 10 := by
  decide +kernel

private theorem allowed_nine :
    ∀ j : Fin 11, allowedPair 9 j → j = 2 ∨ j = 6 ∨ j = 8 ∨ j = 10 := by
  decide +kernel

private theorem two_partners_force_second
    (P : Fin 11 → Fin 11 → Prop) (i a b : Fin 11)
    (hchoice : ∀ j, i ≠ j → P i j → j = a ∨ j = b)
    (htwo : ∃ j k, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧ P i j ∧ P i k) :
    P i b := by
  obtain ⟨j, k, hjk, hij, hik, hpj, hpk⟩ := htwo
  rcases hchoice j hij hpj with hj | hj
  · rcases hchoice k hik hpk with hk | hk
    · exact False.elim (hjk (hj.trans hk.symm))
    · simpa only [hk] using hpk
  · simpa only [hj] using hpj

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem low_pair_symm {a b : V} (hp : lowPair G a b) : lowPair G b a := by
  obtain ⟨w, hw2, haw, hbw⟩ := hp
  exact ⟨w, hw2, hbw, haw⟩

/-- Four forced pairings, actual girth, and the actual stub two-partner property
force the remaining three pairings. The two-partner premise is not a pairing
classification: its witnesses may be any of the eleven actual right labels. -/
private theorem actual_low_pair_completion
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (r : Fin 11 → V) (h : Fin 6 → V)
    (hr : Function.Injective r) (hh : Function.Injective h)
    (hrR : ∀ i, r i ∈ R) (hh3 : ∀ p, G.degree (h p) = 3)
    (hz2 : G.degree (r 0) = 2)
    (hinc : ∀ i p, highIncidence i p → G.Adj (r i) (h p))
    (hexists : ∀ i : Fin 11, i ≠ 0 → ∃ j, i ≠ j ∧ lowPair G (r i) (r j))
    (htwo : ∀ i ∈ ({7, 8, 9, 10} : Finset (Fin 11)),
      ∃ j k, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧
        lowPair G (r i) (r j) ∧ lowPair G (r i) (r k))
    (haY2 : lowPair G (r 1) (r 10))
    (hbY1 : lowPair G (r 2) (r 9))
    (hcX2 : lowPair G (r 3) (r 8))
    (hdX1 : lowPair G (r 4) (r 7)) :
    lowPair G (r 5) (r 6) ∧
      lowPair G (r 7) (r 8) ∧ lowPair G (r 9) (r 10) := by
  classical
  have hallowed {i j : Fin 11} (hij : i ≠ j)
      (hp : lowPair G (r i) (r j)) : allowedPair i j :=
    actual_low_pair_allowed hpart hlow hg r h hr hh hrR hh3 hz2 hinc hij hp
  have hfixed_excludes {a s t : Fin 11} {q : Fin 6}
      (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
      (hsq : highIncidence s q) (haq : highIncidence a q)
      (hp : lowPair G (r a) (r t)) : ¬ lowPair G (r s) (r t) := by
    exact low_pair_excluded_by_fixed_pair hpart hg (hrR s) (hh3 q)
      (fun he => has (hr he)) (fun he => hat (hr he)) (fun he => hst (hr he))
      (hinc s q hsq) (hinc a q haq) hp

  -- c-X2 and the common y1 exclude e-X2.
  have hno58 : ¬ lowPair G (r 5) (r 8) :=
    hfixed_excludes (a := 3) (q := 4)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hcX2
  -- a-Y2 and the common x1 exclude e-Y2.
  have hno510 : ¬ lowPair G (r 5) (r 10) :=
    hfixed_excludes (a := 1) (q := 2)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) haY2
  have hef : lowPair G (r 5) (r 6) := by
    obtain ⟨j, h5j, hp⟩ := hexists 5 (by decide +kernel)
    rcases allowed_five j (hallowed h5j hp) with rfl | rfl | rfl
    · exact hp
    · exact False.elim (hno58 hp)
    · exact False.elim (hno510 hp)

  -- d-X1 and the common y2 exclude f-X1.
  have hno67 : ¬ lowPair G (r 6) (r 7) :=
    hfixed_excludes (a := 4) (q := 5)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hdX1
  -- a-Y2 and the common x1 exclude X1-Y2.
  have hno710 : ¬ lowPair G (r 7) (r 10) :=
    hfixed_excludes (a := 1) (q := 2)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) haY2
  have hXchoice (j : Fin 11) (h7j : (7 : Fin 11) ≠ j)
      (hp : lowPair G (r 7) (r j)) : j = 4 ∨ j = 8 := by
    rcases allowed_seven j (hallowed h7j hp) with hj | rfl | hj | rfl
    · exact Or.inl hj
    · exact False.elim (hno67 (low_pair_symm hp))
    · exact Or.inr hj
    · exact False.elim (hno710 hp)
  have hXX : lowPair G (r 7) (r 8) :=
    two_partners_force_second (fun i j => lowPair G (r i) (r j)) 7 4 8
      hXchoice (htwo 7 (by simp))

  -- b-Y1 and the common x2 exclude f-Y1.
  have hno69 : ¬ lowPair G (r 6) (r 9) :=
    hfixed_excludes (a := 2) (q := 3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hbY1
  -- c-X2 and the common y1 exclude Y1-X2.
  have hno98 : ¬ lowPair G (r 9) (r 8) :=
    hfixed_excludes (a := 3) (q := 4)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hcX2
  have hYchoice (j : Fin 11) (h9j : (9 : Fin 11) ≠ j)
      (hp : lowPair G (r 9) (r j)) : j = 2 ∨ j = 10 := by
    rcases allowed_nine j (hallowed h9j hp) with hj | rfl | rfl | hj
    · exact Or.inl hj
    · exact False.elim (hno69 (low_pair_symm hp))
    · exact False.elim (hno98 hp)
    · exact Or.inr hj
  have hYY : lowPair G (r 9) (r 10) :=
    two_partners_force_second (fun i j => lowPair G (r i) (r j)) 9 2 10
      hYchoice (htwo 9 (by simp))
  exact ⟨hef, hXX, hYY⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairCompletion

end

/- Internal bridge for the actual asymmetric-slice refutation. -/

/- Actual complete indexed labels for the asymmetric parameter branch. -/

set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricIndexedSliceLabels

open SimpleGraph GirthSliceCounting AsymmetricCompressedCore AsymmetricLowPairAllowed
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricHighRightLabels (high_right_connector_labels right_labels_assembly)
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricCompressedCore (high_left high_degree connector_right connector_degree)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rows in the order z,a,b,c,d,e,f,X1,X2,Y1,Y2. -/
private def highRow (h : Fin 6 → V) : Fin 11 → Finset V :=
  ![{h 0, h 1}, {h 0, h 2}, {h 0, h 3}, {h 1, h 4},
    {h 1, h 5}, {h 2, h 4}, {h 3, h 5}, {h 2}, {h 3}, {h 4}, {h 5}]

/-- Actual vertices, complete side and high-side enumerations, and actual tables.
This is an internal proof package, not an added classification assumption. -/
private structure IndexedLabels (G : SimpleGraph V) (L R : Finset V) where
  r : Fin 11 → V
  h : Fin 6 → V
  r_injective : Function.Injective r
  h_injective : Function.Injective h
  r_mem : ∀ i, r i ∈ R
  h_mem : ∀ p, h p ∈ L
  h_degree : ∀ p, G.degree (h p) = 3
  r_zero_degree : G.degree (r 0) = 2
  r_nonzero_degree : ∀ i, i ≠ 0 → G.degree (r i) = 3
  r_complete : ∀ w ∈ R, ∃ i, r i = w
  h_complete : ∀ w ∈ degreeThree G L, ∃ p, h p = w
  incidence : ∀ i p, G.Adj (r i) (h p) ↔ highIncidence i p
  u_neighbors : G.neighborFinset (h 0) = {r 1, r 2, r 0}
  v_neighbors : G.neighborFinset (h 1) = {r 3, r 4, r 0}
  high_neighbors : ∀ i, degreeThree G (G.neighborFinset (r i)) = highRow h i

set_option maxHeartbeats 400000 in
private theorem indexed_labels_of_parameters
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1) :
    Nonempty (IndexedLabels G L R) := by
  classical
  obtain ⟨z, hz, u, v, x1, x2, y1, y2, huz, hvz, hhigh, hhigh_all,
    a, b, c, d, e, f, ha, hb, hc, hd, he, hf, hmiddle, hM,
    Ta, Tb, Tc, Td, Te, Tf⟩ :=
    high_right_connector_labels hpart hdeg hlow hg hL hR hL2 hR2
  obtain ⟨X1, X2, Y1, Y2, hX1R, hX2R, hY1R, hY2R,
    hX13, hX23, hY13, hY23, TX1, TX2, TY1, TY2,
    Nz, Nu, Nv, Nx1, Nx2, Ny1, Ny2, hright, hR_all⟩ :=
    right_labels_assembly hpart hdeg hlow hg hL hR hL2 hR2 hz
      u v x1 x2 y1 y2 huz hvz hhigh ha hb hc hd he hf hmiddle hM
      Ta Tb Tc Td Te Tf
  let r : Fin 11 → V := ([z, a, b, c, d, e, f, X1, X2, Y1, Y2] : List V).get
  let h : Fin 6 → V := ([u.val, v.val, x1.val, x2.val, y1.val, y2.val] : List V).get
  have hr : Function.Injective r := hright.injective_get
  have hhd : ([u.val, v.val, x1.val, x2.val, y1.val, y2.val] : List V).Nodup :=
    hhigh.map Subtype.val_injective
  have hh : Function.Injective h := hhd.injective_get
  have hzR : z ∈ R := (Finset.mem_filter.mp hz).1
  have hz2 : G.degree z = 2 := (Finset.mem_filter.mp hz).2
  have hrR : ∀ i, r i ∈ R := by
    intro i
    fin_cases i <;> simp only [r, List.get_eq_getElem]
    · exact hzR
    · exact connector_right ha
    · exact connector_right hb
    · exact connector_right hc
    · exact connector_right hd
    · exact connector_right he
    · exact connector_right hf
    · exact hX1R
    · exact hX2R
    · exact hY1R
    · exact hY2R
  have hhL : ∀ p, h p ∈ L := by
    intro p
    fin_cases p <;> simp only [h, List.get_eq_getElem]
    · exact high_left u
    · exact high_left v
    · exact high_left x1
    · exact high_left x2
    · exact high_left y1
    · exact high_left y2
  have hh3 : ∀ p, G.degree (h p) = 3 := by
    intro p
    fin_cases p <;> simp only [h, List.get_eq_getElem]
    · exact high_degree u
    · exact high_degree v
    · exact high_degree x1
    · exact high_degree x2
    · exact high_degree y1
    · exact high_degree y2
  have hr3 : ∀ i, i ≠ 0 → G.degree (r i) = 3 := by
    intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    · exact connector_degree ha
    · exact connector_degree hb
    · exact connector_degree hc
    · exact connector_degree hd
    · exact connector_degree he
    · exact connector_degree hf
    · exact hX13
    · exact hX23
    · exact hY13
    · exact hY23
  have hr_all : ∀ w ∈ R, ∃ i, r i = w := by
    intro w hw
    rw [hR_all] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
    · exact ⟨0, hw.symm⟩
    · exact ⟨1, hw.symm⟩
    · exact ⟨2, hw.symm⟩
    · exact ⟨3, hw.symm⟩
    · exact ⟨4, hw.symm⟩
    · exact ⟨5, hw.symm⟩
    · exact ⟨6, hw.symm⟩
    · exact ⟨7, hw.symm⟩
    · exact ⟨8, hw.symm⟩
    · exact ⟨9, hw.symm⟩
    · exact ⟨10, hw.symm⟩
  have hh_all : ∀ w ∈ degreeThree G L, ∃ p, h p = w := by
    intro w hw
    let w' : High G L := ⟨w, hw⟩
    rcases hhigh_all w' with hw' | hw' | hw' | hw' | hw' | hw'
    · exact ⟨0, (congrArg Subtype.val hw').symm⟩
    · exact ⟨1, (congrArg Subtype.val hw').symm⟩
    · exact ⟨2, (congrArg Subtype.val hw').symm⟩
    · exact ⟨3, (congrArg Subtype.val hw').symm⟩
    · exact ⟨4, (congrArg Subtype.val hw').symm⟩
    · exact ⟨5, (congrArg Subtype.val hw').symm⟩
  have Tz : degreeThree G (G.neighborFinset z) = {u.val, v.val} := by
    rw [Nz]
    ext w
    simp only [degreeThree, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · exact And.left
    · intro hw
      refine ⟨hw, ?_⟩
      rcases hw with rfl | rfl
      · exact high_degree u
      · exact high_degree v
  have htables : ∀ i, degreeThree G (G.neighborFinset (r i)) = highRow h i := by
    intro i
    fin_cases i
    · simpa [r, h, highRow] using Tz
    · simpa [r, h, highRow] using Ta
    · simpa [r, h, highRow] using Tb
    · simpa [r, h, highRow] using Tc
    · simpa [r, h, highRow] using Td
    · simpa [r, h, highRow] using Te
    · simpa [r, h, highRow] using Tf
    · simpa [r, h, highRow] using TX1
    · simpa [r, h, highRow] using TX2
    · simpa [r, h, highRow] using TY1
    · simpa [r, h, highRow] using TY2
  have hinc : ∀ i p, G.Adj (r i) (h p) ↔ highIncidence i p := by
    intro i p
    have hm : G.Adj (r i) (h p) ↔
        h p ∈ degreeThree G (G.neighborFinset (r i)) := by
      simp [degreeThree, hh3 p]
    rw [hm, htables i]
    fin_cases i <;> fin_cases p <;>
      simp [highRow, highIncidence, hh.eq_iff]
  refine ⟨{
    r := r
    h := h
    r_injective := hr
    h_injective := hh
    r_mem := hrR
    h_mem := hhL
    h_degree := hh3
    r_zero_degree := hz2
    r_nonzero_degree := hr3
    r_complete := hr_all
    h_complete := hh_all
    incidence := hinc
    u_neighbors := ?_
    v_neighbors := ?_
    high_neighbors := htables
  }⟩
  · change G.neighborFinset u.val = {a, b, z}
    rw [Nu]
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    simp only [or_comm, or_left_comm, or_assoc]
  · change G.neighborFinset v.val = {c, d, z}
    rw [Nv]
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    simp only [or_comm, or_left_comm, or_assoc]

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricIndexedSliceLabels

end

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairPartners

open SimpleGraph GirthSliceCounting AsymmetricLowPairing
open private neighbor_parts_card one_three_cross_impossible from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private lemma other_right_of_low_neighbor
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (r : Fin 11 → V) (hcover : ∀ x ∈ R, ∃ i, r i = x)
    (i : Fin 11) (hriR : r i ∈ R)
    {w : V} (hw2 : G.degree w = 2) (hriw : G.Adj (r i) w) :
    ∃ j, i ≠ j ∧ G.Adj (r j) w := by
  have hwL : w ∈ L := hpart.mem_of_mem_adj' hriR hriw.symm
  have hcard : 1 < (G.neighborFinset w).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hw2]
    omega
  obtain ⟨v, hvN, hvne⟩ := Finset.exists_mem_ne hcard (r i)
  have hwv : G.Adj w v := (G.mem_neighborFinset _ _).mp hvN
  have hvR : v ∈ R := hpart.mem_of_mem_adj hwL hwv
  obtain ⟨j, hj⟩ := hcover v hvR
  refine ⟨j, ?_, ?_⟩
  · intro hij
    have hriv : r i = v := by simpa only [← hij] using hj
    exact hvne hriv.symm
  · rw [hj]
    exact hwv.symm

private theorem low_pair_partner_exists
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (r : Fin 11 → V) (hcover : ∀ x ∈ R, ∃ i, r i = x)
    (i : Fin 11) (hriR : r i ∈ R) (hri3 : G.degree (r i) = 3)
    (hhigh : (degreeThree G (G.neighborFinset (r i))).card ≤ 2) :
    ∃ j, i ≠ j ∧ lowPair G (r i) (r j) := by
  have hparts := neighbor_parts_card hdeg (r i)
  have hpos : 0 < (degreeTwo G (G.neighborFinset (r i))).card := by
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_filter.mp hw with ⟨hwN, hw2⟩
  have hriw : G.Adj (r i) w := (G.mem_neighborFinset _ _).mp hwN
  obtain ⟨j, hij, hrjw⟩ :=
    other_right_of_low_neighbor hpart r hcover i hriR hw2 hriw
  exact ⟨j, hij, w, hw2, hriw, hrjw⟩

private theorem two_low_pair_partners_exists
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (r : Fin 11 → V) (hrinj : Function.Injective r)
    (hcover : ∀ x ∈ R, ∃ i, r i = x)
    (i : Fin 11) (hriR : r i ∈ R) (hri3 : G.degree (r i) = 3)
    (hhigh : (degreeThree G (G.neighborFinset (r i))).card = 1) :
    ∃ j k, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧
      lowPair G (r i) (r j) ∧ lowPair G (r i) (r k) := by
  have hparts := neighbor_parts_card hdeg (r i)
  have hlowcard : (degreeTwo G (G.neighborFinset (r i))).card = 2 := by
    omega
  obtain ⟨w1, w2, hw12, hlow⟩ := Finset.card_eq_two.mp hlowcard
  have hw1 : w1 ∈ degreeTwo G (G.neighborFinset (r i)) := by
    rw [hlow]
    simp
  have hw2 : w2 ∈ degreeTwo G (G.neighborFinset (r i)) := by
    rw [hlow]
    simp
  rcases Finset.mem_filter.mp hw1 with ⟨hw1N, hw1degree⟩
  rcases Finset.mem_filter.mp hw2 with ⟨hw2N, hw2degree⟩
  have hriw1 : G.Adj (r i) w1 := (G.mem_neighborFinset _ _).mp hw1N
  have hriw2 : G.Adj (r i) w2 := (G.mem_neighborFinset _ _).mp hw2N
  obtain ⟨j, hij, hrjw1⟩ :=
    other_right_of_low_neighbor hpart r hcover i hriR hw1degree hriw1
  obtain ⟨k, hik, hrkw2⟩ :=
    other_right_of_low_neighbor hpart r hcover i hriR hw2degree hriw2
  have hri_ne_rj : r i ≠ r j := fun h => hij (hrinj h)
  have hjk : j ≠ k := by
    intro heq
    have hrjw2 : G.Adj (r j) w2 := by simpa only [← heq] using hrkw2
    exact one_three_cross_impossible hpart.symm hg hriR hriR
      hriw2 hriw1 hrjw1.symm hrjw2 hri_ne_rj hw12 ⟨rfl, rfl⟩
  exact ⟨j, k, hjk, hij, hik,
    ⟨w1, hw1degree, hriw1, hrjw1⟩, ⟨w2, hw2degree, hriw2, hrkw2⟩⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairPartners

end

/- From actual asymmetric parameters to the seven actual low pairs. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricActualPairs
open SimpleGraph GirthSliceCounting AsymmetricLowPairing AsymmetricLowPairAllowed
open AsymmetricIndexedSliceLabels AsymmetricLowPairCompletion AsymmetricLowPairPartners
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairPartners (low_pair_partner_exists two_low_pair_partners_exists)
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricIndexedSliceLabels (indexed_labels_of_parameters)
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairForced (first_four_low_pairs)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem indexed_high_card_bound (s : IndexedLabels G L R) (i : Fin 11) :
    (degreeThree G (G.neighborFinset (s.r i))).card ≤ 2 := by
  rw [s.high_neighbors i]
  fin_cases i <;> simp [highRow, s.h_injective.eq_iff]

private theorem indexed_stub_high_card (s : IndexedLabels G L R)
    (i : Fin 11) (hi : i ∈ ({7, 8, 9, 10} : Finset (Fin 11))) :
    (degreeThree G (G.neighborFinset (s.r i))).card = 1 := by
  rw [s.high_neighbors i]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [highRow]

private theorem indexed_first_four
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1)
    (s : IndexedLabels G L R) :
    lowPair G (s.r 1) (s.r 10) ∧ lowPair G (s.r 2) (s.r 9) ∧
      lowPair G (s.r 3) (s.r 8) ∧ lowPair G (s.r 4) (s.r 7) := by
  apply first_four_low_pairs hpart hdeg hlow hg hL hR hL2 hR2
    s.r s.h s.r_injective s.h_injective s.r_mem s.h_mem s.h_degree
    s.r_zero_degree s.incidence s.u_neighbors s.v_neighbors
  · simpa [highRow] using s.high_neighbors 0
  · simpa [highRow] using s.high_neighbors 1
  · simpa [highRow] using s.high_neighbors 2
  · simpa [highRow] using s.high_neighbors 3
  · simpa [highRow] using s.high_neighbors 4

private theorem all_actual_pairs
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1)
    (s : IndexedLabels G L R) :
    lowPair G (s.r 1) (s.r 10) ∧ lowPair G (s.r 2) (s.r 9) ∧
      lowPair G (s.r 3) (s.r 8) ∧ lowPair G (s.r 4) (s.r 7) ∧
      lowPair G (s.r 5) (s.r 6) ∧ lowPair G (s.r 7) (s.r 8) ∧
      lowPair G (s.r 9) (s.r 10) := by
  obtain ⟨h1, h2, h3, h4⟩ := indexed_first_four hpart hdeg hlow hg hL hR hL2 hR2 s
  have hexists : ∀ i : Fin 11, i ≠ 0 → ∃ j, i ≠ j ∧ lowPair G (s.r i) (s.r j) := by
    intro i hi
    exact low_pair_partner_exists hpart hdeg s.r s.r_complete i (s.r_mem i)
      (s.r_nonzero_degree i hi) (indexed_high_card_bound s i)
  have htwo : ∀ i ∈ ({7, 8, 9, 10} : Finset (Fin 11)),
      ∃ j k, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧
        lowPair G (s.r i) (s.r j) ∧ lowPair G (s.r i) (s.r k) := by
    intro i hi
    have hi0 : i ≠ 0 := by
      intro he
      simpa [he] using hi
    exact two_low_pair_partners_exists hpart hdeg hg s.r s.r_injective
      s.r_complete i (s.r_mem i) (s.r_nonzero_degree i hi0) (indexed_stub_high_card s i hi)
  obtain ⟨h5, h6, h7⟩ := actual_low_pair_completion hpart hlow hg s.r s.h
    s.r_injective s.h_injective s.r_mem s.h_degree s.r_zero_degree
    (fun i p hip => (s.incidence i p).mpr hip) hexists htwo h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricActualPairs

end

/- Internal bridge from seven actual low pairs to the explicit 24-point graph.
The finite tables below specify labels and check actual edge types and degrees;
they are internal helpers for the eventual exclusion theorem. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricPairEmbedding

open SimpleGraph AsymmetricLowPairing AsymmetricLowPairAllowed
open private graph edges from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceNonEmbedding

private instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

private abbrev Tag := Fin 11 ⊕ (Fin 7 ⊕ Fin 6)

private def leftEnd : Fin 7 → Fin 11 := ![1, 9, 2, 3, 7, 4, 5]
private def rightEnd : Fin 7 → Fin 11 := ![10, 10, 9, 8, 8, 7, 6]

private def labels : Fin 24 → Tag :=
  ![Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10,
    Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6,
    Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inl 2),
    Sum.inr (Sum.inl 3), Sum.inr (Sum.inl 4), Sum.inr (Sum.inl 5),
    Sum.inr (Sum.inl 6),
    Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 2),
    Sum.inr (Sum.inr 3), Sum.inr (Sum.inr 4), Sum.inr (Sum.inr 5), Sum.inl 0]

private def tagDegree : Tag → ℕ :=
  Sum.elim (fun i => if i = 0 then 2 else 3)
    (Sum.elim (fun _ => 2) (fun _ => 3))

private def neighbors (a : Fin 24) : Finset (Fin 24) :=
  Finset.univ.filter (graph.Adj a)

private def edgeType (a b : Fin 24) : Prop :=
  (∃ (i : Fin 11) (p : Fin 6), labels a = Sum.inl i ∧
    labels b = Sum.inr (Sum.inr p) ∧ highIncidence i p) ∨
  ∃ k : Fin 7, labels a = Sum.inr (Sum.inl k) ∧
    (labels b = Sum.inl (leftEnd k) ∨ labels b = Sum.inl (rightEnd k))

private instance (a b : Fin 24) : Decidable (edgeType a b) := by
  unfold edgeType
  infer_instance

private theorem endpoints_distinct : ∀ k : Fin 7, leftEnd k ≠ rightEnd k := by
  decide +kernel

private theorem endpoints_identify :
    ∀ i j : Fin 7,
      (leftEnd i = leftEnd j ∨ leftEnd i = rightEnd j) →
      (rightEnd i = leftEnd j ∨ rightEnd i = rightEnd j) → i = j := by
  decide +kernel

private theorem labels_injective : Function.Injective labels := by
  decide +kernel

private theorem edges_have_type :
    edges.all (fun e => decide (edgeType e.1 e.2)) = true := by
  decide +kernel

private theorem neighbor_card :
    ∀ a : Fin 24, (neighbors a).card = tagDegree (labels a) := by
  decide +kernel

private theorem injective_sum {A B W : Type*} (f : A → W) (g : B → W)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hsep : ∀ a b, f a ≠ g b) : Function.Injective (Sum.elim f g) := by
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (hf hxy)
      | inr b => exact False.elim (hsep a b hxy)
  | inr a =>
      cases y with
      | inl b => exact False.elim (hsep b a hxy.symm)
      | inr b => exact congrArg Sum.inr (hg hxy)

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

private def realize (r : Fin 11 → V) (w : Fin 7 → V) (h : Fin 6 → V) : Tag → V :=
  Sum.elim r (Sum.elim w h)

omit [DecidableEq V] in
/-- An injective edge-preserving map whose vertices have exactly the source
neighbor counts is induced. -/
private theorem induced_of_saturated_degrees
    {A : Type*} (H : SimpleGraph A) (N : A → Finset A)
    (hN : ∀ a b, b ∈ N a ↔ H.Adj a b)
    (f : A → V) (hf : Function.Injective f)
    (hedge : ∀ a b, H.Adj a b → G.Adj (f a) (f b))
    (hdegree : ∀ a, G.degree (f a) = (N a).card) :
    ∀ a b, H.Adj a b ↔ G.Adj (f a) (f b) := by
  classical
  have hsat (a : A) : (N a).image f = G.neighborFinset (f a) := by
    have hsub : (N a).image f ⊆ G.neighborFinset (f a) := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact (G.mem_neighborFinset _ _).mpr (hedge a b ((hN a b).mp hb))
    apply Finset.eq_of_subset_of_card_le hsub
    apply le_of_eq
    calc
      (G.neighborFinset (f a)).card = G.degree (f a) := rfl
      _ = (N a).card := hdegree a
      _ = ((N a).image f).card := (Finset.card_image_of_injective _ hf).symm
  intro a b
  constructor
  · exact hedge a b
  · intro hab
    have hb : f b ∈ (N a).image f := by
      rw [hsat a]
      exact (G.mem_neighborFinset _ _).mpr hab
    obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp hb
    have hcb' : c = b := hf hcb
    subst c
    exact (hN a b).mp hc

variable {L R : Finset V}

omit [DecidableEq V] in
/-- Seven actual low pairs and the positive high incidences give an actual
induced copy of the explicit 24-vertex graph. -/
private theorem actual_pair_embedding
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (r : Fin 11 → V) (h : Fin 6 → V)
    (hr : Function.Injective r) (hh : Function.Injective h)
    (hrR : ∀ i, r i ∈ R) (hhL : ∀ p, h p ∈ L)
    (hh3 : ∀ p, G.degree (h p) = 3)
    (hz2 : G.degree (r 0) = 2)
    (hr3 : ∀ i : Fin 11, i ≠ 0 → G.degree (r i) = 3)
    (hinc : ∀ i p, highIncidence i p → G.Adj (r i) (h p))
    (h0 : lowPair G (r 1) (r 10))
    (h1 : lowPair G (r 9) (r 10))
    (h2 : lowPair G (r 2) (r 9))
    (h3 : lowPair G (r 3) (r 8))
    (h4 : lowPair G (r 7) (r 8))
    (h5 : lowPair G (r 4) (r 7))
    (h6 : lowPair G (r 5) (r 6)) :
    ∃ F : Fin 24 → V, Function.Injective F ∧
      ∀ a b, graph.Adj a b ↔ G.Adj (F a) (F b) := by
  classical
  have hpairs : ∀ k : Fin 7, lowPair G (r (leftEnd k)) (r (rightEnd k)) := by
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
  have hwitness : ∀ k : Fin 7, ∃ w : V, G.degree w = 2 ∧
      G.Adj (r (leftEnd k)) w ∧ G.Adj (r (rightEnd k)) w := hpairs
  choose w hw2 hwp hwq using hwitness
  have hwL (k : Fin 7) : w k ∈ L :=
    hpart.symm.mem_of_mem_adj (hrR (leftEnd k)) (hwp k)
  have hwN (k : Fin 7) :
      G.neighborFinset (w k) = {r (leftEnd k), r (rightEnd k)} := by
    have hne : r (leftEnd k) ≠ r (rightEnd k) :=
      fun he => endpoints_distinct k (hr he)
    have hsub : ({r (leftEnd k), r (rightEnd k)} : Finset V) ⊆
        G.neighborFinset (w k) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · subst x
        exact (G.mem_neighborFinset _ _).mpr (hwp k).symm
      · have hx' := Finset.mem_singleton.mp hx
        subst x
        exact (G.mem_neighborFinset _ _).mpr (hwq k).symm
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    simp [SimpleGraph.card_neighborFinset_eq_degree, hw2 k, hne]
  have hw : Function.Injective w := by
    intro i j hij
    have hpi : r (leftEnd i) ∈ G.neighborFinset (w j) := by
      apply (G.mem_neighborFinset _ _).mpr
      simpa only [hij] using (hwp i).symm
    have hqi : r (rightEnd i) ∈ G.neighborFinset (w j) := by
      apply (G.mem_neighborFinset _ _).mpr
      simpa only [hij] using (hwq i).symm
    rw [hwN j] at hpi hqi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpi hqi
    exact endpoints_identify i j
      (hpi.elim (fun he => Or.inl (hr he)) (fun he => Or.inr (hr he)))
      (hqi.elim (fun he => Or.inl (hr he)) (fun he => Or.inr (hr he)))
  have hwh : ∀ k p, w k ≠ h p := by
    intro k p he
    have hk := hw2 k
    rw [he, hh3 p] at hk
    omega
  have hleft : Function.Injective (Sum.elim w h) := injective_sum w h hw hh hwh
  have hleftL (t : Fin 7 ⊕ Fin 6) : Sum.elim w h t ∈ L := by
    cases t with
    | inl k => exact hwL k
    | inr p => exact hhL p
  have hrleft : ∀ i t, r i ≠ Sum.elim w h t := by
    intro i t he
    have hiL : r i ∈ L := by
      rw [he]
      exact hleftL t
    exact Set.disjoint_left.mp hpart.disjoint hiL (hrR i)
  have hreal : Function.Injective (realize r w h) :=
    injective_sum r (Sum.elim w h) hr hleft hrleft
  let F : Fin 24 → V := fun a => realize r w h (labels a)
  have hF : Function.Injective F := hreal.comp labels_injective
  have hedge_entry {a b : Fin 24} (hab : (a, b) ∈ edges) :
      G.Adj (F a) (F b) := by
    have ht : edgeType a b :=
      of_decide_eq_true ((List.all_eq_true.mp edges_have_type) (a, b) hab)
    change G.Adj (realize r w h (labels a)) (realize r w h (labels b))
    rcases ht with ⟨i, p, ha, hb, hip⟩ | ⟨k, ha, hb⟩
    · rw [ha, hb]
      exact hinc i p hip
    · rcases hb with hb | hb
      · rw [ha, hb]
        exact (hwp k).symm
      · rw [ha, hb]
        exact (hwq k).symm
  have hedge : ∀ a b, graph.Adj a b → G.Adj (F a) (F b) := by
    intro a b hab
    rcases hab with ⟨_, hab | hab⟩
    · exact hedge_entry hab
    · exact (hedge_entry hab).symm
  have hreal_degree (t : Tag) : G.degree (realize r w h t) = tagDegree t := by
    rcases t with i | (k | p)
    · change G.degree (r i) = if i = 0 then 2 else 3
      split_ifs with hi
      · subst i
        exact hz2
      · exact hr3 i hi
    · exact hw2 k
    · exact hh3 p
  have hdegree (a : Fin 24) : G.degree (F a) = (neighbors a).card :=
    (hreal_degree (labels a)).trans (neighbor_card a).symm
  refine ⟨F, hF, ?_⟩
  apply induced_of_saturated_degrees graph neighbors ?_ F hF hedge hdegree
  intro a b
  simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricPairEmbedding

end

/- The asymmetric parameter branch has no induced realization in a finite cube. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceExclusion

open SimpleGraph GirthSliceCounting AsymmetricIndexedSliceLabels AsymmetricPairEmbedding
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricIndexedSliceLabels (indexed_labels_of_parameters)
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricActualPairs (all_actual_pairs)

/-- A genuine induced subset of a finite cube with the original slice parameters. -/
def claim : Prop :=
  ∃ (n : ℕ) (S : Finset (Fin n → Bool)),
    ∃ L R : Finset {x : Fin n → Bool // x ∈ S},
      let G := (hypercube n).induce {x | x ∈ S}
      G.IsBipartiteWith (L : Set {x : Fin n → Bool // x ∈ S})
        (R : Set {x : Fin n → Bool // x ∈ S}) ∧
      (∀ x, G.degree x = 2 ∨ G.degree x = 3) ∧
      (∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False) ∧
      (8 : ℕ∞) ≤ G.egirth ∧
      L.card = 13 ∧ R.card = 11 ∧
      (degreeTwo G L).card = 7 ∧ (degreeTwo G R).card = 1

/-- No finite cube contains an induced slice with parameters (13,11;7,1),
degrees two/three, independent low vertices and girth at least eight. -/
theorem result : ¬ claim := by
  rintro ⟨n, S, L, R, hpart, hdeg, hlow, hg, hL, hR, hL2, hR2⟩
  obtain ⟨s⟩ := indexed_labels_of_parameters hpart hdeg hlow hg hL hR hL2 hR2
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ :=
    all_actual_pairs hpart hdeg hlow hg hL hR hL2 hR2 s
  obtain ⟨F, hF, he⟩ := actual_pair_embedding hpart s.r s.h
    s.r_injective s.h_injective s.r_mem s.h_mem s.h_degree
    s.r_zero_degree s.r_nonzero_degree (fun i p hip => (s.incidence i p).mpr hip)
    p1 p7 p2 p3 p6 p4 p5
  exact AsymmetricSliceNonEmbedding.result
    ⟨n, fun a => (F a).val, Subtype.val_injective.comp hF, fun a b => he a b⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceExclusion

end
