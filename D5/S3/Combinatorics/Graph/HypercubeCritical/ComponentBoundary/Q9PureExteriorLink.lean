/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Exterior links have even degrees, with an empty or complete link on three directions. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-! At a vertex with no neighbors in a balanced cubic support, two flips can reach
that support only along directions that avoid the separated partner. On three such
directions, exterior parity forces the link to be empty or a triangle. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PureExteriorLink

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced)
open BalancedCubeComponentBoundary (directions exterior_even mem_directions regular_directions)
open BalancedCubeGirth (flip_comm)
open private cross_two_not_mem flip_injective link link_subset from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-- Directions whose first flip avoids the partner support. -/
def exteriorDirections {n : ℕ} (D : Finset (Q n)) (x : Q n) : Finset (Fin n) :=
  Finset.univ \ directions D x

/-- Exterior directions are exactly those whose flip avoids `D`. -/
private theorem mem_exteriorDirections {n : ℕ} {D : Finset (Q n)} {x : Q n} {i : Fin n} :
    i ∈ exteriorDirections D x ↔ flip x i ∉ D := by
  simp [exteriorDirections, mem_directions]

/-- The neighbors of an exterior direction `i` in the link are the other exterior
directions whose pair flip with `i` lands in `C`. -/
def exteriorLinkNeighbors {n : ℕ} (C D : Finset (Q n)) (x : Q n) (i : Fin n) :
    Finset (Fin n) :=
  link C x (exteriorDirections D x) i

/-- Two distinct exterior directions are joined when their pair flip lands in `C`. -/
private theorem mem_exteriorLinkNeighbors {n : ℕ} {C D : Finset (Q n)} {x : Q n}
    {i j : Fin n} :
    j ∈ exteriorLinkNeighbors C D x i ↔
      j ≠ i ∧ j ∈ exteriorDirections D x ∧ flip (flip x i) j ∈ C := by
  simp [exteriorLinkNeighbors, link, and_assoc]

private theorem mem_exteriorLinkNeighbors_symm {n : ℕ} {C D : Finset (Q n)} {x : Q n}
    {i j : Fin n} (hi : i ∈ exteriorDirections D x)
    (hj : j ∈ exteriorLinkNeighbors C D x i) : i ∈ exteriorLinkNeighbors C D x j := by
  obtain ⟨hji, _, hC⟩ := mem_exteriorLinkNeighbors.mp hj
  exact mem_exteriorLinkNeighbors.mpr ⟨hji.symm, hi, by rwa [flip_comm x j i]⟩

/-- At a vertex outside `C`, separation identifies the link neighborhood with
all directions from the first flip into `C`. -/
theorem exteriorLinkNeighbors_eq_directions {n : ℕ} {C D : Finset (Q n)} {x : Q n}
    (hcross : ∀ u ∈ C, ∀ v ∈ D, ¬ (hypercube n).Adj u v) (hx : x ∉ C) (i : Fin n) :
    exteriorLinkNeighbors C D x i = directions C (flip x i) := by
  ext j
  rw [mem_exteriorLinkNeighbors, mem_directions]
  refine ⟨fun h => h.2.2, fun h => ⟨?_, ?_, h⟩⟩
  · rintro rfl
    exact hx (by simpa only [BalancedCriticalSpectrum.flip_flip] using h)
  · exact mem_exteriorDirections.mpr fun hj => cross_two_not_mem C D hcross x i j hj h

variable {C D : Finset (Q 9)} {x : Q 9}

private theorem not_mem_of_directions_eq_empty (hC : directions C x = ∅) (i : Fin 9) :
    flip x i ∉ C := by
  intro hi
  simpa only [hC, Finset.notMem_empty] using (mem_directions C x i).mpr hi

open Classical in
private theorem not_mem_of_no_neighbors
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hC : directions C x = ∅) : x ∉ C := by
  intro hx
  have hdegree := regular_directions C hr hx
  simp [hC] at hdegree

open Classical in
/-- Every vertex of the exterior link has even degree, by Huang exterior parity
at the corresponding first flip. -/
theorem even_card_exteriorLinkNeighbors
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcross : ∀ u ∈ C, ∀ v ∈ D, ¬ (hypercube 9).Adj u v)
    (hC : directions C x = ∅) (i : Fin 9) :
    Even (exteriorLinkNeighbors C D x i).card := by
  rw [exteriorLinkNeighbors_eq_directions hcross (not_mem_of_no_neighbors hr hC)]
  exact exterior_even C hr hb _ (not_mem_of_directions_eq_empty hC i)

open Classical in
/-- With three exterior directions, each link degree is zero or two. -/
private theorem card_exteriorLinkNeighbors_eq_zero_or_two
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcross : ∀ u ∈ C, ∀ v ∈ D, ¬ (hypercube 9).Adj u v)
    (hC : directions C x = ∅)
    (hthree : (exteriorDirections D x).card = 3) {i : Fin 9} (hi : i ∈ exteriorDirections D x) :
    (exteriorLinkNeighbors C D x i).card = 0 ∨ (exteriorLinkNeighbors C D x i).card = 2 := by
  have hle := Finset.card_le_card (link_subset C x (exteriorDirections D x) i)
  change (exteriorLinkNeighbors C D x i).card ≤ ((exteriorDirections D x).erase i).card at hle
  rw [Finset.card_erase_of_mem hi, hthree] at hle
  obtain ⟨k, hk⟩ := even_card_exteriorLinkNeighbors hr hb hcross hC i
  omega

open Classical in
/-- The link on three exterior directions is empty or complete. In the complete
case all three distinct pair flips land in `C`. -/
theorem exteriorLink_empty_or_complete_of_card_three
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcross : ∀ u ∈ C, ∀ v ∈ D, ¬ (hypercube 9).Adj u v)
    (hC : directions C x = ∅)
    (hthree : (exteriorDirections D x).card = 3) :
    (∀ i ∈ exteriorDirections D x, exteriorLinkNeighbors C D x i = ∅) ∨
    (∀ i ∈ exteriorDirections D x,
      exteriorLinkNeighbors C D x i = (exteriorDirections D x).erase i) := by
  have full {i : Fin 9} (hi : i ∈ exteriorDirections D x)
      (hne : (exteriorLinkNeighbors C D x i).Nonempty) :
      exteriorLinkNeighbors C D x i = (exteriorDirections D x).erase i := by
    refine Finset.eq_of_subset_of_card_le (link_subset C x (exteriorDirections D x) i) ?_
    have htwo := (card_exteriorLinkNeighbors_eq_zero_or_two hr hb hcross hC hthree hi).resolve_left
      (fun hz => hne.ne_empty (Finset.card_eq_zero.mp hz))
    rw [htwo, Finset.card_erase_of_mem hi, hthree]
  by_cases hempty : ∀ i ∈ exteriorDirections D x, exteriorLinkNeighbors C D x i = ∅
  · exact Or.inl hempty
  · push Not at hempty
    obtain ⟨i, hi, hne⟩ := hempty
    have hfull := full hi hne
    right
    intro j hj
    by_cases hji : j = i
    · exact hji.symm ▸ hfull
    · have hjLink : j ∈ exteriorLinkNeighbors C D x i :=
        hfull ▸ Finset.mem_erase.mpr ⟨hji, hj⟩
      exact full hj ⟨i, mem_exteriorLinkNeighbors_symm hi hjLink⟩

/-- A high leaf in direction `i` occupies every transverse double flip in `D`,
so the link row at `i` is empty. -/
private theorem exteriorLinkNeighbors_eq_empty_of_highLeaf (hdisj : Disjoint C D) {i : Fin 9}
    (htransverse : ∀ j ≠ i, flip (flip x i) j ∈ D) :
    exteriorLinkNeighbors C D x i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hji, _, hjC⟩ := mem_exteriorLinkNeighbors.mp hj
  exact Finset.disjoint_left.mp hdisj hjC (htransverse j hji)

open Classical in
/-- With three exterior directions and a high leaf, every first-flip vertex has
no neighbor in `C`. Thus every pair flip stays outside `C`. -/
theorem pairFlips_not_mem_of_card_three_of_highLeaf
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcross : ∀ u ∈ C, ∀ v ∈ D, ¬ (hypercube 9).Adj u v)
    (hC : directions C x = ∅) (hdisj : Disjoint C D)
    (hthree : (exteriorDirections D x).card = 3) {a : Fin 9}
    (hhigh : flip x a ∉ D) (htransverse : ∀ j ≠ a, flip (flip x a) j ∈ D) :
    ∀ i j : Fin 9, flip (flip x i) j ∉ C := by
  have haExt := mem_exteriorDirections.mpr hhigh
  have haEmpty := exteriorLinkNeighbors_eq_empty_of_highLeaf hdisj htransverse
  have hempty := (exteriorLink_empty_or_complete_of_card_three hr hb hcross hC hthree).resolve_right
    fun hfull => by
      have hcard := congrArg Finset.card ((hfull a haExt).symm.trans haEmpty)
      rw [Finset.card_erase_of_mem haExt, hthree, Finset.card_empty] at hcard
      omega
  intro i j hjC
  by_cases hi : i ∈ exteriorDirections D x
  · have hx := not_mem_of_no_neighbors hr hC
    have hj := (mem_directions C (flip x i) j).mpr hjC
    rw [← exteriorLinkNeighbors_eq_directions hcross hx, hempty i hi] at hj
    exact Finset.notMem_empty _ hj
  · have hiD : flip x i ∈ D := by simpa only [mem_exteriorDirections, not_not] using hi
    exact hcross _ hjC _ hiD (flip_adj (flip x i) j).symm

open Classical in
/-- If a vertex avoiding `C` at distance one contacts `C` at distance two,
it contacts at least three distinct vertices there. The two directions of
one contact each have positive even link degree, and therefore supply two
further contacts. -/
theorem three_le_card_pairFlipContacts
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hC : directions C x = ∅) {i j : Fin 9} (hij : i ≠ j)
    (hcontact : flip (flip x i) j ∈ C) :
    3 ≤ (C.filter fun y => ∃ a b : Fin 9, a ≠ b ∧ y = flip (flip x a) b).card := by
  classical
  let D : Finset (Q 9) := ∅
  have hcross : ∀ u ∈ C, ∀ v ∈ D, ¬ (hypercube 9).Adj u v := by
    simp [D]
  have hx := not_mem_of_no_neighbors hr hC
  have hi : i ∈ exteriorDirections D x := mem_exteriorDirections.mpr (by simp [D])
  have hjLink : j ∈ exteriorLinkNeighbors C D x i := by
    rw [exteriorLinkNeighbors_eq_directions hcross hx]
    exact (mem_directions C _ _).mpr hcontact
  have hiLink := mem_exteriorLinkNeighbors_symm hi hjLink
  have other {a b : Fin 9} (hmem : b ∈ exteriorLinkNeighbors C D x a) :
      ∃ c ∈ exteriorLinkNeighbors C D x a, c ≠ b := by
    have hpos := Finset.card_pos.mpr ⟨b, hmem⟩
    obtain ⟨k, hk⟩ := even_card_exteriorLinkNeighbors hr hb hcross hC a
    have he : 1 < (exteriorLinkNeighbors C D x a).card := by omega
    exact Finset.exists_mem_ne he b
  obtain ⟨k, hk, hkj⟩ := other hjLink
  obtain ⟨l, hl, hli⟩ := other hiLink
  obtain ⟨hki, _, hkC⟩ := mem_exteriorLinkNeighbors.mp hk
  obtain ⟨hlj, _, hlC⟩ := mem_exteriorLinkNeighbors.mp hl
  have hfirst : flip (flip x i) j ≠ flip (flip x i) k := fun he =>
    hkj ((flip_injective _ he).symm)
  have hsecond : flip (flip x i) j ≠ flip (flip x j) l := by
    rw [flip_comm x i j]
    exact fun he => hli ((flip_injective _ he).symm)
  have hthird : flip (flip x i) k ≠ flip (flip x j) l := by
    intro he
    have hbit := congrFun he i
    simp [BalancedCriticalSpectrum.flip, hki, hij, hli.symm, hki.symm] at hbit
  let contacts := C.filter fun y => ∃ a b : Fin 9, a ≠ b ∧ y = flip (flip x a) b
  let three : Finset (Q 9) := {flip (flip x i) j, flip (flip x i) k, flip (flip x j) l}
  have hsub : three ⊆ contacts := by
    intro y hy
    simp only [three, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hcontact, i, j, hij, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hkC, i, k, hki.symm, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hlC, j, l, hlj.symm, rfl⟩
  have hcard : three.card = 3 := by
    simp [three, hfirst, hsecond, hthird]
  simpa [hcard] using Finset.card_le_card hsub

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PureExteriorLink
