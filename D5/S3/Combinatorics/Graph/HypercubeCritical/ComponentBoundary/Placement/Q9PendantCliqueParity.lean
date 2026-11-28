import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeThreeContactOrbit
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CoherentExteriorFragment

/-! Three closed axes in a four-axis contact clique force opposing stars in the contact fibre. The fourth axis may have further contact partners. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueParity

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced)
open BalancedCubeGirth (flip_comm)
open Q9CoherentExteriorFragment (twice_card_le_directions_of_coherent_exterior_fragment)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9SharedContactNormalized (LocalRules)
open Q9FiveAxisMissingContact (Geometry)
open Q9MinimumDistanceOperator (minimumDisplacements RidgeContact)
open Q9IsotropicHuang (parity)
open Q9SharedContactCNF (Word Axis)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open private row_contact minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter
open private parity_flip mem_minimumDisplacements differingAxes foldl_flip_apply from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private adjacentWord adjacentWord_spec from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF
open private rootWord rootWord_cube from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses

private def axes : Finset Axis := {0, 1, 2, 3}

private abbrev vertex (w : Word) : Q 9 := cubeBitVec 9 w

private theorem disjoint_contacts {C D : Finset (Q 9)}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y) :
    Disjoint C D := by
  rw [disjoint_left]
  intro x hx hy
  have hs := hsep x hx x hy
  simpa using hs

open Classical in
private theorem midpoint_partition {C D : Finset (Q 9)}
    (hleft : LocalRules C) (hright : LocalRules D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hclosed : ∀ i j : Axis, ({i, j} : Finset Axis) ∈ minimumDisplacements C D false 2 →
      (i.val < 3 → j ∈ axes) ∧ (j.val < 3 → i ∈ axes))
    {z : Q 9} {i j : Axis} (hz : parity z = true)
    (hi : i.val < 3) (hj : j.val < 3) (hC : flip z i ∈ C) (hD : flip z j ∈ D) :
    directions C z ∪ directions D z = axes ∧
      Disjoint (directions C z) (directions D z) ∧
      (directions C z).card = 2 := by
  have hd := disjoint_contacts hsep
  have hnC : z ∉ C := by
    intro hc
    have hs := hsep z hc (flip z j) hD
    have he : hammingDist z (flip z j) = 1 := flip_adj z j
    omega
  have hnD : z ∉ D := by
    intro hc
    have hs := hsep (flip z i) hC z hc
    have he : hammingDist (flip z i) z = 1 := (flip_adj z i).symm
    omega
  have hpc (k : Axis) : parity (flip z k) = false := by rw [parity_flip, hz]; decide
  have hsubC : directions C z ⊆ axes := by
    intro k hk
    have hc := (mem_directions C z k).mp hk
    have hne : k ≠ j := fun he => disjoint_left.mp hd (he ▸ hc) hD
    exact (hclosed k j (row_contact hc hD hne (hpc k))).2 hj
  have hsubD : directions D z ⊆ axes := by
    intro k hk
    have hc := (mem_directions D z k).mp hk
    have hne : i ≠ k := fun he => disjoint_left.mp hd (he ▸ hC) hc
    exact (hclosed i k (row_contact hC hc hne (hpc i))).1 hi
  have hdis : Disjoint (directions C z) (directions D z) := by
    rw [disjoint_left]
    intro k hkC hkD
    exact disjoint_left.mp hd ((mem_directions C z k).mp hkC) ((mem_directions D z k).mp hkD)
  have hposC := card_pos.mpr ⟨i, (mem_directions C z i).mpr hC⟩
  have hposD := card_pos.mpr ⟨j, (mem_directions D z j).mpr hD⟩
  obtain ⟨a, ha⟩ := hleft.exterior_degree z hnC
  obtain ⟨b, hb⟩ := hright.exterior_degree z hnD
  have hsub := union_subset hsubC hsubD
  have hc : (directions C z ∪ directions D z).card ≤ axes.card := card_le_card hsub
  have haxes : axes.card = 4 := by decide
  rw [card_union_of_disjoint hdis, haxes] at hc
  exact ⟨eq_of_subset_of_card_le hsub (by rw [haxes, card_union_of_disjoint hdis]; omega),
    hdis, by omega⟩

private theorem flip_vertex (w : Word) (i : Axis) :
    flip (vertex w) i = vertex (adjacentWord w i) := (adjacentWord_spec w i).symm

private theorem roots {C D : Finset (Q 9)} (h : Geometry C D) :
    vertex 0 ∈ C ∧ vertex 3 ∈ D := by
  have h0 : vertex 0 = D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization.origin := by
    simpa only [rootWord, Bool.false_eq_true, if_false] using rootWord_cube false
  have h3 : vertex 3 = Q9FiveAxisMissingContact.rightRoot := by
    simpa only [rootWord, if_true] using rootWord_cube true
  exact ⟨h0.symm ▸ h.left_root, h3.symm ▸ h.right_root⟩

open Classical in
private theorem translated_words {C D : Finset (Q 9)}
    (htrans : ∀ ⦃i j p q : Axis⦄ ⦃x : Q 9⦄, p ≠ q →
      (∀ k, ({i, k} : Finset Axis) ∈ minimumDisplacements C D false 2 →
        k = j ∨ k = p ∨ k = q) →
      RidgeContact C D false [i] j x →
      RidgeContact C D false [i] j (flip (flip x p) q))
    (hclosed : ∀ i j : Axis, ({i, j} : Finset Axis) ∈ minimumDisplacements C D false 2 →
      (i.val < 3 → j ∈ axes) ∧ (j.val < 3 → i ∈ axes))
    {w : Word} {i j p q : Axis}
    (hi : i.val < 3) (hpq : p ≠ q) (hij : i ≠ j)
    (hcover : ∀ k ∈ axes, k ≠ i → k = j ∨ k = p ∨ k = q)
    (hw : parity (vertex w) = false) (hC : vertex w ∈ C)
    (hD : vertex (adjacentWord (adjacentWord w i) j) ∈ D) :
    vertex (adjacentWord (adjacentWord w p) q) ∈ C ∧
      vertex (adjacentWord (adjacentWord (adjacentWord (adjacentWord w p) q) i) j) ∈ D := by
  have hpart (k : Axis) (hk : ({i, k} : Finset Axis) ∈ minimumDisplacements C D false 2) :
      k = j ∨ k = p ∨ k = q := by
    have hne : k ≠ i := by
      intro he
      subst k
      obtain ⟨x, _, y, _, _, hd, ha⟩ := mem_minimumDisplacements.mp hk
      change (differingAxes x y).card = 2 at hd
      rw [ha] at hd
      simp at hd
    exact hcover k ((hclosed i k hk).1 hi) hne
  have hcontact : RidgeContact C D false [i] j (vertex w) := by
    refine ⟨by simpa using hij.symm, hC, hw, ?_⟩
    simpa only [List.foldl_cons,List.foldl_nil, adjacentWord_spec] using hD
  have hnew := htrans hpq hpart hcontact
  exact ⟨by simpa only [adjacentWord_spec] using hnew.2.1,
    by simpa only [adjacentWord_spec, List.foldl_cons,List.foldl_nil] using hnew.2.2.2⟩

/-- The normalized contact at words zero and three between two closed axes
forces one of the two opposing stars in the low four-coordinate even fiber. -/
theorem opposing_stars {C D : Finset (Q 9)} (h : Geometry C D)
    (hclosed : ∀ i j : Axis, ({i, j} : Finset Axis) ∈ minimumDisplacements C D false 2 →
      (i.val < 3 → j ∈ axes) ∧ (j.val < 3 → i ∈ axes))
    (htrans : ∀ ⦃i j p q : Axis⦄ ⦃x : Q 9⦄, p ≠ q →
      (∀ k, ({i, k} : Finset Axis) ∈ minimumDisplacements C D false 2 → k = j ∨ k = p ∨ k = q) →
      RidgeContact C D false [i] j x →
      RidgeContact C D false [i] j (flip (flip x p) q)) :
    ((∀ w ∈ ({0, 5, 6, 12} : Finset Word), vertex w ∈ C) ∧
      (∀ w ∈ ({3, 9, 10, 15} : Finset Word), vertex w ∈ D)) ∨
    ((∀ w ∈ ({0, 9, 10, 12} : Finset Word), vertex w ∈ C) ∧
      (∀ w ∈ ({3, 5, 6, 15} : Finset Word), vertex w ∈ D)) := by
  classical
  obtain ⟨h0, h3⟩ := roots h
  have hroot : vertex (adjacentWord (adjacentWord 0 0) 1) ∈ D := by
    rw [show adjacentWord (adjacentWord (0 : Word) 0) 1 = 3 by decide]
    exact h3
  obtain ⟨h12, h15⟩ := translated_words htrans hclosed (w := 0) (i := 0) (j := 1)
    (p := 2) (q := 3) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) h0 hroot
  have h12' : vertex 12 ∈ C := by exact h12
  have h15' : vertex 15 ∈ D := by exact h15
  have hL : (0 : Axis) ∈ directions C (vertex 1) :=
    (mem_directions _ _ _).mpr (by rw [flip_vertex]; exact h0)
  have hR : (1 : Axis) ∈ directions D (vertex 1) :=
    (mem_directions _ _ _).mpr (by rw [flip_vertex]; exact h3)
  obtain ⟨hpart, hdis, hcard⟩ := midpoint_partition h.left_rules h.right_rules h.separated hclosed (z := vertex 1)
    (i := 0) (j := 1) (by decide +kernel) (by decide) (by decide)
    ((mem_directions _ _ _).mp hL) ((mem_directions _ _ _).mp hR)
  have hchoice (k : Axis) (hk : k ∈ axes) :
      k ∈ directions C (vertex 1) ∨ k ∈ directions D (vertex 1) := by
    rw [← mem_union, hpart]
    exact hk
  have h2 := hchoice 2 (by decide)
  have h3axis := hchoice 3 (by decide)
  have hnotBoth : ¬ ((2 : Axis) ∈ directions C (vertex 1) ∧
      (3 : Axis) ∈ directions C (vertex 1)) := by
    rintro ⟨h2, h3⟩
    have hinc : ({0, 2, 3} : Finset Axis) ⊆ directions C (vertex 1) :=
      insert_subset hL (insert_subset h2 (singleton_subset_iff.mpr h3))
    have hle := card_le_card hinc
    rw [hcard, show ({0, 2, 3} : Finset Axis).card = 3 by decide] at hle
    omega
  have hnotNeither : ¬ ((2 : Axis) ∈ directions D (vertex 1) ∧
      (3 : Axis) ∈ directions D (vertex 1)) := by
    rintro ⟨h2, h3⟩
    have hinc : ({1, 2, 3} : Finset Axis) ⊆ directions D (vertex 1) :=
      insert_subset hR (insert_subset h2 (singleton_subset_iff.mpr h3))
    have hle := card_le_card hinc
    rw [show ({1, 2, 3} : Finset Axis).card = 3 by decide] at hle
    have hsum := card_union_of_disjoint hdis
    rw [hpart, hcard, show axes.card = 4 by decide] at hsum
    omega
  have hsplit : ((2 : Axis) ∈ directions C (vertex 1) ∧
      (3 : Axis) ∈ directions D (vertex 1)) ∨
      ((3 : Axis) ∈ directions C (vertex 1) ∧
      (2 : Axis) ∈ directions D (vertex 1)) := by tauto
  rcases hsplit with ⟨hc5, hd9⟩ | ⟨hc9, hd5⟩
  · have hc5' : vertex 5 ∈ C := by
      have hmem := (mem_directions _ _ _).mp hc5
      rw [flip_vertex] at hmem
      exact hmem
    have hd9' : vertex 9 ∈ D := by
      have hmem := (mem_directions _ _ _).mp hd9
      rw [flip_vertex] at hmem
      exact hmem
    obtain ⟨_, hd10⟩ := translated_words htrans hclosed (w := 5) (i := 1) (j := 2)
      (p := 0) (q := 3) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) hc5' (by exact h3)
    obtain ⟨hc6, _⟩ := translated_words htrans hclosed (w := 0) (i := 0) (j := 3)
      (p := 1) (q := 2) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) h0 (by exact hd9')
    left
    constructor
    · intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact h0
      · exact hc5'
      · exact hc6
      · exact h12'
    · intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact h3
      · exact hd9'
      · exact hd10
      · exact h15'
  · have hc9' : vertex 9 ∈ C := by
      have hmem := (mem_directions _ _ _).mp hc9
      rw [flip_vertex] at hmem
      exact hmem
    have hd5' : vertex 5 ∈ D := by
      have hmem := (mem_directions _ _ _).mp hd5
      rw [flip_vertex] at hmem
      exact hmem
    obtain ⟨_, hd6⟩ := translated_words htrans hclosed (w := 9) (i := 1) (j := 3)
      (p := 0) (q := 2) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) hc9' (by exact h3)
    obtain ⟨hc10, _⟩ := translated_words htrans hclosed (w := 0) (i := 0) (j := 2)
      (p := 1) (q := 3) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) h0 (by exact hd5')
    right
    constructor
    · intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact h0
      · exact hc9'
      · exact hc10
      · exact h12'
    · intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact h3
      · exact hd5'
      · exact hd6
      · exact h15'

open Classical in
/-- A four-leaf star in a four-axis block with three closed axes has an exterior
centre of degree eight. Each outer face through the chosen leaf shares a
midpoint with the other component, so its two inner contributions align. -/
theorem isolated_star_degree_eight {C D : Finset (Q 9)}
    (hleft : LocalRules C) (hright : LocalRules D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hclosed : ∀ i j : Axis, ({i, j} : Finset Axis) ∈ minimumDisplacements C D false 2 →
      (i.val < 3 → j ∈ axes) ∧ (j.val < 3 → i ∈ axes))
    {z : Q 9} (hz : parity z = true) {i : Axis} (hi : i.val < 3)
    (hstar : ∀ k ∈ axes, flip z k ∈ C)
    (hshared : ∀ j ∈ axes, i ≠ j → ∃ k : Axis, k.val < 3 ∧ flip (flip (flip z i) j) k ∈ D) :
    z ∉ C ∧ (directions C z).card = 8 := by
  have hiA : i ∈ axes := (show ∀ k : Axis, k.val < 3 → k ∈ axes by decide +kernel) i hi
  have hsub : axes ⊆ directions C z := fun k hk => (mem_directions C z k).mpr (hstar k hk)
  have hcard : axes.card = 4 := by decide
  have hbelow := card_le_card hsub
  have hzC : z ∉ C := by
    intro hzC
    rw [hleft.occupied_degree z hzC, hcard] at hbelow
    omega
  have hfaces (j : Axis) (hj : j ∈ axes) (hij : i ≠ j) :
      flip (flip z i) j ∉ C ∧ directions C (flip (flip z i) j) = {i, j} := by
    let v := flip (flip z i) j
    obtain ⟨k, hk, hD⟩ := hshared j hj hij
    change flip v k ∈ D at hD
    have hvC : v ∉ C := by
      intro hv
      have hbad := hsep v hv _ hD
      have he : hammingDist v (flip v k) = 1 := flip_adj v k
      omega
    have hvj : flip v j ∈ C := by
      simpa only [v, BalancedCriticalSpectrum.flip_flip] using hstar i hiA
    have hvi : flip v i ∈ C := by
      change flip (flip (flip z i) j) i ∈ C
      rw [flip_comm z i j, BalancedCriticalSpectrum.flip_flip]
      exact hstar j hj
    have hvpar : parity v = true := by simp [v, parity_flip, hz]
    obtain ⟨_, _, htwo⟩ := midpoint_partition hleft hright hsep hclosed hvpar hi hk hvi hD
    have hpair : ({i, j} : Finset Axis) ⊆ directions C v :=
      insert_subset ((mem_directions C v i).mpr hvi)
        (singleton_subset_iff.mpr ((mem_directions C v j).mpr hvj))
    exact ⟨hvC, (eq_of_subset_of_card_le hpair (by rw [htwo, card_pair hij])).symm⟩
  have hlarge := twice_card_le_directions_of_coherent_exterior_fragment hr hb hzC hiA hsub hfaces
  have hcap : (directions C z).card ≤ 9 := (card_le_card (subset_univ _)).trans (by simp)
  obtain ⟨m, hm⟩ := hleft.exterior_degree z hzC
  rw [hcard] at hlarge
  exact ⟨hzC, by omega⟩

open Classical in
private theorem star_word_degree {C D : Finset (Q 9)}
    (hleft : LocalRules C) (hright : LocalRules D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hclosed : ∀ i j : Axis, ({i, j} : Finset Axis) ∈ minimumDisplacements C D false 2 →
      (i.val < 3 → j ∈ axes) ∧ (j.val < 3 → i ∈ axes))
    {L R : Finset Word} (hL : ∀ w ∈ L, vertex w ∈ C) (hR : ∀ w ∈ R, vertex w ∈ D)
    (z : Word) (hz : parity (vertex z) = true)
    (hstar : ∀ k ∈ axes, adjacentWord z k ∈ L)
    (hshared : ∀ j ∈ axes, (0 : Axis) ≠ j → ∃ k : Axis, k.val < 3 ∧
      adjacentWord (adjacentWord (adjacentWord z 0) j) k ∈ R) :
    vertex z ∉ C ∧ (directions C (vertex z)).card = 8 := by
  apply isolated_star_degree_eight hleft hright hsep hr hb hclosed hz (i := 0) (by decide)
  · intro k hk
    rw [flip_vertex]
    exact hL _ (hstar k hk)
  · intro j hj hne
    obtain ⟨k, hk, hmem⟩ := hshared j hj hne
    refine ⟨k, hk, ?_⟩
    rw [flip_vertex, flip_vertex, flip_vertex]
    exact hR _ hmem

open Classical in
/-- Both opposing stars forced by a rooted four-clique with three closed axes have
exterior centres of degree eight. The two alternatives are the actual
coordinate-normalized possibilities. -/
theorem opposing_stars_degree_eight {C D : Finset (Q 9)} (h : Geometry C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hclosed : ∀ i j : Axis, ({i, j} : Finset Axis) ∈ minimumDisplacements C D false 2 →
      (i.val < 3 → j ∈ axes) ∧ (j.val < 3 → i ∈ axes))
    (htrans : ∀ ⦃i j p q : Axis⦄ ⦃x : Q 9⦄, p ≠ q →
      (∀ k, ({i, k} : Finset Axis) ∈ minimumDisplacements C D false 2 → k = j ∨ k = p ∨ k = q) →
      RidgeContact C D false [i] j x →
      RidgeContact C D false [i] j (flip (flip x p) q)) :
    ((∀ w ∈ ({0, 5, 6, 12} : Finset Word), vertex w ∈ C) ∧
      (∀ w ∈ ({3, 9, 10, 15} : Finset Word), vertex w ∈ D) ∧
      vertex 4 ∉ C ∧ (directions C (vertex 4)).card = 8 ∧
      vertex 11 ∉ D ∧ (directions D (vertex 11)).card = 8) ∨
    ((∀ w ∈ ({0, 9, 10, 12} : Finset Word), vertex w ∈ C) ∧
      (∀ w ∈ ({3, 5, 6, 15} : Finset Word), vertex w ∈ D) ∧
      vertex 8 ∉ C ∧ (directions C (vertex 8)).card = 8 ∧
      vertex 7 ∉ D ∧ (directions D (vertex 7)).card = 8) := by
  have hsep' (x : Q 9) (hx : x ∈ D) (y : Q 9) (hy : y ∈ C) :
      2 ≤ hammingDist x y := by rw [hammingDist_comm]; exact h.separated y hy x hx
  have hclosed' (i j : Axis) (hm : ({i, j} : Finset Axis) ∈ minimumDisplacements D C false 2) :
      (i.val < 3 → j ∈ axes) ∧ (j.val < 3 → i ∈ axes) := by
    rw [minimumDisplacements_swap_two D C false] at hm
    exact hclosed i j hm
  rcases opposing_stars h hclosed htrans with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · obtain ⟨ho, hc⟩ := star_word_degree h.left_rules h.right_rules h.separated hrC hbC
      hclosed hL hR 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    obtain ⟨ho', hc'⟩ := star_word_degree h.right_rules h.left_rules hsep' hrD hbD
      hclosed' hR hL 11 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    exact Or.inl ⟨hL, hR, ho, hc, ho', hc'⟩
  · obtain ⟨ho, hc⟩ := star_word_degree h.left_rules h.right_rules h.separated hrC hbC
      hclosed hL hR 8 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    obtain ⟨ho', hc'⟩ := star_word_degree h.right_rules h.left_rules hsep' hrD hbD
      hclosed' hR hL 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    exact Or.inr ⟨hL, hR, ho, hc, ho', hc'⟩

open Classical in
private theorem word_base_star {C D : Finset (Q 9)} {L R : Finset Word} {z : Word}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hL : ∀ w ∈ L, vertex w ∈ C) (hR : ∀ w ∈ R, vertex w ∈ D)
    (hz : vertex z ∉ C) (hshape : L = axes.image (adjacentWord z))
    (hcover : ∀ w : Word, (∀ i ∉ axes, vertex w i = vertex z i) →
      w ∈ L ∨ w = z ∨ (R.filter fun v => hammingDist (vertex w) (vertex v) ≤ 1).Nonempty) :
    ∀ u, (∀ i ∉ axes, u i = vertex z i) → (u ∈ C ↔ ∃ i ∈ axes, flip (vertex z) i = u) := by
  intro u hu
  obtain ⟨w, rfl⟩ := (cubeBitVec 9).surjective u
  constructor
  · intro hw
    rcases hcover w hu with hmem | hcenter | ⟨v, hv⟩
    · rw [hshape] at hmem
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hmem
      exact ⟨i, hi, flip_vertex z i⟩
    · exact False.elim (hz (hcenter ▸ hw))
    · obtain ⟨hmem, hd⟩ := mem_filter.mp hv
      have hbad := hsep _ hw _ (hR _ hmem)
      change 2 ≤ hammingDist (vertex w) (vertex v) at hbad
      omega
  · rintro ⟨i, hi, he⟩
    rw [flip_vertex] at he
    have hword := (cubeBitVec 9).injective he
    subst w
    exact hL _ (hshape.symm ▸ mem_image.mpr ⟨i, hi, rfl⟩)

set_option maxHeartbeats 1000000 in
open Classical in
/-- A four-axis clique with three closed axes supplies an actual pair of antipodal stars
with complete base membership and both exterior centre degrees equal to eight. -/
theorem opposing_stars_full_geometry {C D : Finset (Q 9)} (h : Geometry C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hclosed : ∀ i j : Axis, ({i, j} : Finset Axis) ∈ minimumDisplacements C D false 2 →
      (i.val < 3 → j ∈ axes) ∧ (j.val < 3 → i ∈ axes))
    (htrans : ∀ ⦃i j p q : Axis⦄ ⦃x : Q 9⦄, p ≠ q →
      (∀ k, ({i, k} : Finset Axis) ∈ minimumDisplacements C D false 2 → k = j ∨ k = p ∨ k = q) →
      RidgeContact C D false [i] j x →
      RidgeContact C D false [i] j (flip (flip x p) q)) :
    ∃ z : Q 9, parity z = true ∧
      (∀ u, (∀ i ∉ axes, u i = z i) → (u ∈ C ↔ ∃ i ∈ axes, flip z i = u)) ∧
      (∀ u, (∀ i ∉ axes, u i = axes.toList.foldl flip z i) →
        (u ∈ D ↔ ∃ i ∈ axes, flip (axes.toList.foldl flip z) i = u)) ∧
      axes ⊆ directions C z ∧ axes ⊆ directions D (axes.toList.foldl flip z) ∧
      (directions C z).card = 8 ∧ (directions D (axes.toList.foldl flip z)).card = 8 := by
  have hsep' (x : Q 9) (hx : x ∈ D) (y : Q 9) (hy : y ∈ C) :
      2 ≤ hammingDist x y := by rw [hammingDist_comm]; exact h.separated y hy x hx
  rcases opposing_stars_degree_eight h hrC hrD hbC hbD hclosed htrans with
    ⟨hL, hR, hzC, h8C, hzD, h8D⟩ | ⟨hL, hR, hzC, h8C, hzD, h8D⟩
  · have hab : axes.toList.foldl flip (vertex 4) = vertex 11 := by
      funext k
      rw [foldl_flip_apply _ (nodup_toList _)]
      simp only [mem_toList]
      exact (show ∀ k : Axis, (if k ∈ axes then !vertex 4 k else vertex 4 k) = vertex 11 k by decide +kernel) k
    refine ⟨vertex 4, by decide +kernel, ?_, ?_, ?_, ?_, h8C, ?_⟩
    · exact word_base_star h.separated hL hR hzC (by decide +kernel) (by decide +kernel)
    · rw [hab]
      exact word_base_star hsep' hR hL hzD (by decide +kernel) (by decide +kernel)
    · intro i hi
      apply (mem_directions _ _ _).mpr
      rw [flip_vertex]
      exact hL _ ((show ∀ i ∈ axes, adjacentWord 4 i ∈ ({0,5,6,12} : Finset Word) by decide +kernel) i hi)
    · rw [hab]
      intro i hi
      apply (mem_directions _ _ _).mpr
      rw [flip_vertex]
      exact hR _ ((show ∀ i ∈ axes, adjacentWord 11 i ∈ ({3,9,10,15} : Finset Word) by decide +kernel) i hi)
    · rwa [hab]
  · have hab : axes.toList.foldl flip (vertex 8) = vertex 7 := by
      funext k
      rw [foldl_flip_apply _ (nodup_toList _)]
      simp only [mem_toList]
      exact (show ∀ k : Axis, (if k ∈ axes then !vertex 8 k else vertex 8 k) = vertex 7 k by decide +kernel) k
    refine ⟨vertex 8, by decide +kernel, ?_, ?_, ?_, ?_, h8C, ?_⟩
    · exact word_base_star h.separated hL hR hzC (by decide +kernel) (by decide +kernel)
    · rw [hab]
      exact word_base_star hsep' hR hL hzD (by decide +kernel) (by decide +kernel)
    · intro i hi
      apply (mem_directions _ _ _).mpr
      rw [flip_vertex]
      exact hL _ ((show ∀ i ∈ axes, adjacentWord 8 i ∈ ({0,9,10,12} : Finset Word) by decide +kernel) i hi)
    · rw [hab]
      intro i hi
      apply (mem_directions _ _ _).mpr
      rw [flip_vertex]
      exact hR _ ((show ∀ i ∈ axes, adjacentWord 7 i ∈ ({3,5,6,15} : Finset Word) by decide +kernel) i hi)
    · rwa [hab]

#print axioms opposing_stars_full_geometry
#print axioms opposing_stars_degree_eight
#print axioms isolated_star_degree_eight
#print axioms opposing_stars

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueParity
