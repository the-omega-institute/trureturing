/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParityFoldedBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParityFoldedBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Parity counts and coordinate deletion for balanced cubic cube supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BalancedHalfCardinality
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedExclusion

/-! Coordinate halves of a Huang-balanced cubic support have lower bounds on
both parity counts. Deleting one coordinate identifies each parity class with
a smaller cube and sends the opposite-parity neighborhood to a closed neighborhood. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityFoldedBoundary

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count flip_adj
  flip_flip)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeLowerBound (coordinateSlice)
open GirthSliceCounting (degreeTwo degreeThree)
open CoordinateHalves.BalancedHalfCardinality (half_cardinality)
open private cubeParity cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private coordinate_slice_degree_cases coordinate_slice_low_independent low_slice_card_eq_q
  parts_card sum_degrees_parts paritySide parity_bipartite parity_union from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private reindex reindex_regular reindex_balanced reindex_slice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private adjacent_exists_flip two_step_first_direction_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
attribute [local instance] Classical.propDecidable

/-- Global parity of a Boolean cube vertex, with false denoting even parity. -/
abbrev parity {n : ℕ} (x : Q n) : Bool := cubeParity x

/-- Restrict a finite set of cube vertices to one global parity. -/
def parityPart {n : ℕ} (S : Finset (Q n)) (p : Bool) : Finset (Q n) :=
  S.filter (fun x => parity x = p)

private theorem paritySide_card (S : Finset (Q 9)) (p : Bool) :
    (paritySide S p).card = (parityPart S p).card := by
  have he : (paritySide S p).map ⟨Subtype.val, Subtype.val_injective⟩ = parityPart S p := by
    ext x
    simp only [paritySide, parityPart, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.Embedding.coeFn_mk]
    exact ⟨fun ⟨v, hv, he⟩ => he ▸ ⟨v.property, hv⟩, fun ⟨hx, hp⟩ => ⟨⟨x, hx⟩, hp, rfl⟩⟩
  rw [← he, Finset.card_map]

private theorem parity_bipartition (S : Finset (Q 9)) (p : Bool) :
    ((hypercube 9).induce (S : Set (Q 9))).IsBipartiteWith
      (paritySide S p : Set _) (paritySide S (!p) : Set _) := by
  cases p
  · exact parity_bipartite S
  · exact (parity_bipartite S).symm

private theorem parity_partition_card (S : Finset (Q 9)) (p : Bool)
    (P : ↥(S : Set (Q 9)) → Prop) [DecidablePred P] :
    ((paritySide S p).filter P).card + ((paritySide S (!p)).filter P).card =
      (Finset.univ.filter P).card := by
  have hcover : paritySide S p ∪ paritySide S (!p) = Finset.univ := by
    cases p
    · exact parity_union S
    · simpa only [Bool.not_true, Finset.union_comm] using parity_union S
  have hd : Disjoint ((paritySide S p).filter P) ((paritySide S (!p)).filter P) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (parity_bipartition S p).disjoint
      (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
  rw [← Finset.card_union_of_disjoint hd, ← Finset.filter_union, hcover]

private theorem parity_reindex (e : Fin 9 ≃ Fin 9) (x : Q 9) :
    parity (reindex e x) = parity x := by
  change (∑ k, x (e.symm k)) = ∑ k, x k
  exact Equiv.sum_comp e.symm x

private theorem parityPart_reindex (e : Fin 9 ≃ Fin 9) (S : Finset (Q 9)) (p : Bool) :
    parityPart (S.image (reindex e)) p = (parityPart S p).image (reindex e) := by
  unfold parityPart
  rw [Finset.filter_image]
  simp only [parity_reindex]

private theorem balanced_common_neighbor_unique {C : Finset (Q 9)} (hb : IsBalanced C)
    {a b u v : Q 9} (ha : a ∈ C) (hbC : b ∈ C) (hu : u ∈ C) (hv : v ∈ C) (hab : a ≠ b)
    (hau : (hypercube 9).Adj a u) (hub : (hypercube 9).Adj u b)
    (hav : (hypercube 9).Adj a v) (hvb : (hypercube 9).Adj v b) : u = v := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip hau
  obtain ⟨j, hj⟩ := adjacent_exists_flip hub
  obtain ⟨k, hk⟩ := adjacent_exists_flip hav
  obtain ⟨l, hl⟩ := adjacent_exists_flip hvb
  rw [hi] at hj
  rw [hk] at hl
  have hij : i ≠ j := by
    rintro rfl
    exact hab ((hj.trans (flip_flip a i)).symm)
  have hkl : k ≠ l := by
    rintro rfl
    exact hab ((hl.trans (flip_flip a k)).symm)
  have he := two_step_first_direction_eq hb hij hkl ha (hi ▸ hu) (hj ▸ hbC) (hk ▸ hv)
    (hj.symm.trans hl)
  rw [hi, hk, he]

/-- The two global parity classes of a cubic support of order `6 * m`
have cardinality `3 * m` each. -/
theorem cubic_parityPart_card {C : Finset (Q 9)} {m : ℕ} (hC : C.card = 6 * m)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (p : Bool) :
    (parityPart C p).card = 3 * m := by
  have hs := parity_partition_card C p (fun _ => True)
  simp only [Finset.filter_true, Finset.card_univ] at hs
  rw [show Fintype.card (↥(C : Set (Q 9))) = C.card by simp, hC] at hs
  have he := SimpleGraph.isBipartiteWith_sum_degrees_eq
    (parity_bipartition C p)
  simp only [hr.degree_eq, Finset.sum_const, smul_eq_mul] at he
  rw [← paritySide_card]
  omega

/-- A coordinate half of order `N` has at least `⌈2m/3⌉` points on either parity
side and at least `⌈(3N-m)/6⌉` as a function of its order. At support order 78,
a parity side of size ten would create a selected four-cycle. -/
theorem coordinate_half_parity_bounds {C : Finset (Q 9)} {m : ℕ} (hC : C.card = 6 * m)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (j : Fin 9) (b p : Bool) :
    let H := C.filter (fun x => x j = b)
    let N := (parityPart H p).card
    2 * m ≤ 3 * N ∧ 3 * H.card ≤ 6 * N + m ∧ (m = 13 → 11 ≤ N) := by
  let e := Equiv.swap j (0 : Fin 9)
  let T := C.image (reindex e)
  let S := coordinateSlice T b
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S p
  let R := paritySide S (!p)
  have hreg := reindex_regular hr e
  have hbal := reindex_balanced hb e
  have hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3 :=
    fun x => coordinate_slice_degree_cases x.property hreg
  have hT : T.card = 6 * m := by
    rw [show T = C.image (reindex e) from rfl,
      Finset.card_image_of_injective _ (reindex e).injective, hC]
  have hcross : 6 * directionEdges T 0 = T.card := by
    simpa using direction_edge_count (d := 3) T hreg hbal 0
  have hlow_total : (degreeTwo G Finset.univ).card = directionEdges T 0 :=
    low_slice_card_eq_q hreg
  have hlow : (degreeTwo G L).card + (degreeTwo G R).card = m := by
    have h := parity_partition_card S p (fun x => G.degree x = 2)
    change (degreeTwo G L).card + (degreeTwo G R).card = (degreeTwo G Finset.univ).card at h
    rw [h, hlow_total]
    omega
  have hL := parts_card G hdeg L
  have hR := parts_card G hdeg R
  have hbip := parity_bipartition S p
  have he : 2 * (degreeTwo G L).card + 3 * (degreeThree G L).card =
      2 * (degreeTwo G R).card + 3 * (degreeThree G R).card :=
    (sum_degrees_parts G hdeg L).symm.trans
      ((SimpleGraph.isBipartiteWith_sum_degrees_eq hbip).trans (sum_degrees_parts G hdeg R))
  have hsum := parity_partition_card S p (fun _ => True)
  simp only [Finset.filter_true, Finset.card_univ] at hsum
  rw [show Fintype.card (↥(S : Set (Q 9))) = S.card by simp] at hsum
  change L.card + R.card = S.card at hsum
  have hS : S = (C.filter (fun x => x j = b)).image (reindex e) := reindex_slice C j b
  have hsize : S.card = (C.filter (fun x => x j = b)).card := by
    rw [hS, Finset.card_image_of_injective _ (reindex e).injective]
  have hsizeL : L.card = (parityPart (C.filter (fun x => x j = b)) p).card := by
    rw [paritySide_card, hS, parityPart_reindex,
      Finset.card_image_of_injective _ (reindex e).injective]
  have ⟨hmin, hmod⟩ := half_cardinality hC hr hb j b
  rw [← hsize] at hmin hmod
  dsimp only
  rw [← hsize, ← hsizeL]
  refine ⟨by omega, by omega, fun hm => ?_⟩
  by_contra! hsmall
  have hleft : (degreeTwo G L).card = 2 := by omega
  have hright : (degreeThree G R).card = 2 := by omega
  obtain ⟨a, c, hac, hlowSet⟩ := Finset.card_eq_two.mp hleft
  obtain ⟨u, v, huv, hhighSet⟩ := Finset.card_eq_two.mp hright
  have neighboring (x : (S : Set (Q 9))) (hx : x ∈ degreeTwo G L) :
      G.neighborFinset x = degreeThree G R := by
    have hsub : G.neighborFinset x ⊆ degreeThree G R := by
      intro y hy
      have hxy := (G.mem_neighborFinset x y).mp hy
      have hxL := (Finset.mem_filter.mp hx).1
      have hx2 := (Finset.mem_filter.mp hx).2
      have hyR := (hbip.mem_of_mem_adj hxL hxy)
      rcases hdeg y with hy2 | hy3
      · exact (coordinate_slice_low_independent hreg hbal hxy hx2 hy2).elim
      · exact Finset.mem_filter.mpr ⟨hyR, hy3⟩
    apply Finset.eq_of_subset_of_card_le hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    have hx2 : G.degree x = 2 := (Finset.mem_filter.mp hx).2
    exact le_of_eq (hright.trans hx2.symm)
  have ha := neighboring a (by rw [hlowSet]; simp)
  have hc := neighboring c (by rw [hlowSet]; simp)
  have hau := (G.mem_neighborFinset a u).mp (by rw [ha, hhighSet]; simp)
  have hcu := (G.mem_neighborFinset c u).mp (by rw [hc, hhighSet]; simp)
  have hav := (G.mem_neighborFinset a v).mp (by rw [ha, hhighSet]; simp)
  have hcv := (G.mem_neighborFinset c v).mp (by rw [hc, hhighSet]; simp)
  apply huv
  apply Subtype.ext
  exact balanced_common_neighbor_unique hbal (Finset.mem_filter.mp a.property).1
    (Finset.mem_filter.mp c.property).1
    (Finset.mem_filter.mp u.property).1 (Finset.mem_filter.mp v.property).1
    (fun heq => hac (Subtype.ext heq)) hau hcu.symm hav hcv.symm

/-- Excluding a half of size 20 forces ten points of each parity in that half
of an order-72 balanced cubic support. -/
theorem ten_le_coordinate_half_parity_of_no_twenty_half {C : Finset (Q 9)}
    (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (j : Fin 9) (b p : Bool)
    (h20 : (C.filter (fun x => x j = b)).card ≠ 20) :
    10 ≤ (parityPart (C.filter (fun x => x j = b)) p).card := by
  have h22 : (C.filter (fun x => x j = b)).card ≠ 22 := by
    let e := Equiv.swap j (0 : Fin 9)
    have hcard : (C.image (reindex e)).card = 72 := by
      rw [Finset.card_image_of_injective _ (reindex e).injective, hC]
    intro hs
    apply CoordinateHalves.Q9TwentyTwoPairedExclusion.no_twenty_two_half
      hcard (reindex_regular hr e) (reindex_balanced hb e) b
    rw [show coordinateSlice (C.image (reindex e)) b =
      (C.filter (fun x => x j = b)).image (reindex e) from reindex_slice C j b,
      Finset.card_image_of_injective _ (reindex e).injective, hs]
  have h72 : C.card = 6 * 12 := hC
  have ⟨hmin, hmod⟩ := half_cardinality h72 hr hb j b
  have ⟨_, hbalance, _⟩ := coordinate_half_parity_bounds h72 hr hb j b p
  change 5 * 12 ≤ 3 * (C.filter (fun x => x j = b)).card at hmin
  change (C.filter (fun x => x j = b)).card % 2 = 12 % 2 at hmod
  omega

/-- Delete a cube coordinate, keeping the remaining coordinates in order. -/
def dropCoordinate {n : ℕ} (i : Fin (n + 1)) (x : Q (n + 1)) : Q n :=
  fun k => x (i.succAbove k)

private theorem dropCoordinate_flip_drop {n : ℕ} (i : Fin (n + 1)) (x : Q (n + 1)) :
    dropCoordinate i (flip x i) = dropCoordinate i x := by
  funext k
  simp [dropCoordinate, BalancedCriticalSpectrum.flip, Fin.succAbove_ne]

private theorem dropCoordinate_flip_keep {n : ℕ} (i : Fin (n + 1)) (x : Q (n + 1))
    (k : Fin n) :
    dropCoordinate i (flip x (i.succAbove k)) = flip (dropCoordinate i x) k := by
  funext l
  by_cases h : l = k
  · subst l
    simp [dropCoordinate, BalancedCriticalSpectrum.flip]
  · have h' : i.succAbove l ≠ i.succAbove k :=
      fun he => h (Fin.succAbove_right_injective he)
    simp [dropCoordinate, BalancedCriticalSpectrum.flip, h, h']

private theorem dropCoordinate_inj_on_parity {n : ℕ} (i : Fin (n + 1)) (p : Bool) :
    Set.InjOn (dropCoordinate i) {x | parity x = p} := by
  intro x hx y hy hxy
  have hoff (k : Fin (n + 1)) (hk : k ≠ i) : x k = y k := by
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
    exact congrFun hxy l
  by_contra hne
  have hi : x i ≠ y i := fun he => hne (funext fun k => by
    by_cases hk : k = i
    · simpa [hk] using he
    · exact hoff k hk)
  have hflip : y = flip x i := by
    funext k
    by_cases hk : k = i
    · subst k
      cases hxi : x i <;> cases hyi : y i <;> simp_all
    · simpa [BalancedCriticalSpectrum.flip, hk] using (hoff k hk).symm
  have hadj : (hypercube (n + 1)).Adj x y := hflip.symm ▸ flip_adj x i
  exact cubeParity_ne_of_adj hadj (hx.trans hy.symm)

private theorem parity_eq_not_of_adj {n : ℕ} {x y : Q n}
    (hxy : (hypercube n).Adj x y) : parity y = !parity x := by
  have h : parity x ≠ parity y := cubeParity_ne_of_adj hxy
  cases hx : parity x <;> cases hy : parity y <;> simp_all

private theorem parity_flip {n : ℕ} (x : Q n) (i : Fin n) :
    parity (flip x i) = !parity x :=
  parity_eq_not_of_adj (flip_adj x i)

/-- Deleting a coordinate is a bijection from either global parity class of
`Q (n + 1)` onto `Q n`. -/
def parityFold {n : ℕ} (i : Fin (n + 1)) (p : Bool) :
    {x : Q (n + 1) // parity x = p} ≃ Q n :=
  Equiv.ofBijective (fun x => dropCoordinate i x.val) (by
    constructor
    · intro x y h
      exact Subtype.ext (dropCoordinate_inj_on_parity i p x.property y.property h)
    · intro z
      let x : Q (n + 1) := i.insertNth false z
      have hz : dropCoordinate i x = z := by
        funext k
        exact Fin.insertNth_apply_succAbove (α := fun _ => Bool) i false z k
      by_cases hx : parity x = p
      · exact ⟨⟨x, hx⟩, hz⟩
      · have hflip : parity (flip x i) = p := by
          rw [parity_flip]
          cases hp : parity x <;> cases p <;> simp_all
        exact ⟨⟨flip x i, hflip⟩, (dropCoordinate_flip_drop i x).trans hz⟩)

private theorem dropCoordinate_adj_iff {n : ℕ} (i : Fin (n + 1)) {x y : Q (n + 1)}
    (hparity : parity y = !parity x) :
    (hypercube (n + 1)).Adj x y ↔
      dropCoordinate i x = dropCoordinate i y ∨
        (hypercube n).Adj (dropCoordinate i x) (dropCoordinate i y) := by
  constructor
  · intro h
    obtain ⟨j, rfl⟩ := adjacent_exists_flip h
    by_cases hj : j = i
    · subst j
      exact Or.inl (dropCoordinate_flip_drop i x).symm
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [dropCoordinate_flip_keep]
      exact Or.inr (flip_adj _ _)
  · rintro (he | ha)
    · have hy : y = flip x i :=
        dropCoordinate_inj_on_parity i (!parity x) hparity (parity_flip x i)
          (he.symm.trans (dropCoordinate_flip_drop i x).symm)
      rw [hy]
      exact flip_adj _ _
    · obtain ⟨k, hk⟩ := adjacent_exists_flip ha
      have hy : y = flip x (i.succAbove k) :=
        dropCoordinate_inj_on_parity i (!parity x) hparity (parity_flip x _)
          (hk.trans (dropCoordinate_flip_keep i x k).symm)
      rw [hy]
      exact flip_adj _ _

/-- Under the parity-class bijections, an edge to the opposite parity becomes
equality or adjacency in the smaller cube. -/
theorem parityFold_adj_iff {n : ℕ} (i : Fin (n + 1)) (p : Bool)
    (x : {x : Q (n + 1) // parity x = p}) (y : {y : Q (n + 1) // parity y = !p}) :
    (hypercube (n + 1)).Adj x.val y.val ↔
      parityFold i p x = parityFold i (!p) y ∨
        (hypercube n).Adj (parityFold i p x) (parityFold i (!p) y) :=
  dropCoordinate_adj_iff i (y.property.trans (congrArg Bool.not x.property).symm)

/-- The open cube neighborhood of a set of one parity projects to the closed
neighborhood of its projection. The left-hand finset uses the opposite parity
automatically, since every cube edge reverses parity. -/
theorem image_neighbor_eq_closed_neighbor {n : ℕ} (i : Fin (n + 1)) (p : Bool)
    (A : Finset (Q (n + 1))) (hA : ∀ x ∈ A, parity x = p) :
    (Finset.univ.filter (fun y => ∃ x ∈ A, (hypercube (n + 1)).Adj x y)).image
        (dropCoordinate i) =
      Finset.univ.filter (fun v => ∃ u ∈ A.image (dropCoordinate i),
        u = v ∨ (hypercube n).Adj u v) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
    have hp := parity_eq_not_of_adj hxy
    exact ⟨dropCoordinate i x, ⟨x, hx, rfl⟩, (dropCoordinate_adj_iff i hp).mp hxy⟩
  · rintro ⟨u, ⟨x, hx, rfl⟩, huv⟩
    obtain ⟨y, hy⟩ := (parityFold i (!p)).surjective v
    have hparity : parity y.val = !parity x := y.property.trans (congrArg Bool.not (hA x hx)).symm
    change dropCoordinate i y.val = v at hy
    rw [← hy] at huv
    exact ⟨y.val, ⟨x, hx, (dropCoordinate_adj_iff i hparity).mpr huv⟩, hy⟩

/-- Projection preserves the cardinality of each single-parity set. -/
theorem card_image_dropCoordinate {n : ℕ} (i : Fin (n + 1)) (p : Bool)
    (A : Finset (Q (n + 1))) (hA : ∀ x ∈ A, parity x = p) :
    (A.image (dropCoordinate i)).card = A.card := by
  apply Finset.card_image_of_injOn
  exact fun x hx y hy hxy => dropCoordinate_inj_on_parity i p (hA x hx) (hA y hy) hxy

/-- The open neighborhood of a single-parity set has the same cardinality as
the closed neighborhood of its projection. -/
theorem card_neighbor_eq_card_closed_neighbor_image {n : ℕ} (i : Fin (n + 1)) (p : Bool)
    (A : Finset (Q (n + 1))) (hA : ∀ x ∈ A, parity x = p) :
    (Finset.univ.filter (fun y => ∃ x ∈ A, (hypercube (n + 1)).Adj x y)).card =
      (Finset.univ.filter (fun v => ∃ u ∈ A.image (dropCoordinate i),
        u = v ∨ (hypercube n).Adj u v)).card := by
  rw [← image_neighbor_eq_closed_neighbor i p A hA]
  symm
  apply card_image_dropCoordinate i (!p)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.mp hy).2
  rw [parity_eq_not_of_adj hxy, hA x hx]

/-- A split in a retained direction has the original parity counts after deletion.
For any original direction `j ≠ i`, use `Fin.exists_succAbove_eq` to recover `k`. -/
theorem card_projected_parity_half {n : ℕ} (i : Fin (n + 1)) (k : Fin n)
    (C : Finset (Q (n + 1))) (b p : Bool) :
    (((parityPart C p).image (dropCoordinate i)).filter (fun x => x k = b)).card =
      (parityPart (C.filter (fun x => x (i.succAbove k) = b)) p).card := by
  rw [Finset.filter_image]
  have hf : (parityPart C p).filter (fun x => dropCoordinate i x k = b) =
      parityPart (C.filter (fun x => x (i.succAbove k) = b)) p := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxC, hp⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hxC, (Finset.mem_filter.mp hx).2⟩, hp⟩
    · intro hx
      obtain ⟨hxC, hb⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hxC, (Finset.mem_filter.mp hx).2⟩, hb⟩
  rw [hf]
  exact card_image_dropCoordinate i p _ (fun _ hx => (Finset.mem_filter.mp hx).2)

#print axioms parity
#print axioms parityPart
#print axioms cubic_parityPart_card
#print axioms coordinate_half_parity_bounds
#print axioms ten_le_coordinate_half_parity_of_no_twenty_half
#print axioms dropCoordinate
#print axioms parityFold
#print axioms parityFold_adj_iff
#print axioms image_neighbor_eq_closed_neighbor
#print axioms card_image_dropCoordinate
#print axioms card_neighbor_eq_card_closed_neighbor_image
#print axioms card_projected_parity_half

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityFoldedBoundary
