/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: The actual twenty-point degree-two/degree-three slice has five high-high edges and only the 10/10 or 11/9 parity splits before the remaining cube obstruction.
 -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
import Batteries.Tactic.OpenPrivate

/-! Actual-input counting and low-path compression for the twenty-point slice. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSlice

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

private def paritySide {n : ℕ} (S : Finset (Q n)) (b : Bool) :
    Finset (S : Set (Q n)) :=
  Finset.univ.filter (fun x => cubeParity x.1 = b)

private theorem parity_union {n : ℕ} (S : Finset (Q n)) :
    paritySide S false ∪ paritySide S true = Finset.univ := by
  ext x
  cases h : cubeParity x.1 <;> simp [paritySide, h]

private theorem parity_bipartite {n : ℕ} (S : Finset (Q n)) :
    ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (paritySide S false : Set (S : Set (Q n)))
      (paritySide S true : Set (S : Set (Q n))) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hx0 := (Finset.mem_filter.mp hx).2
    have hx1 := (Finset.mem_filter.mp hy).2
    exact Bool.false_ne_true (hx0.symm.trans hx1)
  · intro x y hxy
    have hne := cubeParity_ne_of_adj hxy
    cases hx : cubeParity x.1 <;> cases hy : cubeParity y.1 <;>
      simp_all [paritySide]

private theorem positive_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) (v : V) :
    v ∈ L ∨ v ∈ R := by
  have hp : 0 < G.degree v := by
    rcases hdeg v with h | h <;> omega
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hp
  rcases hpart.mem_of_adj hvw with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

private theorem degree_parts_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    Disjoint L R ∧ L ∪ R = Finset.univ := by
  have hd : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Set.disjoint_left.mp hpart.disjoint hv hw
  refine ⟨hd, ?_⟩
  ext v
  constructor
  · intro _; exact Finset.mem_univ _
  · intro _; exact Finset.mem_union.mpr (positive_partition hpart hdeg v)

private theorem low_partition_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hcount : (degreeTwo G Finset.univ).card = 10) :
    (degreeTwo G L).card + (degreeTwo G R).card = 10 := by
  obtain ⟨hd, hu⟩ := degree_parts_cover hpart hdeg
  have hdl : Disjoint (degreeTwo G L) (degreeTwo G R) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hv).1
      (Finset.mem_filter.mp hw).1
  have hu2 : degreeTwo G L ∪ degreeTwo G R = degreeTwo G Finset.univ := by
    simp only [degreeTwo, ← Finset.filter_union, hu]
  rw [← Finset.card_union_of_disjoint hdl, hu2, hcount]

private theorem parity_split
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hL : L.card + R.card = 20)
    (hcount : (degreeTwo G Finset.univ).card = 10) :
    (L.card = 10 ∧ R.card = 10 ∧
        (degreeTwo G L).card = 5 ∧ (degreeTwo G R).card = 5) ∨
      (L.card = 11 ∧ R.card = 9 ∧
        (degreeTwo G L).card = 8 ∧ (degreeTwo G R).card = 2) ∨
      (L.card = 9 ∧ R.card = 11 ∧
        (degreeTwo G L).card = 2 ∧ (degreeTwo G R).card = 8) := by
  let a := L.card
  let b := R.card
  let p := (degreeTwo G L).card
  let q := (degreeTwo G R).card
  have hpq : p + q = 10 := low_partition_card hpart hdeg hcount
  have hpartsL := parts_card G hdeg L
  have hpartsR := parts_card G hdeg R
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq (s := L) (t := R) hpart
  rw [sum_degrees_parts G hdeg L, sum_degrees_parts G hdeg R] at hsum
  have hrel : 3 * a - p = 3 * b - q := by
    have hLa : p + (degreeThree G L).card = a := by simpa [a, p] using hpartsL
    have hRb : q + (degreeThree G R).card = b := by simpa [b, q] using hpartsR
    omega
  have hab : a + b = 20 := by simpa [a, b] using hL
  have bounds : p ≤ a ∧ q ≤ b := by
    constructor
    · change (degreeTwo G L).card ≤ L.card
      unfold degreeTwo
      exact Finset.card_filter_le _ _
    · change (degreeTwo G R).card ≤ R.card
      unfold degreeTwo
      exact Finset.card_filter_le _ _
  dsimp [a, b, p, q] at hab hpq hrel bounds ⊢
  omega

private theorem high_high_edge_count
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hN : Fintype.card V = 20)
    (hq : (degreeTwo G Finset.univ).card = 10) :
    (graph G).edgeFinset.card = 5 := by
  let lo := degreeTwo G Finset.univ
  let hi := degreeThree G Finset.univ
  have hparts := parts_card G hdeg Finset.univ
  have hlohigh (x : V) (hx : x ∈ lo) :
      degreeThree G (G.neighborFinset x) = G.neighborFinset x := by
    ext y
    simp only [degreeThree, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · exact And.left
    · intro hxy
      rcases hdeg y with hy2 | hy3
      · exact (hlow hxy (Finset.mem_filter.mp hx).2 hy2).elim
      · exact ⟨hxy, hy3⟩
  have hlowhighcard :
      ∑ x ∈ lo, (degreeThree G (G.neighborFinset x)).card = 20 := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [hlohigh x hx])]
    simp only [SimpleGraph.card_neighborFinset_eq_degree]
    rw [show (∑ x ∈ lo, G.degree x) = ∑ _x ∈ lo, 2 by
      apply Finset.sum_congr rfl; intro x hx; exact (Finset.mem_filter.mp hx).2]
    simp [lo, hq]
  have hdouble :
      (∑ x ∈ lo, (degreeThree G (G.neighborFinset x)).card) =
        ∑ y ∈ hi, (degreeTwo G (G.neighborFinset y)).card := by
    rw [show (∑ x ∈ lo, (degreeThree G (G.neighborFinset x)).card) =
      ∑ x ∈ lo, (hi.bipartiteAbove G.Adj x).card by
        apply Finset.sum_congr rfl; intro x hx
        congr 1
        ext y
        simp only [Finset.mem_bipartiteAbove, SimpleGraph.mem_neighborFinset,
          hi, degreeThree, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hxy, hy⟩; exact ⟨hy, hxy⟩
        · rintro ⟨hy, hxy⟩; exact ⟨hxy, hy⟩]
    rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    apply Finset.sum_congr rfl
    intro y hy
    congr 1
    ext x
    simp only [Finset.mem_bipartiteBelow, SimpleGraph.mem_neighborFinset,
      lo, degreeTwo, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hxy⟩; exact ⟨hxy.symm, hx⟩
    · rintro ⟨hxy, hx⟩; exact ⟨hx, hxy.symm⟩
  have hsumlow (y : V) (hy : y ∈ hi) :
      (degreeTwo G (G.neighborFinset y)).card +
          (degreeThree G (G.neighborFinset y)).card = 3 := by
    exact (neighbor_parts_card hdeg y).trans (Finset.mem_filter.mp hy).2
  have hsumhigh :
      ∑ y ∈ hi, (degreeThree G (G.neighborFinset y)).card = 10 := by
    have htotal : ∑ y ∈ hi, G.degree y = 30 := by
      rw [show (∑ y ∈ hi, G.degree y) = ∑ _y ∈ hi, 3 by
        apply Finset.sum_congr rfl; intro y hy; exact (Finset.mem_filter.mp hy).2]
      have hhi : hi.card = 10 := by
        dsimp [hi]
        rw [Finset.card_univ, hN, hq] at hparts
        omega
      simp [hhi, Nat.mul_comm]
    rw [show (∑ y ∈ hi, G.degree y) =
      ∑ y ∈ hi, ((degreeTwo G (G.neighborFinset y)).card +
        (degreeThree G (G.neighborFinset y)).card) by
        apply Finset.sum_congr rfl; intro y hy
        exact (neighbor_parts_card hdeg y).symm, Finset.sum_add_distrib] at htotal
    rw [← hdouble, hlowhighcard] at htotal
    omega
  have hgraphsum :
      ∑ x : High G, (graph G).degree x =
        ∑ y ∈ hi, (degreeThree G (G.neighborFinset y)).card := by
    apply Finset.sum_bij (fun x _ => x.val)
    · intro x _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩
    · intro x _ y _ hxy; exact Subtype.ext hxy
    · intro y hy
      have hy3 := Finset.mem_filter.mp hy
      exact ⟨⟨y, hy3.2⟩, Finset.mem_univ _, rfl⟩
    · intro x _
      exact graph_degree G x
  have hgraphedges := (graph G).sum_degrees_eq_twice_card_edges
  rw [hgraphsum, hsumhigh] at hgraphedges
  omega

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

/- The public obstruction claim is retained at the original actual-support telescope.
   The final five-vertex and signed-word elimination is the next private proof unit. -/
def claim : Prop :=
  ∃ (n : ℕ) (S : Finset (Q n)),
    ∃ L R : Finset {x : Q n // x ∈ S},
      let G := (hypercube n).induce {x | x ∈ S}
      G.IsBipartiteWith (L : Set {x : Q n // x ∈ S})
        (R : Set {x : Q n // x ∈ S}) ∧
      S.card = 20 ∧
      (∀ x, G.degree x = 2 ∨ G.degree x = 3) ∧
      (degreeTwo G Finset.univ).card = 10 ∧
      (∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False) ∧
      IsBalanced S

/- The exact actual-support telescope yields the derived girth, parity alternatives,
   and the five-edge high graph.  The remaining private unit is the elimination of
   these alternatives by actual cube words and Huang signs. -/
theorem actual_twenty_point_slice_data (h : claim) :
    ∃ (n : ℕ) (S : Finset (Q n)),
      ∃ L R : Finset {x : Q n // x ∈ S},
        let G := (hypercube n).induce {x | x ∈ S}
        G.IsBipartiteWith (L : Set {x : Q n // x ∈ S})
          (R : Set {x : Q n // x ∈ S}) ∧
        S.card = 20 ∧
        (∀ x, G.degree x = 2 ∨ G.degree x = 3) ∧
        (degreeTwo G Finset.univ).card = 10 ∧
        (∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False) ∧
        IsBalanced S ∧
        (8 : ℕ∞) ≤ G.egirth ∧
        (∃ P T : Finset {x : Q n // x ∈ S},
          G.IsBipartiteWith (P : Set {x : Q n // x ∈ S})
            (T : Set {x : Q n // x ∈ S}) ∧
          ((P.card = 10 ∧ T.card = 10 ∧
              (degreeTwo G P).card = 5 ∧ (degreeTwo G T).card = 5) ∨
           (P.card = 11 ∧ T.card = 9 ∧
              (degreeTwo G P).card = 8 ∧ (degreeTwo G T).card = 2) ∨
           (P.card = 9 ∧ T.card = 11 ∧
              (degreeTwo G P).card = 2 ∧ (degreeTwo G T).card = 8))) ∧
        (G.induce {v | G.degree v = 3}).edgeFinset.card = 5 ∧
        (∀ P T : Finset (S : Set (Q n)),
          G.IsBipartiteWith (P : Set (S : Set (Q n))) (T : Set (S : Set (Q n))) →
          (∀ x : SideHigh G P, (compressed G P).degree x +
              (degreeThree G (G.neighborFinset x.val)).card = 3) ∧
          (∀ x y z, (compressed G P).Adj x y → (compressed G P).Adj y z →
              (compressed G P).Adj z x → False) ∧
          (T.card = 9 → ∀ x ∈ degreeThree G P,
            (∀ y, G.Adj x y → G.degree y = 3 →
              degreeThree G (G.neighborFinset y) = {x}) ∧
            (∀ y ∈ T, ¬ G.Adj x y → hammingDist x.val y.val = 3)) ∧
          ((degreeThree G P).card = 3 → (degreeTwo G T).card = 2 → T.card = 9 →
            ∃ u v w a b, ∃ Z : SideHigh G T,
              u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ a ≠ b ∧
              degreeThree G P = {u, v, w} ∧ degreeTwo G T = {a, b} ∧
              G.neighborFinset a = {u, v} ∧ G.neighborFinset b = {v, w} ∧
              degreeThree G (G.neighborFinset v) = {Z.val} ∧
              (compressed G T).degree Z = 2 ∧
              ∀ z, (compressed G T).Adj Z z →
                degreeThree G (G.neighborFinset z.val) = ∅)) := by
  rcases h with ⟨n, S, L, R, hpart, hScard, hdeg, hq, hlow, ⟨sigma, hswitch⟩⟩
  let hbal : IsBalanced S := ⟨sigma, hswitch⟩
  let G := (hypercube n).induce {x | x ∈ S}
  have hparity : G.IsBipartiteWith
      (paritySide S false : Set (S : Set (Q n)))
      (paritySide S true : Set (S : Set (Q n))) := parity_bipartite S
  have hparity_disjoint : Disjoint (paritySide S false) (paritySide S true) := by
    simpa only [Finset.disjoint_coe] using hparity.disjoint
  have hparity_card :
      (paritySide S false).card + (paritySide S true).card = S.card := by
    rw [← Finset.card_union_of_disjoint hparity_disjoint, parity_union]
    simp
  have hparity_card20 :
      (paritySide S false).card + (paritySide S true).card = 20 :=
    hparity_card.trans hScard
  have hsplit := parity_split hparity hdeg hparity_card20 hq
  have hcardV : Fintype.card (S : Set (Q n)) = 20 := by
    simpa using hScard
  have hedge := high_high_edge_count hdeg hlow hcardV hq
  refine ⟨n, S, L, R, ?_, hScard, hdeg, hq, hlow, hbal,
    BalancedCubeGirth.eight_le_egirth S hbal, ?_, ?_, ?_⟩
  · exact hpart
  · refine ⟨paritySide S false, paritySide S true, hparity, ?_⟩
    exact hsplit
  · change (graph G).edgeFinset.card = 5
    exact hedge
  · intro P T hp
    have hg := BalancedCubeGirth.eight_le_egirth S hbal
    refine ⟨compressed_degree hp hdeg hlow hg,
      compressed_triangle_free hp hg, ?_, ?_⟩
    · intro hT x hx
      have hx0 := Finset.mem_filter.mp hx
      refine ⟨(nine_side_no_high_wedge hp hdeg hlow hg hT hx0.1 hx0.2).2, ?_⟩
      intro y hy hxy
      obtain ⟨a, b, hxa, hab, hby, hxb, hay⟩ :=
        nine_side_three_step_cover hp hdeg hlow hg hT hx0.1 hx0.2 hy hxy
      exact selected_three_hamming hbal hxa hab hby hxb hay
    · intro hP3 hT2 hT
      exact eleven_nine_central_obstruction hp hdeg hlow hg hP3 hT2 hT

#print axioms actual_twenty_point_slice_data

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSlice
