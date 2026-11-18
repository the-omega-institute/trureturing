/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: The actual twenty-point slice reduces to paired squares with leaves after excluding 11/9 and paired pentagons.
 -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSquareLeaf
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
import Batteries.Tactic.OpenPrivate

/-! Actual-input counting and low-path compression for the twenty-point slice. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSlice

open private paired_cycle_nonembedding from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonExclusion

open private sq crossNbr paired_square_labels from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSquareLeaf

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

open private SideHigh compressed compressed_degree compressed_triangle_free
  nine_side_no_high_wedge nine_side_three_step_cover selected_three_hamming
  eleven_nine_central_obstruction from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private eleven_nine_nonembedding from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private SquareLeaf symmetric_paired_types from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric

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

/- The original actual-support telescope reduces to paired squares with leaves.
   The 11/9 orientations and the paired-pentagon branch are excluded. -/
private theorem actual_twenty_point_slice_data (h : claim) :
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
          P.card = 10 ∧ T.card = 10 ∧
            (degreeTwo G P).card = 5 ∧ (degreeTwo G T).card = 5 ∧
            (SquareLeaf (compressed G P) ∧ SquareLeaf (compressed G T) ∧
              ∃ eP : sq ≃g compressed G P, ∃ eT : sq ≃g compressed G T,
                ∀ i j, G.Adj (eP i).val (eT j).val ↔ j ∈ crossNbr i)) ∧
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
  have hhigh (T : Finset (S : Set (Q n))) {a b : ℕ} (hT : T.card = a)
      (hlo : (degreeTwo G T).card = b) : (degreeThree G T).card = a - b := by
    have hp := parts_card G hdeg T
    omega
  have hsym : (paritySide S false).card = 10 ∧ (paritySide S true).card = 10 ∧
      (degreeTwo G (paritySide S false)).card = 5 ∧
      (degreeTwo G (paritySide S true)).card = 5 := by
    rcases hsplit with hs | hs | hs
    · exact hs
    · have hp : (degreeThree G (paritySide S false)).card = 3 :=
        hhigh _ hs.1 hs.2.2.1
      have ht : (degreeThree G (paritySide S true)).card = 7 :=
        hhigh _ hs.2.1 hs.2.2.2
      exact (eleven_nine_nonembedding hparity hdeg hlow hbal
        hp hs.2.2.2 ht hs.2.1).elim
    · have hp : (degreeThree G (paritySide S false)).card = 7 :=
        hhigh _ hs.1 hs.2.2.1
      have ht : (degreeThree G (paritySide S true)).card = 3 :=
        hhigh _ hs.2.1 hs.2.2.2
      exact (eleven_nine_nonembedding hparity.symm hdeg hlow hbal
        ht hs.2.2.1 hp hs.1).elim
  have hcardV : Fintype.card (S : Set (Q n)) = 20 := by
    simpa using hScard
  have hedge := high_high_edge_count hdeg hlow hcardV hq
  refine ⟨n, S, L, R, ?_, hScard, hdeg, hq, hlow, hbal,
    BalancedCubeGirth.eight_le_egirth S hbal, ?_, ?_, ?_⟩
  · exact hpart
  · refine ⟨paritySide S false, paritySide S true, hparity, ?_⟩
    refine ⟨hsym.1, hsym.2.1, hsym.2.2.1, hsym.2.2.2, ?_⟩
    have hp : (degreeThree G (paritySide S false)).card = 5 :=
      hhigh _ hsym.1 hsym.2.2.1
    have ht : (degreeThree G (paritySide S true)).card = 5 :=
      hhigh _ hsym.2.1 hsym.2.2.2
    have hcases := symmetric_paired_types hparity hdeg hlow
      (BalancedCubeGirth.eight_le_egirth S hbal) hp ht
      hsym.2.2.1 hsym.2.2.2
    rcases hcases with ⟨hLc, hRc⟩ | hsq
    · exact (paired_cycle_nonembedding hparity hdeg hlow hbal hLc hRc).elim
    · exact ⟨hsq.1, hsq.2, paired_square_labels hparity hdeg hlow
        (BalancedCubeGirth.eight_le_egirth S hbal) hp ht hsq.1 hsq.2⟩
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
