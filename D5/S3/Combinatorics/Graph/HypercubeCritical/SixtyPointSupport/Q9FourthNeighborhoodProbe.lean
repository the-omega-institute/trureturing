/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9FourthNeighborhoodProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9FourthNeighborhoodProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Count vertices reached in four steps by tracking their incidences with the third layer. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

/-! Count the fourth neighborhood using the attachments to the third layer. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
attribute [local instance] Classical.propDecidable

open private second third second_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private HammingSeven.ball root_data from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private distance_parity second_distance third_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private lemma exterior_card_of_blocking {V : Type*} [DecidableEq V]
    (L T : Finset V) (R : V → V → Prop) [DecidableRel R]
    (htwo : ∀ z ∈ L, (T.filter (R z)).card = 2)
    (hthree : ∀ w ∈ T, (L.filter (fun z => R z w)).card ≤ 3)
    (hblock : ∀ z ∈ L, ∀ w ∈ T, ∀ u ∈ T, R z w → R z u → w ≠ u →
      (L.filter (fun v => R v w)).card = 3 →
      (L.filter (fun v => R v u)).card = 1) :
    L.card ≤ (T.filter (fun w => 0 < (L.filter (fun z => R z w)).card)).card := by
  let d (w : V) := (L.filter (fun z => R z w)).card
  let weight (w : V) := 4 - d w
  let F := T.filter (fun w => 0 < d w)
  have hlower : ∀ z ∈ L, 4 ≤ ∑ w ∈ T.filter (R z), weight w := by
    intro z hz
    obtain ⟨w, u, hwu, hpair⟩ := Finset.card_eq_two.mp (htwo z hz)
    have hw : w ∈ T.filter (R z) := by rw [hpair]; simp
    have hu : u ∈ T.filter (R z) := by rw [hpair]; simp
    obtain ⟨hwT, hzw⟩ := Finset.mem_filter.mp hw
    obtain ⟨huT, hzu⟩ := Finset.mem_filter.mp hu
    have hw₃ : d w ≤ 3 := hthree w hwT
    have hu₃ : d u ≤ 3 := hthree u huT
    rw [hpair, Finset.sum_pair hwu]
    change 4 ≤ 4 - d w + (4 - d u)
    by_cases hwfull : d w = 3
    · have hu₁ : d u = 1 := hblock z hz w hwT u huT hzw hzu hwu hwfull
      omega
    by_cases hufull : d u = 3
    · have hw₁ : d w = 1 := hblock z hz u huT w hwT hzu hzw hwu.symm hufull
      omega
    omega
  have hswitch : (∑ z ∈ L, ∑ w ∈ T.filter (R z), weight w) =
      ∑ w ∈ T, d w * weight w := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have hupper : (∑ w ∈ T, d w * weight w) ≤ 4 * F.card := by
    calc
      _ = ∑ w ∈ F, d w * weight w := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro w hw hn
        have hd : d w = 0 := by simpa [F, hw] using hn
        simp [hd]
      _ ≤ ∑ _w ∈ F, 4 := by
        apply Finset.sum_le_sum
        intro w hw
        have hd : d w ≤ 3 := hthree w (Finset.mem_filter.mp hw).1
        change d w * (4 - d w) ≤ 4
        interval_cases d w <;> decide
      _ = _ := by simp [Nat.mul_comm]
  have hlow := Finset.sum_le_sum hlower
  rw [hswitch, Finset.sum_const, smul_eq_mul] at hlow
  change L.card ≤ F.card
  omega

private lemma hamming_two_four_of_blocking {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x : (C : Set (Q 9)))
    (hblock :
      let G := (hypercube 9).induce (C : Set (Q 9))
      ∀ z ∈ third G x, ∀ w ∉ HammingSeven.ball G x, ∀ u ∉ HammingSeven.ball G x, G.Adj z w → G.Adj z u → w ≠ u →
        ((third G x).filter (fun v => G.Adj v w)).card = 3 →
        ((third G x).filter (fun v => G.Adj v u)).card = 1) :
    18 ≤ (Finset.univ.filter (fun y : (C : Set (Q 9)) => hammingDist x.val y.val = 2)).card +
      (Finset.univ.filter (fun y : (C : Set (Q 9)) => hammingDist x.val y.val = 4)).card := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let N (k : ℕ) := Finset.univ.filter (fun y : (C : Set (Q 9)) => hammingDist x.val y.val = k)
  let T := Finset.univ \ HammingSeven.ball G x
  let F := T.filter (fun w => 0 < ((third G x).filter (fun z => G.Adj z w)).card)
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  obtain ⟨_, h12, hout⟩ := root_data (parity_bipartite C) hg hr.degree_eq x
  have h6 := second_card hg (hr.degree_eq x) (fun a _ => hr.degree_eq a)
  have hF : 12 ≤ F.card := by
    rw [← h12]
    apply exterior_card_of_blocking (third G x) T G.Adj
    · intro z hz
      have heq : T.filter (G.Adj z) = G.neighborFinset z \ HammingSeven.ball G x := by
        ext w
        simp [T, G.mem_neighborFinset, and_comm]
      rw [heq]
      exact hout z hz
    · intro w _
      calc
        _ ≤ (G.neighborFinset w).card := Finset.card_le_card (by
          intro z hz
          exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hz).2.symm)
        _ = 3 := by rw [G.card_neighborFinset_eq_degree, hr.degree_eq]
    · intro z hz w hw u hu
      exact hblock z hz w (Finset.mem_sdiff.mp hw).2 u (Finset.mem_sdiff.mp hu).2
  have hFsub : F ⊆ N 2 ∪ N 4 := by
    intro w hw
    obtain ⟨hwT, hpositive⟩ := Finset.mem_filter.mp hw
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpositive
    obtain ⟨hzthird, hzw⟩ := Finset.mem_filter.mp hz
    have h3 := third_distance hzthird
    have h1 : hammingDist z.val w.val = 1 := hzw
    have hu := hammingDist_triangle x.val z.val w.val
    have hp := cubeParity_ne_of_adj hzw
    have hxp : cubeParity x.val ≠ cubeParity z.val := by
      intro he
      have := (distance_parity x.val z.val).mpr he
      omega
    have hsame : cubeParity x.val = cubeParity w.val := by
      cases hx : cubeParity x.val <;> cases hz : cubeParity z.val <;>
        cases hw : cubeParity w.val <;> simp_all
    have hmod := (distance_parity x.val w.val).mpr hsame
    have h0 : hammingDist x.val w.val ≠ 0 := by
      intro he
      have he' : w = x := Subtype.ext ((hammingDist_eq_zero.mp he).symm)
      exact (Finset.mem_sdiff.mp hwT).2
        (by rw [he']; exact Finset.mem_union_left _ (Finset.mem_insert_self _ _))
    have : hammingDist x.val w.val = 2 ∨ hammingDist x.val w.val = 4 := by omega
    simpa [N] using this
  have hdis : Disjoint (second G x) F := by
    apply Finset.disjoint_left.mpr
    intro z hz hf
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hf).1).2
      (Finset.mem_union_left _ (Finset.mem_insert_of_mem hz))
  have hsub : second G x ∪ F ⊆ N 2 ∪ N 4 := by
    apply Finset.union_subset
    · intro z hz
      exact Finset.mem_union_left _ (by simpa [N] using second_distance hz)
    · exact hFsub
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_union_of_disjoint hdis, h6] at h
  change 18 ≤ (N 2).card + (N 4).card
  omega

#print axioms hamming_two_four_of_blocking
