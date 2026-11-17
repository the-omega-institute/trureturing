/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/HammingSeven
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/HammingSeven
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Balanced cubic fifty-four vertex cube supports have Hamming diameter at most seven. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
import Batteries.Tactic.OpenPrivate

/-! Two actual radius-three balls and their outward incidences force short walks.
The Moore counting method is standard; the consumer is the actual balanced cube support. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven

open SimpleGraph
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (IsBalanced)

attribute [local instance] Classical.propDecidable

open private second third mem_second root_not_second second_side third_side
  second_card third_card third_witness first_third_disjoint third_parent_unique from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private actual_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private def ball (G : SimpleGraph V) (x : V) : Finset V :=
  insert x (second G x) ∪ (G.neighborFinset x ∪ third G x)

private lemma third_subset_ball (x : V) : third G x ⊆ ball G x := by
  intro z hz
  exact Finset.mem_union_right _ (Finset.mem_union_right _ hz)

private lemma ball_walk {x z : V} (hz : z ∈ ball G x) :
    ∃ p : G.Walk x z, p.length ≤ 3 := by
  rcases Finset.mem_union.mp hz with hz | hz
  · rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨.nil, by simp⟩
    · obtain ⟨a, hxa, haz, _⟩ := mem_second.mp hz
      exact ⟨.cons hxa (.cons haz .nil), by simp⟩
  · rcases Finset.mem_union.mp hz with hz | hz
    · exact ⟨.cons (by simpa using hz) .nil, by simp⟩
    · obtain ⟨a, b, hxa, hab, hbz, _⟩ := third_witness hz
      exact ⟨.cons hxa (.cons hab (.cons hbz .nil)), by simp⟩

private lemma ball_card_of_side {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hd : ∀ v, G.degree v = 3)
    {x : V} (hx : x ∈ L) : (ball G x).card = 22 ∧ (third G x).card = 12 := by
  have h6 := second_card hg (hd x) (fun a _ => hd a)
  have h12 := third_card hpart hg (fun v => Or.inr (hd v)) hx (hd x)
    (fun a _ => hd a)
  have hempty : GirthSliceCounting.degreeTwo G (second G x) = ∅ := by
    ext v
    simp [GirthSliceCounting.degreeTwo, hd]
  rw [hempty, Finset.card_empty, Nat.add_zero] at h12
  refine ⟨?_, h12⟩
  have hleft : insert x (second G x) ⊆ L :=
    Finset.insert_subset hx (second_side hpart hx)
  have hright : G.neighborFinset x ∪ third G x ⊆ R := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hpart.mem_of_mem_adj hx (by simpa using hz)
    · exact third_side hpart hx hz
  have hdis : Disjoint (insert x (second G x)) (G.neighborFinset x ∪ third G x) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact Set.disjoint_left.mp hpart.disjoint (hleft hz) (hright hz')
  rw [ball, Finset.card_union_of_disjoint hdis,
    Finset.card_insert_of_notMem (root_not_second x), h6,
    Finset.card_union_of_disjoint (first_third_disjoint x),
    G.card_neighborFinset_eq_degree, hd, h12]

private lemma third_inner_neighbors {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) {x : V} (hx : x ∈ L)
    {z : V} (hz : z ∈ third G x) :
    (G.neighborFinset z ∩ ball G x).card = 1 := by
  obtain ⟨a, b, hxa, hab, hbz, hxb, haz, hb, hzn⟩ := third_witness hz
  have hzR := third_side hpart hx hz
  have hsingleton : G.neighborFinset z ∩ ball G x = {b} := by
    ext w
    simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hzw, hw⟩
      have hwL := hpart.symm.mem_of_mem_adj hzR hzw
      rcases Finset.mem_union.mp hw with hw | hw
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · exact (hzn (by simpa using hzw.symm)).elim
        · exact third_parent_unique hpart hg hx hw hb hzw.symm hbz hzn
      · have hwR : w ∈ R := by
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hpart.mem_of_mem_adj hx (by simpa using hw)
          · exact third_side hpart hx hw
        exact (Set.disjoint_left.mp hpart.disjoint hwL hwR).elim
    · rintro rfl
      exact ⟨hbz.symm, Finset.mem_union_left _ (Finset.mem_insert_of_mem hb)⟩
  simp [hsingleton]

private lemma root_data {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hd : ∀ v, G.degree v = 3) (x : V) :
    (ball G x).card = 22 ∧ (third G x).card = 12 ∧
      ∀ z ∈ third G x, (G.neighborFinset z \ ball G x).card = 2 := by
  have hs (L R : Finset V) (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
      (hx : x ∈ L) :
      (ball G x).card = 22 ∧ (third G x).card = 12 ∧
        ∀ z ∈ third G x, (G.neighborFinset z \ ball G x).card = 2 := by
    obtain ⟨hc, ht⟩ := ball_card_of_side hp hg hd hx
    refine ⟨hc, ht, ?_⟩
    intro z hz
    have hi := third_inner_neighbors hp hg hx hz
    have hn := Finset.card_sdiff_add_card_inter (G.neighborFinset z) (ball G x)
    rw [G.card_neighborFinset_eq_degree, hd, hi] at hn
    omega
  rcases actual_partition hpart (fun v => Or.inr (hd v)) x with hx | hx
  · exact hs L R hpart hx
  · exact hs R L hpart.symm hx

omit [DecidableEq V] in
private lemma short_walk {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hd : ∀ v, G.degree v = 3)
    (hcard : Fintype.card V = 54) (x y : V) :
    ∃ p : G.Walk x y, p.length ≤ 7 := by
  classical
  by_contra hfar
  have hdis : Disjoint (ball G x) (ball G y) := by
    apply Finset.disjoint_left.mpr
    intro z hx hy
    obtain ⟨p, hp⟩ := ball_walk hx
    obtain ⟨q, hq⟩ := ball_walk hy
    apply hfar
    refine ⟨p.append q.reverse, ?_⟩
    simp only [Walk.length_append, Walk.length_reverse]
    omega
  have hno (u : V) (hu : u ∈ ball G x) (v : V) (hv : v ∈ ball G y) :
      ¬ G.Adj u v := by
    intro huv
    obtain ⟨p, hp⟩ := ball_walk hu
    obtain ⟨q, hq⟩ := ball_walk hv
    apply hfar
    refine ⟨p.append (.cons huv q.reverse), ?_⟩
    simp only [Walk.length_append, Walk.length_cons, Walk.length_reverse]
    omega
  obtain ⟨hx22, hx12, hxout⟩ := root_data hpart hg hd x
  obtain ⟨hy22, hy12, hyout⟩ := root_data hpart hg hd y
  let S := third G x ∪ third G y
  let T := Finset.univ \ (ball G x ∪ ball G y)
  have hS : S.card = 24 := by
    rw [Finset.card_union_of_disjoint
      (hdis.mono (third_subset_ball x) (third_subset_ball y)), hx12, hy12]
  have hT : T.card = 10 := by
    have hc := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (ball G x ∪ ball G y))
    rw [Finset.card_union_of_disjoint hdis, hx22, hy22, Finset.card_univ, hcard] at hc
    change T.card + (22 + 22) = 54 at hc
    omega
  have hlow : ∀ z ∈ S, 2 ≤ (T.bipartiteAbove G.Adj z).card := by
    intro z hz
    have hxsub (hzx : z ∈ third G x) :
        G.neighborFinset z \ ball G x ⊆ T.bipartiteAbove G.Adj z := by
      intro w hw
      have hm := Finset.mem_sdiff.mp hw
      have hzw : G.Adj z w := by simpa using hm.1
      have hwy : w ∉ ball G y := fun hw => hno z (third_subset_ball x hzx) w hw hzw
      exact Finset.mem_filter.mpr
        ⟨by simp [T, hm.2, hwy], hzw⟩
    have hysub (hzy : z ∈ third G y) :
        G.neighborFinset z \ ball G y ⊆ T.bipartiteAbove G.Adj z := by
      intro w hw
      have hm := Finset.mem_sdiff.mp hw
      have hzw : G.Adj z w := by simpa using hm.1
      have hwx : w ∉ ball G x := fun hw => hno w hw z (third_subset_ball y hzy) hzw.symm
      exact Finset.mem_filter.mpr
        ⟨by simp [T, hm.2, hwx], hzw⟩
    rcases Finset.mem_union.mp hz with hz | hz
    · simpa [hxout z hz] using Finset.card_le_card (hxsub hz)
    · simpa [hyout z hz] using Finset.card_le_card (hysub hz)
  have hupper : ∀ w ∈ T, (S.bipartiteBelow G.Adj w).card ≤ 3 := by
    intro w _
    calc
      _ ≤ (G.neighborFinset w).card := Finset.card_le_card (by
        intro z hz
        exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hz).2.symm)
      _ = 3 := by rw [G.card_neighborFinset_eq_degree, hd]
  have hcap := Finset.card_mul_le_card_mul G.Adj hlow hupper
  rw [hS, hT] at hcap
  omega

private lemma hamming_le_walk {n : ℕ} {C : Finset (Sensitivity.Q n)}
    {x y : (C : Set (Sensitivity.Q n))}
    (p : ((hypercube n).induce (C : Set (Sensitivity.Q n))).Walk x y) :
    hammingDist x.val y.val ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have he : hammingDist u.val v.val = 1 := huv
    have ht := hammingDist_triangle u.val v.val w.val
    simp only [Walk.length_cons]
    omega

/-- Every pair in an actual Huang-balanced cubic 54-vertex support in Q9
differs in at most seven coordinates. No connectivity or girth is assumed. -/
theorem hamming_distance_le_seven {C : Finset (Sensitivity.Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Sensitivity.Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcard : C.card = 54) :
    ∀ x ∈ C, ∀ y ∈ C,
      (Finset.univ.filter (fun i : Fin 9 => x i ≠ y i)).card ≤ 7 := by
  let G := (hypercube 9).induce (C : Set (Sensitivity.Q 9))
  let L : Finset (C : Set (Sensitivity.Q 9)) :=
    Finset.univ.filter fun z => cubeParity z.val = false
  let R : Finset (C : Set (Sensitivity.Q 9)) :=
    Finset.univ.filter fun z => cubeParity z.val = true
  have hpart : G.IsBipartiteWith (L : Set _) (R : Set _) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro z hz hz'
      have h0 : cubeParity z.val = false := (Finset.mem_filter.mp hz).2
      have h1 : cubeParity z.val = true := (Finset.mem_filter.mp hz').2
      exact Bool.false_ne_true (h0.symm.trans h1)
    · intro u v huv
      have hne := cubeParity_ne_of_adj huv
      cases hu : cubeParity u.val <;> cases hv : cubeParity v.val <;>
        simp_all [L, R]
  have hn : Fintype.card (C : Set (Sensitivity.Q 9)) = 54 := by
    simpa using hcard
  intro x hx y hy
  obtain ⟨p, hp⟩ := short_walk hpart (BalancedCubeGirth.eight_le_egirth C hb)
    hr.degree_eq hn ⟨x, hx⟩ ⟨y, hy⟩
  exact (hamming_le_walk p).trans hp

end D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
