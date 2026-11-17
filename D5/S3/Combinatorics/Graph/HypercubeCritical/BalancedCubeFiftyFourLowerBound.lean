/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound.claim
   digest: Nonempty balanced cubic induced subgraphs of the actual nine-cube have at least 54 vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSliceExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyFourExclusion
import Batteries.Tactic.OpenPrivate

/-! The smaller actual coordinate slice has only four possible parameter tuples.
The signing and induced cube adjacency are retained without reidentification. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFiftyFourLowerBound

open SimpleGraph GirthSliceCounting
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeLowerBound (coordinateSlice)
open private coordinate_slice_smaller coordinate_slice_degree_cases
  low_slice_card_eq_q coordinate_slice_low_independent balanced_subset
  paritySide parity_union parity_bipartite parts_card sum_degrees_parts
  twice_low_le_three_high from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound

attribute [local instance] Classical.propDecidable

private theorem numerical_parameters (a b p r h k N : ℕ)
    (ha : p + h = a) (hb : r + k = b) (hN : a + b = N)
    (hq : p + r = 8) (hd : 2 * p + 3 * h = 2 * r + 3 * k)
    (hsmall : N ≤ 24) (hlow : 5 * 8 ≤ 3 * N)
    (hc : 15 * h ≤ h * b + 2 * k + 4 * r)
    (hc' : 15 * k ≤ k * a + 2 * h + 4 * p) :
    (a = 11 ∧ b = 11 ∧ p = 4 ∧ r = 4) ∨
    (a = 13 ∧ b = 11 ∧ p = 7 ∧ r = 1) ∨
    (a = 11 ∧ b = 13 ∧ p = 1 ∧ r = 7) ∨
    (a = 12 ∧ b = 12 ∧ p = 4 ∧ r = 4) := by
  have hp : p = 1 ∨ p = 4 ∨ p = 7 := by
    have hp8 : p ≤ 8 := by omega
    interval_cases p <;> omega
  rcases hp with rfl | rfl | rfl
  · have hab : b = a + 2 := by omega
    simp only [hab] at hb hN hc hc'
    have ha6 : 6 ≤ a := by omega
    have ha11 : a ≤ 11 := by omega
    have hae : a = 11 := by interval_cases a <;> omega
    exact Or.inr (Or.inr (Or.inl ⟨hae, by omega, rfl, by omega⟩))
  · have hab : b = a := by omega
    simp only [hab] at hb hN hc hc'
    have ha7 : 7 ≤ a := by omega
    have ha12 : a ≤ 12 := by omega
    have hae : a = 11 ∨ a = 12 := by interval_cases a <;> omega
    rcases hae with hae | hae
    · exact Or.inl ⟨hae, by omega, rfl, by omega⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hae, by omega, rfl, by omega⟩))
  · have hab : a = b + 2 := by omega
    simp only [hab] at ha hN hc hc'
    have hb6 : 6 ≤ b := by omega
    have hb11 : b ≤ 11 := by omega
    have hbe : b = 11 := by interval_cases b <;> omega
    exact Or.inr (Or.inl ⟨by omega, hbe, rfl, by omega⟩)

private theorem slice_parameters
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hcover : L ∪ R = Finset.univ)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hq : (degreeTwo G Finset.univ).card = 8)
    (hsmall : Fintype.card V ≤ 24) :
    (L.card = 11 ∧ R.card = 11 ∧
      (degreeTwo G L).card = 4 ∧ (degreeTwo G R).card = 4) ∨
    (L.card = 13 ∧ R.card = 11 ∧
      (degreeTwo G L).card = 7 ∧ (degreeTwo G R).card = 1) ∨
    (L.card = 11 ∧ R.card = 13 ∧
      (degreeTwo G L).card = 1 ∧ (degreeTwo G R).card = 7) ∨
    (L.card = 12 ∧ R.card = 12 ∧
      (degreeTwo G L).card = 4 ∧ (degreeTwo G R).card = 4) := by
  have hdisj : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Set.disjoint_left.mp hpart.disjoint hv hw
  have hN : L.card + R.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ]
  have hpq : (degreeTwo G L).card + (degreeTwo G R).card = 8 := by
    have hd : Disjoint (degreeTwo G L) (degreeTwo G R) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hv).1
        (Finset.mem_filter.mp hw).1
    rw [← Finset.card_union_of_disjoint hd]
    simpa only [degreeTwo, ← Finset.filter_union, hcover] using hq
  have hd : 2 * (degreeTwo G L).card + 3 * (degreeThree G L).card =
      2 * (degreeTwo G R).card + 3 * (degreeThree G R).card := by
    have he := SimpleGraph.isBipartiteWith_sum_degrees_eq (s := L) (t := R) hpart
    rwa [sum_degrees_parts G hdeg L, sum_degrees_parts G hdeg R] at he
  have hlowN : 5 * 8 ≤ 3 * Fintype.card V := by
    have ht := parts_card G hdeg Finset.univ
    have hi := twice_low_le_three_high G hdeg hlow
    rw [hq, Finset.card_univ] at ht
    rw [hq] at hi
    omega
  have hc := cubic_slice_counting hpart hdeg hlow hg
  exact numerical_parameters L.card R.card (degreeTwo G L).card
    (degreeTwo G R).card (degreeThree G L).card (degreeThree G R).card
    (Fintype.card V) (parts_card G hdeg L) (parts_card G hdeg R)
    hN hpq hd hsmall hlowN hc.1 hc.2

private theorem small_actual_slice {C : Finset (Q 9)} (hC : C.Nonempty)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hsmall : C.card < 54) :
    ∃ (S : Finset (Q 9)) (L R : Finset (S : Set (Q 9))),
      let G := (hypercube 9).induce (S : Set (Q 9))
      G.IsBipartiteWith (L : Set (S : Set (Q 9))) (R : Set (S : Set (Q 9))) ∧
      (∀ x, G.degree x = 2 ∨ G.degree x = 3) ∧
      (∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False) ∧
      (8 : ℕ∞) ≤ G.egirth ∧
      ((L.card = 11 ∧ R.card = 11 ∧
          (degreeTwo G L).card = 4 ∧ (degreeTwo G R).card = 4) ∨
       (L.card = 13 ∧ R.card = 11 ∧
          (degreeTwo G L).card = 7 ∧ (degreeTwo G R).card = 1) ∨
       (L.card = 11 ∧ R.card = 13 ∧
          (degreeTwo G L).card = 1 ∧ (degreeTwo G R).card = 7) ∨
       (L.card = 12 ∧ R.card = 12 ∧
          (degreeTwo G L).card = 4 ∧ (degreeTwo G R).card = 4)) := by
  have h48 := BalancedCubeLowerBound.forty_eight_le_card C hC hr hb
  have h6 : 6 * directionEdges C 0 = C.card := by
    simpa using direction_edge_count (d := 3) C hr hb 0
  have hq : directionEdges C 0 = 8 := by omega
  obtain ⟨b, hs⟩ := coordinate_slice_smaller C
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3 := fun v =>
    coordinate_slice_degree_cases v.property hr
  have hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False := by
    intro v w hxy hx hy
    exact coordinate_slice_low_independent hr hb hxy hx hy
  have hbal : IsBalanced S := balanced_subset hb (Finset.filter_subset _ _)
  have hg : (8 : ℕ∞) ≤ G.egirth := BalancedCubeGirth.eight_le_egirth S hbal
  have hqcard : (degreeTwo G Finset.univ).card = 8 :=
    (low_slice_card_eq_q hr).trans hq
  have hNsmall : Fintype.card (S : Set (Q 9)) ≤ 24 := by
    have hScard : Fintype.card (S : Set (Q 9)) = S.card := by simp
    rw [hScard]
    change (coordinateSlice C b).card ≤ 24
    omega
  refine ⟨S, paritySide S false, paritySide S true,
    parity_bipartite S, hdeg, hlow, hg, ?_⟩
  exact slice_parameters (parity_bipartite S) (parity_union S)
    hdeg hlow hg hqcard hNsmall

/-- A nonempty balanced actual cubic induced subgraph of Q9 with fewer than 54 vertices. -/
def claim : Prop :=
  ∃ C : Finset (Q 9), C.Nonempty ∧
    ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
    IsBalanced C ∧ C.card < 54

private theorem finite_slice_of_claim (hc : claim) :
    ∃ (m : ℕ) (G : SimpleGraph (Fin m)) (L R : Finset (Fin m))
      (f : Fin m → Q 9),
      G.IsBipartiteWith (L : Set (Fin m)) (R : Set (Fin m)) ∧
      (∀ x, G.degree x = 2 ∨ G.degree x = 3) ∧
      (∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False) ∧
      (8 : ℕ∞) ≤ G.egirth ∧
      L.card = 12 ∧ R.card = 12 ∧
      (degreeTwo G L).card = 4 ∧ (degreeTwo G R).card = 4 ∧
      Function.Injective f ∧
      (∀ x y, G.Adj x y ↔ (hypercube 9).Adj (f x) (f y)) := by
  classical
  obtain ⟨C, hC, hr, hb, hsmall⟩ := hc
  obtain ⟨S, L, R, hpart, hdeg, hlow, hg, hp⟩ := small_actual_slice hC hr hb hsmall
  rcases hp with hp | hp | hp | hp
  · exact (SymmetricSliceExclusion.result
      ⟨9, S, L, R, hpart, hdeg, hlow, hg, hp⟩).elim
  · exact (AsymmetricSliceExclusion.result
      ⟨9, S, L, R, hpart, hdeg, hlow, hg, hp⟩).elim
  · rcases hp with ⟨hL, hR, hL2, hR2⟩
    exact (AsymmetricSliceExclusion.result
      ⟨9, S, R, L, hpart.symm, hdeg, hlow, hg, hR, hL, hR2, hL2⟩).elim
  · rcases hp with ⟨hL, hR, hL2, hR2⟩
    let V := (S : Set (Q 9))
    let G := (hypercube 9).induce (S : Set (Q 9))
    let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
    let H : SimpleGraph (Fin (Fintype.card V)) := G.comap e
    let Lt := L.map e.symm.toEmbedding
    let Rt := R.map e.symm.toEmbedding
    have hmem (T : Finset V) (i : Fin (Fintype.card V)) :
        i ∈ T.map e.symm.toEmbedding ↔ e i ∈ T := by
      simp only [Finset.mem_map_equiv, Equiv.symm_symm]
    have hd (i : Fin (Fintype.card V)) : H.degree i = G.degree (e i) :=
      ((SimpleGraph.Iso.comap e G).degree_eq i).symm
    have hpart' : H.IsBipartiteWith (Lt : Set (Fin (Fintype.card V)))
        (Rt : Set (Fin (Fintype.card V))) := by
      constructor
      · apply Set.disjoint_left.mpr
        intro i hi hi'
        exact Set.disjoint_left.mp hpart.disjoint ((hmem L i).mp hi)
          ((hmem R i).mp hi')
      · intro i j hij
        rcases hpart.mem_of_adj hij with h | h
        · exact Or.inl ⟨(hmem L i).mpr h.1, (hmem R j).mpr h.2⟩
        · exact Or.inr ⟨(hmem R i).mpr h.1, (hmem L j).mpr h.2⟩
    have hlowcard (T : Finset V) :
        (degreeTwo H (T.map e.symm.toEmbedding)).card = (degreeTwo G T).card := by
      have heq : degreeTwo H (T.map e.symm.toEmbedding) =
          (degreeTwo G T).map e.symm.toEmbedding := by
        ext i
        simp only [degreeTwo, Finset.mem_filter, Finset.mem_map_equiv,
          Equiv.symm_symm]
        constructor
        · rintro ⟨hi, hi2⟩
          exact ⟨hi, (hd i).symm.trans hi2⟩
        · rintro ⟨hi, hi2⟩
          exact ⟨hi, (hd i).trans hi2⟩
      rw [heq, Finset.card_map]
    refine ⟨Fintype.card V, H, Lt, Rt, fun i => (e i).val, hpart', ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, Subtype.val_injective.comp e.injective, ?_⟩
    · intro i
      rcases hdeg (e i) with hi | hi
      · exact Or.inl ((hd i).trans hi)
      · exact Or.inr ((hd i).trans hi)
    · intro i j hij hi hj
      exact hlow hij ((hd i) ▸ hi) ((hd j) ▸ hj)
    · calc
        (8 : ℕ∞) ≤ G.egirth := hg
        _ = H.egirth := (SimpleGraph.Iso.comap e G).egirth_eq.symm
    · simpa only [Lt, Finset.card_map] using hL
    · simpa only [Rt, Finset.card_map] using hR
    · exact (hlowcard L).trans hL2
    · exact (hlowcard R).trans hR2
    · intro i j
      rfl

/-- Every nonempty balanced actual induced cubic subgraph of Q9 has at least 54 vertices. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨m, G, L, R, f, hpart, hdeg, hlow, hg, hL, hR, hL2, hR2, hf, hind⟩ :=
    finite_slice_of_claim hc
  exact SymmetricTwentyFourExclusion.result
    ⟨m, 9, G, L, R, f, hf, hind, hpart, hL, hR, hdeg, hL2, hR2, hlow, hg⟩

#print axioms result

end D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFiftyFourLowerBound
