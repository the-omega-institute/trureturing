import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyExclusionProbe

/-! Bounds on the sixth distance layer of a balanced 66-vertex cubic support. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
attribute [local instance] Classical.propDecidable

open private paritySide parity_union parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private distance_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private balanced_cubic_hamming_two_four from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9FourthLeafSignProbe
open private distance_six_shell_partner_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyExclusionProbe
open private distanceSevenPartners distanceSeven_partner_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe

private lemma sixty_six_distance_six_bound {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    {x : Q 9} (hx : x ∈ C) : (shell C x 6).card ≤ 14 := by
  have hcardC : Fintype.card (C : Set (Q 9)) = 66 := by simpa using hc
  have hparity (b : Bool) : (paritySide C b).card = 33 := by
    have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq (parity_bipartite C)
    simp only [hr.degree_eq, Finset.sum_const, smul_eq_mul] at hs
    have hu := congrArg Finset.card (parity_union C)
    rw [Finset.card_union_of_disjoint (by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact Bool.false_ne_true ((Finset.mem_filter.mp hz).2.symm.trans
        (Finset.mem_filter.mp hz').2)), Finset.card_univ, hcardC] at hu
    cases b <;> omega
  let n (k : ℕ) := (Finset.univ.filter
    (fun y : (C : Set (Q 9)) => hammingDist x y.val = k)).card
  let w (k : ℕ) : ℕ := if k % 2 = 0 then 1 else 0
  have hsum : (∑ k ∈ Finset.range 8, n k * w k) =
      ∑ y : (C : Set (Q 9)), w (hammingDist x y.val) := by
    simpa only [n, Finset.sum_const, smul_eq_mul] using
      Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.range 8)
        (g := fun y : (C : Set (Q 9)) => hammingDist x y.val)
        (fun y _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hd x hx y.val y.property))) w
  have heven : (∑ y : (C : Set (Q 9)), w (hammingDist x y.val)) = 33 := by
    dsimp only [w]
    rw [← Finset.card_filter]
    have heq : (Finset.univ.filter (fun y : (C : Set (Q 9)) =>
        hammingDist x y.val % 2 = 0)) = paritySide C (cubeParity x) := by
      ext y
      simp only [paritySide, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (distance_parity x y.val).trans eq_comm
    rw [heq, hparity]
  have he := hsum.trans heven
  simp only [w, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMod, ite_true,
    Nat.mul_one, Nat.zero_add] at he
  have hzero : 1 ≤ n 0 := Finset.card_pos.mpr
    ⟨⟨x,hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hammingDist_self x⟩⟩
  have h24 : 18 ≤ n 2 + n 4 := balanced_cubic_hamming_two_four hr hb ⟨x,hx⟩
  have h6 : n 6 ≤ 14 := by omega
  have hcard : (shell C x 6).card = n 6 := by
    apply Finset.card_bij
      (fun y hy => (⟨y, (Finset.mem_filter.mp hy).1⟩ : (C : Set (Q 9))))
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
    · intro y _ z _ heq
      exact congrArg Subtype.val heq
    · intro y hy
      exact ⟨y.val, Finset.mem_filter.mpr ⟨y.property, (Finset.mem_filter.mp hy).2⟩, rfl⟩
  exact hcard.le.trans h6

open private unusedDirections from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe

private lemma sixty_six_partner_capacity {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    {x : Q 9} (hx : x ∈ C) :
    (shell C x 7).card +
        ((Finset.univ : Finset (unusedDirections C x)).filter
          (fun v => (distanceSevenPartners C x).degree v = 2)).card +
        ((distanceSevenPartners C x).cliqueFinset 3).card ≤ 14 := by
  have h6 := sixty_six_distance_six_bound hc hr hb hd hx
  obtain ⟨sigma, hs⟩ := hb
  have hbound := distance_six_shell_partner_bound hs hr hd hx
  have hcard : (distanceSevenPartners C x).edgeFinset.card = (shell C x 7).card :=
    distanceSeven_partner_card hd x
  rw [← hcard]
  exact hbound.trans h6

#print axioms sixty_six_partner_capacity
