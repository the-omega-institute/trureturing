/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterProbe.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterProbe.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterProbe.claim
   digest: Exclude Hamming distances eight and nine among the vertices of a 66-vertex Huang-balanced induced cubic support in the nine-cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixResidualCountingProbe

/-! Exclude distance eight from a 66-vertex balanced cubic support. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open SimpleGraph Finset
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
attribute [local instance] Classical.propDecidable

open private incidences incidences_symm incidences_add from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private HammingSeven.ball from D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private sixty_six_distance_eight_residual from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixResidualProbe
open private paritySide from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private residual_opposite_half_has_no_isolated from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixResidualHalfProbe
open private crossing_neighbor from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixResidualMatchingProbe
open private cross_from_residual_bound cube_cut_incidences ball_half_internal_and_crossing_eq
  incidence_eq_neighbor_inter sum_incidence_eq_const_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixResidualCountingProbe
open private sixty_six_half_card_ge_twenty_one from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixShellProbe

set_option maxHeartbeats 1200000 in
-- Repeated comparison of incidence sums on induced-graph subtypes needs normalization.
private lemma sixty_six_no_distance_eight {C : Finset (Q 9)} (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (x y : (C : Set (Q 9))) (hxy : hammingDist x.val y.val = 8) : False := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let B := HammingSeven.ball G x ∪ HammingSeven.ball G y
  let R := univ \ B
  let K := (univ : Finset (Fin 9)).filter (fun i => x.val i = y.val i)
  have hK : K.card = 1 := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin 9)))
      (fun i => x.val i ≠ y.val i)
    simp only [card_univ,Fintype.card_fin,not_not] at h
    change hammingDist x.val y.val + K.card = 9 at h
    omega
  obtain ⟨k,hkK⟩ := card_pos.mp (by omega : 0 < K.card)
  have hk := (mem_filter.mp hkK).2
  let H := univ.filter (fun w : (C : Set (Q 9)) => w.val k ≠ x.val k)
  let W := R \ H
  let P := R ∩ paritySide C (cubeParity x.val)
  let T := R ∩ paritySide C (!cubeParity x.val)
  let I := P ∩ H
  let J := T ∩ H
  let Pout := P \ H
  let Tout := T \ H
  let S := H ∩ B
  let U := H \ B
  have hsH : H.card = S.card + U.card := by
    have h := card_sdiff_add_card_inter H B
    change U.card + S.card = H.card at h
    omega
  have hH : 21 ≤ H.card := by
    have he : H.card = (C.filter (fun w => w k = !x.val k)).card := by
      apply card_bij (fun w _ => w.val)
      · intro w hw
        have hh := (mem_filter.mp hw).2
        exact mem_filter.mpr ⟨w.property,Bool.eq_not_of_ne hh⟩
      · intro w _ v _ h
        exact Subtype.ext h
      · intro w hw
        obtain ⟨hwC,hwk⟩ := mem_filter.mp hw
        exact ⟨⟨w,hwC⟩,mem_filter.mpr ⟨mem_univ _,by simp [hwk]⟩,rfl⟩
    rw [he]
    exact sixty_six_half_card_ge_twenty_one hc hr hb k (!x.val k)
  obtain ⟨_,hT,hTN⟩ := sixty_six_distance_eight_residual hc hr hb x y hxy
  change T.card = 3 at hT
  change ∀ w ∈ T, G.neighborFinset w ⊆ P at hTN
  have hIU : U = I ∪ J := by
    ext w
    simp only [I,J,U,P,T,H,R,paritySide,mem_union,mem_inter,mem_sdiff,mem_filter,mem_univ,true_and]
    cases cubeParity x.val <;> cases cubeParity w.val <;> simp <;> tauto
  have hIJ : Disjoint I J := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    have hp := (mem_filter.mp (mem_inter.mp (mem_inter.mp hw).1).2).2
    have ht := (mem_filter.mp (mem_inter.mp (mem_inter.mp hw').1).2).2
    have hh := hp.symm.trans ht
    cases h : cubeParity x.val <;> simp [h] at hh
  have hU : U.card = I.card + J.card := by rw [hIU,card_union_of_disjoint hIJ]
  have hI : I ∪ Pout = P := by ext w; simp [I,Pout]; tauto
  have hJ : J ∪ Tout = T := by ext w; simp [J,Tout]; tauto
  have hIdis : Disjoint I Pout := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact (mem_sdiff.mp hw').2 (mem_inter.mp hw).2
  have hJdis : Disjoint J Tout := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact (mem_sdiff.mp hw').2 (mem_inter.mp hw).2
  have hJsum : J.card + Tout.card = 3 := by
    rw [← card_union_of_disjoint hJdis,hJ,hT]
  have hTtotal : incidences G P T = 9 := by
    rw [incidences_symm]
    have h := sum_incidence_eq_const_degree G T P 3 (fun w hw => by
      change (G.neighborFinset w ∩ P).card = 3
      rw [inter_eq_left.mpr (hTN w hw),G.card_neighborFinset_eq_degree]
      exact hr.degree_eq w)
    rw [hT] at h
    exact h
  have hIT : incidences G I T = incidences G I J + incidences G I Tout := by
    rw [← hJ,incidences_add G I J Tout hJdis]
  have htotal : incidences G I J + incidences G I Tout +
      incidences G Pout J + incidences G Pout Tout = 9 := by
    have h := hTtotal
    rw [← hI, incidences_symm G (I ∪ Pout) T, incidences_add G T I Pout hIdis,
      incidences_symm G T I, incidences_symm G T Pout, hIT,
      ← hJ, incidences_add G Pout J Tout hJdis] at h
    omega
  have internal_zero (D : Finset (C : Set (Q 9))) (b : Bool)
      (hp : ∀ w ∈ D, cubeParity w.val = b) : incidences G D D = 0 := by
    rw [← Nat.zero_mul D.card]
    apply sum_incidence_eq_const_degree
    intro z hz
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hwN,hwD⟩ := mem_inter.mp hw
    have hadj := (G.mem_neighborFinset z w).mp hwN
    exact cubeParity_ne_of_adj hadj ((hp z hz).trans (hp w hwD).symm)
  have hII : incidences G I I = 0 := internal_zero I _ (fun w hw =>
    (mem_filter.mp (mem_inter.mp (mem_inter.mp hw).1).2).2)
  have hJJ : incidences G J J = 0 := internal_zero J _ (fun w hw =>
    (mem_filter.mp (mem_inter.mp (mem_inter.mp hw).1).2).2)
  have hIn : incidences G U U = 2 * incidences G I J := by
    rw [hIU,incidences_add G (I ∪ J) I J hIJ,incidences_symm G (I ∪ J) I,
      incidences_symm G (I ∪ J) J,incidences_add G I I J hIJ,incidences_add G J I J hIJ,
      hII,hJJ,incidences_symm G J I]
    omega
  have hcross : incidences G I Tout ≤ Tout.card := by
    rw [incidences_symm,incidence_eq_neighbor_inter]
    calc
      _ ≤ ∑ _w ∈ Tout, 1 := by
        apply sum_le_sum
        intro w hw
        apply card_le_one.mpr
        intro u hu v hv
        have hwbit : w.val k = x.val k := by simpa [H] using (mem_sdiff.mp hw).2
        have hn {z : (C : Set (Q 9))} (hz : z ∈ G.neighborFinset w ∩ I) :
            z.val = BalancedCriticalSpectrum.flip w.val k := by
          have hbit := (mem_filter.mp (mem_inter.mp (mem_inter.mp hz).2).2).2
          exact crossing_neighbor ((G.mem_neighborFinset w z).mp (mem_inter.mp hz).1)
            (fun h => hbit (h.trans hwbit))
        exact Subtype.ext ((hn hu).trans (hn hv).symm)
      _ = _ := by simp
  have hIdeg : I.card ≤ incidences G I T := by
    rw [incidence_eq_neighbor_inter,card_eq_sum_ones]
    apply sum_le_sum
    intro w hw
    have hwP := (mem_inter.mp hw).1
    have hwR := (mem_inter.mp hwP).1
    have hwH := (mem_filter.mp (mem_inter.mp hw).2).2
    have hh := residual_opposite_half_has_no_isolated hc hr hb x y hxy k hk w hwR hwH
    change 0 < (G.neighborFinset w ∩ R).card at hh
    have heq : G.neighborFinset w ∩ R = G.neighborFinset w ∩ T := by
      ext v
      constructor
      · intro hv
        obtain ⟨hvN,hvR⟩ := mem_inter.mp hv
        have hp := (mem_filter.mp (mem_inter.mp hwP).2).2
        have hne := cubeParity_ne_of_adj ((G.mem_neighborFinset w v).mp hvN)
        have hvp : cubeParity v.val ≠ cubeParity x.val := fun h => hne (hp.trans h.symm)
        exact mem_inter.mpr ⟨hvN,mem_inter.mpr
          ⟨hvR,mem_filter.mpr ⟨mem_univ _,Bool.eq_not_of_ne hvp⟩⟩⟩
      · intro hv
        exact mem_inter.mpr ⟨(mem_inter.mp hv).1,(mem_inter.mp (mem_inter.mp hv).2).1⟩
    rw [heq] at hh
    exact hh
  have hdeg : incidences G H univ = 3 * H.card :=
    sum_incidence_eq_const_degree G H univ 3 (fun w _ => by
      rw [inter_univ,G.card_neighborFinset_eq_degree]
      exact hr.degree_eq w)
  have hdir := direction_edge_count (d := 3) C hr hb k
  rw [hc] at hdir
  have hcut := cube_cut_incidences (C := C) k (x.val k)
  change incidences G H (univ \ H) = directionEdges C k at hcut
  have hHsplit : H ∪ (univ \ H) = univ := by ext w; simp
  have hHdis : Disjoint H (univ \ H) := disjoint_sdiff
  have hhalf : incidences G H H + 11 = 3 * H.card := by
    rw [← hHsplit,incidences_add G H H (univ \ H) hHdis,hcut] at hdeg
    omega
  have hbnd := ball_half_internal_and_crossing_eq hr hb x y hxy k hk
  change incidences G H H + 2 * incidences G S W = 4 * S.card + incidences G U U at hbnd
  have hcharge := cross_from_residual_bound hc hr hb x y hxy k hk
  change incidences G S W + I.card ≤ incidences G Pout Tout + incidences G I T at hcharge
  rw [hIT] at hcharge hIdeg
  rw [hIn] at hbnd
  omega

#print axioms sixty_six_no_distance_eight

open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff diff_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

/-- A 66-vertex Huang-balanced induced cubic support in the nine-cube has diameter at most seven. -/
theorem huang_balanced_cubic_sixty_six_diameter_le_seven {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7 := by
  intro x hx y hy
  have hEight : hammingDist x y ≠ 8 := sixty_six_no_distance_eight hc hr hb ⟨x,hx⟩ ⟨y,hy⟩
  have hNine : hammingDist x y ≠ 9 := by
    intro h9
    let G := (hypercube 9).induce (C : Set (Q 9))
    let r : (C : Set (Q 9)) := ⟨x,hx⟩
    have hN : (G.neighborFinset r).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]
      exact hr.degree_eq r
    obtain ⟨u,hu⟩ := card_pos.mp (by omega : 0 < (G.neighborFinset r).card)
    have hadj : (hypercube 9).Adj x u.val := (G.mem_neighborFinset r u).mp hu
    obtain ⟨k,hk⟩ := adjacent_exists_flip hadj
    have hf : diff x y = univ := by
      apply eq_of_subset_of_card_le (subset_univ _)
      rw [card_univ,Fintype.card_fin]
      exact h9.ge
    have hku : k ∈ diff x y := by rw [hf]; exact mem_univ _
    have h8 : hammingDist u.val y = 8 := by
      change (diff u.val y).card = 8
      rw [hk,diff_flip,ite_eq_left hku,card_erase_of_mem hku]
      change hammingDist x y - 1 = 8
      omega
    exact sixty_six_no_distance_eight hc hr hb u ⟨y,hy⟩ h8
  have hmax : hammingDist x y ≤ 9 := hammingDist_le_card_fintype
  omega

#print axioms huang_balanced_cubic_sixty_six_diameter_le_seven

namespace Q9SixtySixDiameterProbe

/-- A counterexample to the Hamming diameter bound at order 66. -/
def claim : Prop :=
  ∃ C : Finset (Q 9), C.card = 66 ∧
    ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧ IsBalanced C ∧
    ∃ x ∈ C, ∃ y ∈ C, 7 < hammingDist x y

/-- Distance greater than seven is impossible in the 66-point case. -/
theorem result : ¬ claim := by
  rintro ⟨C, hc, hr, hb, x, hx, y, hy, hxy⟩
  exact not_lt_of_ge (huang_balanced_cubic_sixty_six_diameter_le_seven hc hr hb x hx y hy) hxy

#print axioms result

end Q9SixtySixDiameterProbe

end D5.S3.Combinatorics.Graph.HypercubeCritical
