/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyExclusionProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyExclusionProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyExclusionProbe.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyExclusionProbe.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyExclusionProbe.claim
   digest: Exclude cardinality sixty for a Huang-balanced induced cubic support in the nine-cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyDiameterUpperProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SignedPartnerCapacityProbe

/-! Exclude a 60-vertex Huang-balanced cubic support in the nine-cube. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced IsSwitching)
attribute [local instance] Classical.propDecidable

open private triangleCharge partner_incidence_global_bound wedge_count_plus_degree_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SignedPartnerCapacityProbe
open private distanceSevenPartners unusedDirections unused_card distanceSeven_partner_card
  distanceSeven_partner_degree partnerPhase partnerPhase_nonzero shellWithRoot from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9PartnerGraphProbe
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyShellCompositionProbe
open private no_sixty_with_partner_geometry from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyThinHalfProbe
open private sixty_diameter_le_seven from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyDiameterUpperProbe

private lemma partner_triangle_count_le_charge {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma) (x : Q 9) :
    ((distanceSevenPartners C x).cliqueFinset 3).card ≤
      ∑ T ∈ (Finset.univ : Finset (Fin 9)).powersetCard 3,
        triangleCharge (partnerPhase C sigma x) T := by
  let I := unusedDirections C x
  let G := distanceSevenPartners C x
  let e : I ↪ Fin 9 := ⟨Subtype.val, Subtype.val_injective⟩
  let a := partnerPhase C sigma x
  let U := (Finset.univ : Finset (Fin 9)).powersetCard 3
  let lift : Finset I ↪ Finset (Fin 9) := ⟨Finset.map e, Finset.map_injective e⟩
  let F := (G.cliqueFinset 3).map lift
  have hsub : F ⊆ U := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hT
    refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
    change (S.map e).card = 3
    rw [Finset.card_map]
    exact (SimpleGraph.mem_cliqueFinset_iff.mp hS).2
  have hcharge (T : Finset (Fin 9)) (hT : T ∈ F) : triangleCharge a T = 1 := by
    obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hT
    have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hS
    unfold triangleCharge
    apply if_pos
    intro i hi j hj hij
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hj
    have hadj : G.Adj u v := hclique.1 hu hv (fun h => hij (congrArg e h))
    exact (partnerPhase_nonzero hs x u.val v.val).1.mpr hadj.2
  change (G.cliqueFinset 3).card ≤ ∑ T ∈ U, triangleCharge a T
  calc
    _ = ∑ _T ∈ F, (1 : ℕ) := by simp [F]
    _ = ∑ T ∈ F, triangleCharge a T :=
      Finset.sum_congr rfl (fun T hT => (hcharge T hT).symm)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

private lemma distance_six_shell_partner_bound {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hd : ∀ a ∈ C, ∀ b ∈ C, hammingDist a b ≤ 7)
    {x : Q 9} (hx : x ∈ C) :
    (distanceSevenPartners C x).edgeFinset.card +
        (Finset.univ.filter (fun i => (distanceSevenPartners C x).degree i = 2)).card +
        ((distanceSevenPartners C x).cliqueFinset 3).card ≤ (shell C x 6).card := by
  have hCapacity := partner_incidence_global_bound hs hr hd hx
  have hWedges := wedge_count_plus_degree_two hs hr hd hx
  have hTriangles := partner_triangle_count_le_charge hs x
  have hEdges : (distanceSevenPartners C x).edgeFinset.card = (shellWithRoot C x 7).card :=
    distanceSeven_partner_card hd x
  change _ ≤ (shellWithRoot C x 6).card
  omega

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

/-- A Huang-balanced induced 3-regular subgraph of the nine-cube cannot have order 60. -/
private theorem no_huang_balanced_cubic_sixty (C : Finset (Q 9))
    (hc : C.card = 60)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : False := by
  have hd := sixty_diameter_le_seven hc hr hb
  apply no_sixty_with_partner_geometry C hc hr hb hd
  intro x hx
  let G := distanceSevenPartners C x
  let e : unusedDirections C x ≃ Fin 6 :=
    Fintype.equivOfCardEq (by simpa using unused_card hr hx)
  let H : SimpleGraph (Fin 6) := G.map e
  let iso : G ≃g H := SimpleGraph.Iso.map e G
  have hDegree (v) : H.degree (e v) = G.degree v := iso.degree_eq v
  have hTwo : (Finset.univ.filter (fun v => H.degree v = 2)).card =
      (Finset.univ.filter (fun v => G.degree v = 2)).card := by
    apply Finset.card_bij (fun v _ => e.symm v)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [← hDegree (e.symm v), e.apply_symm_apply]
      exact hv
    · intro _ _ _ _ h
      exact e.symm.injective h
    · intro v hv
      refine ⟨e v, ?_, e.symm_apply_apply v⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hDegree] using hv
  have hClique : (H.cliqueFinset 3).card = (G.cliqueFinset 3).card := by
    change ((G.map e).cliqueFinset 3).card = _
    rw [G.cliqueFinset_map_of_equiv, Finset.card_map]
  refine ⟨H, inferInstance, ?_, ?_, ?_⟩
  · rw [← iso.card_edgeFinset_eq]
    exact distanceSeven_partner_card hd x
  · intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [hDegree]
    exact distanceSeven_partner_degree hr hb hd hx w
  · obtain ⟨sigma, hs⟩ := hb
    rw [← iso.card_edgeFinset_eq, hTwo, hClique]
    exact distance_six_shell_partner_bound hs hr hd hx

namespace Q9SixtyExclusionProbe

/-- The literal sixty-vertex support proposition in the nine-cube. -/
def claim : Prop :=
  ∃ C : Finset (Q 9), C.card = 60 ∧
    ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧ IsBalanced C

/-- The sixty-vertex support proposition is false. -/
theorem result : ¬ claim := by
  rintro ⟨C, hC, hr, hb⟩
  exact no_huang_balanced_cubic_sixty C hC hr hb

#print axioms result

end Q9SixtyExclusionProbe

end D5.S3.Combinatorics.Graph.HypercubeCritical
