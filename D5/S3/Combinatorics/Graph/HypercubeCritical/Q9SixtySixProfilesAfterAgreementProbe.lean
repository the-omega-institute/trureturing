import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixForcedEdgesProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySix114555555Probe

/-! The profile list after the first agreement-capacity certificate. -/

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

open BalancedCriticalSpectrum (Q IsBalanced)

set_option autoImplicit false

def sixtySixProfilesAfterAgreement : List (List ℤ) :=
  sixtySixProfilesAfterForcedEdges.filter (· != [1, 1, 4, 5, 5, 5, 5, 5, 5])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
-- Kernel reduction traverses the preceding profile filters as well as the final deletion.
theorem sixtySixProfilesAfterAgreement_length :
    sixtySixProfilesAfterAgreement.length = 38 := by
  decide +kernel

open Classical in
theorem q9_sixty_six_mem_profiles_after_agreement
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterAgreement := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hp⟩ := q9_sixty_six_mem_profiles_after_forced_edges hC hreg hb
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  rw [sixtySixProfilesAfterAgreement, List.mem_filter]
  refine ⟨hp, bne_iff_ne.mpr ?_⟩
  intro he
  have hv :
      List.ofFn (![1, 1, 4, 5, 5, 5, 5, 5, 5] : Fin 9 → ℤ) =
      [1, 1, 4, 5, 5, 5, 5, 5, 5] := by decide +kernel
  have hr := List.ofFn_inj.mp (he.trans hv.symm)
  subst r
  exact q9_sixty_six_excludes_114555555 hS hregS hbS hhalf

#print axioms q9_sixty_six_mem_profiles_after_agreement

end D5.S3.Combinatorics.Graph.HypercubeCritical
