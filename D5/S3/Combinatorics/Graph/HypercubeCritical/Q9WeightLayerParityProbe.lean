import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9UniformFourDeficitsProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.WeightLayerParity

/-! The normalized profiles surviving the weight-layer parity obstruction. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced)

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

open private sum_ofFn_int from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe

/-- The residual profiles with even total deficit. -/
def sixtySixProfilesAfterWeightParity : List (List ℤ) :=
  sixtySixProfilesAfterUniformFour.filter (fun p => decide (p.sum % 2 = 0))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- The kernel enumerates the residual profiles of even total deficit.
theorem sixtySixProfilesAfterWeightParity_length :
    sixtySixProfilesAfterWeightParity.length = 44 := by
  decide +kernel

/-- A hypothetical 66-point Huang-balanced cubic support has one of 44
normalized profiles after the weight-layer parity exclusions. -/
theorem q9_sixty_six_mem_profiles_after_weight_parity {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterWeightParity := by
  obtain ⟨S, r, hs, hreg, hbal, hhalf, hprofile⟩ :=
    q9_sixty_six_mem_profiles_after_uniform_four hc hr hb
  refine ⟨S, r, hs, hreg, hbal, hhalf, ?_⟩
  rw [sixtySixProfilesAfterWeightParity, List.mem_filter, decide_eq_true_eq]
  refine ⟨hprofile, ?_⟩
  rw [sum_ofFn_int]
  exact balanced_sixty_six_even_total_deficit hs hreg hbal r hhalf

#print axioms q9_sixty_six_mem_profiles_after_weight_parity

end D5.S3.Combinatorics.Graph.HypercubeCritical
