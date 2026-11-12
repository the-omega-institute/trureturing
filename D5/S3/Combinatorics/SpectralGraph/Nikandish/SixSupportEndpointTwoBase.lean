/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoBase
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportEndpointTwoBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoBase.endpoint_one_for_actual_integral; instance=D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoBase.result
   digest: Complete8658 endpoint-two base with exact minimum absolute endpoint8208. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportClassificationAlgebra
import Mathlib.Tactic

/-! Exact original8≤a≤39, a<b<2a-2, b<c≤floor((9a-33)/4).
The new checks are kernel integer Horner checks. The original independent
Bareiss and per-row reproduction reports retain their separate provenance. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointTwoBase

open SixSupportClassificationAlgebra
open SixSupportIdealIntersectionLift (exponents)
open IdealIntersectionSupport IdealIntersectionObstructions

/-- The exact original finite integer parameter set, without omitted positions. -/
def domain : List (ℕ × ℕ × ℕ) :=
  ((List.range 40).filter fun a => 8 ≤ a).flatMap fun a =>
    ((List.range (2*a-2)).filter fun b => a < b).flatMap fun b =>
      ((List.range ((9*a-33)/4+1)).filter fun c => b < c).map fun c => (a,b,c)

/-- Canonical membership is the complete original domain. -/
theorem mem_domain (a b c : ℕ) : (a,b,c) ∈ domain ↔
    8 ≤ a ∧ a < 40 ∧ a < b ∧ b < 2*a-2 ∧ b < c ∧ c ≤ (9*a-33)/4 := by
  simp [domain, List.mem_flatMap, List.mem_map, and_assoc, and_left_comm, and_comm,
    Nat.lt_succ_iff]

/-- Exact endpoint bounds on every original triple, checked in the Lean kernel. -/
theorem result : domain.all (fun t =>
    decide (8208 ≤ (value (t.1 : ℤ) (t.2.1 : ℤ) (t.2.2 : ℤ) 2).natAbs)) = true := by
  decide +kernel

/-- The complete original number of parameter positions. -/
theorem domain_card : domain.length = 8658 := by decide +kernel

/-- The attained lower absolute value, at its actual original parameter triple. -/
theorem attained_minimum : (14,19,21) ∈ domain ∧ value (14 : ℤ) 19 21 2 = 8208 := by
  decide +kernel

/-- Every original finite endpoint-two value is nonzero over the real parameters. -/
theorem endpoint_two_nonzero (a b c : ℕ) (ha : 8 ≤ a) (ha40 : a < 40)
    (hab : a < b) (hb : b < 2*a-2) (hbc : b < c) (hc : c ≤ (9*a-33)/4) :
    h (a : ℝ) (b : ℝ) (c : ℝ) 2 ≠ 0 := by
  have hm := (mem_domain a b c).mpr ⟨ha,ha40,hab,hb,hbc,hc⟩
  have hv : 8208 ≤ (value (a : ℤ) (b : ℤ) (c : ℤ) 2).natAbs :=
    of_decide_eq_true (List.all_eq_true.mp result (a,b,c) hm)
  intro hz
  have hz' : value (a : ℤ) (b : ℤ) (c : ℤ) 2 = 0 := by
    rw [h_eq_value] at hz
    dsimp [value] at hz ⊢
    exact_mod_cast hz
  rw [hz'] at hv
  norm_num at hv

/-- Actual ideal graphs consume the complete base through the exact low-root
reduction, retaining endpoint one as a separate remaining alternative. -/
theorem endpoint_one_for_actual_integral (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 8 ≤ a) (ha40 : a < 40)
    (hab : a < b) (hb : b < 2*a-2) (hbc : b < c) (hc : c ≤ (9*a-33)/4)
    (hint : ActualLaplacianIntegral (modulus p (exponents a b c))) :
    h (a : ℝ) (b : ℝ) (c : ℝ) 1 = 0 := by
  exact (endpoint_one_or_two p hp hinj a b c (by omega) hab.le hbc.le hint).resolve_right
    (endpoint_two_nonzero a b c ha ha40 hab hb hbc hc)

#print axioms result
#print axioms domain_card
#print axioms attained_minimum
#print axioms endpoint_one_for_actual_integral

end D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointTwoBase
