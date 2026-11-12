/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTail
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportEndpointTwoTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full real endpoint-two tail and its actual ideal-graph application. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointTwoTailSigns
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! The original real a≥40 endpoint-two theorem, with both rectangle bounds.
The separate sharp-alpha equality case and the integer finite base are not
claimed as consequences of this tail theorem. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointTwoTail

open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra
open D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointTwoTailSigns
open D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions

/-- Both original rectangle bounds on the complete real a≥8 zero surface. -/
theorem rectangle (a b c : ℝ) (ha : 8 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hz : h a b c 2 = 0) : b < 2*a-2 ∧ c < 9*a/4-8 := by
  have hb : b < 2*a-2 := by
    by_contra hn
    have hu : 0 ≤ b-(2*a-2) := by linarith
    have hv : 0 ≤ c-b := by linarith
    have hm : 0 ≤ a-8 := by linarith
    have hs : h a b c 2 = h (8+(a-8)) (14+2*(a-8)+(b-(2*a-2)))
        (14+2*(a-8)+(b-(2*a-2))+(c-b)) 2 := by congr 1 <;> ring
    have hp := first_positive (a-8) (b-(2*a-2)) (c-b) hm hu hv
    rw [← hs, hz] at hp
    linarith
  refine ⟨hb, ?_⟩
  by_contra hn
  let t := (b-a)/(2*a-2-b)
  have hden : 0 < 2*a-2-b := by linarith
  have ht : 0 ≤ t := div_nonneg (by linarith) hden.le
  have ht1 : 1+t ≠ 0 := by positivity
  have hrel : t*(2*a-2-b) = b-a := by dsimp [t]; exact div_mul_cancel₀ _ hden.ne'
  have hbrepr : (a+(2*a-2)*t)/(1+t) = b := by
    apply (div_eq_iff ht1).mpr
    nlinarith only [hrel]
  have hm : 0 ≤ a-8 := by linarith
  have hv : 0 ≤ c-(9*a/4-8) := by linarith
  have h1 : 8+(a-8) = a := by ring
  have h2 : 9*a/4-8+(c-(9*a/4-8)) = c := by ring
  have hp := second_positive (a-8) t (c-(9*a/4-8)) hm ht hv
  rw [h1,hbrepr,h2,hz] at hp
  linarith

/-- The original strict endpoint signs for every ordered real minimum≥40. -/
theorem endpoint_signs (a b c : ℝ) (ha : 40 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hz : h a b c 2 = 0) : 0 < h a b c 4 ∧ h a b c 5 < 0 := by
  obtain ⟨hb, hc⟩ := rectangle a b c (by linarith) hab hbc hz
  have h5diff : 0 < 4*h a b c 2-h a b c 5 := by
    have hm : 0 ≤ a-8 := by linarith
    have ht : 0 ≤ b-8 := by linarith
    have hu : 0 ≤ c-8 := by linarith
    have h1 : 8+(a-8) = a := by ring
    have h2 : 8+(b-8) = b := by ring
    have h3 : 8+(c-8) = c := by ring
    simpa only [h1,h2,h3] using fifth_difference_positive (a-8) (b-8) (c-8) hm ht hu
  let t := (b-a)/(2*a-b)
  let u := 4*(c-a)/(9*a-4*c)
  have hdenT : 0 < 2*a-b := by linarith
  have hdenU : 0 < 9*a-4*c := by linarith
  have ht : 0 ≤ t := div_nonneg (by linarith) hdenT.le
  have hu : 0 ≤ u := div_nonneg (by nlinarith) hdenU.le
  have ht1 : 1+t ≠ 0 := by positivity
  have hu1 : 4*(1+u) ≠ 0 := by positivity
  have hrelT : t*(2*a-b) = b-a := by dsimp [t]; exact div_mul_cancel₀ _ hdenT.ne'
  have hrelU : u*(9*a-4*c) = 4*(c-a) := by dsimp [u]; exact div_mul_cancel₀ _ hdenU.ne'
  have hbrepr : a*(1+2*t)/(1+t) = b := by
    apply (div_eq_iff ht1).mpr
    nlinarith only [hrelT]
  have hcrepr : a*(4+9*u)/(4*(1+u)) = c := by
    apply (div_eq_iff hu1).mpr
    nlinarith only [hrelU]
  have hm : 0 ≤ a-40 := by linarith
  have h1 : 40+(a-40) = a := by ring
  have h4diff := fourth_difference_positive (a-40) t u hm ht hu
  rw [h1,hbrepr,hcrepr,hz] at h4diff
  rw [hz] at h5diff
  constructor <;> linarith

/-- The full real endpoint-two tail has a noninteger quotient root in (4,5). -/
theorem result (a b c : ℝ) (ha : 40 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hz : h a b c 2 = 0) : ∃ e : ℝ, 4 < e ∧ e < 5 ∧ h a b c e = 0 := by
  obtain ⟨h4,h5⟩ := endpoint_signs a b c ha hab hbc hz
  obtain ⟨e, he, heq⟩ := intermediate_value_Icc' (show (4 : ℝ) ≤ 5 by norm_num)
    (show ContinuousOn (fun x : ℝ => h a b c x) (Set.Icc 4 5) by unfold h; fun_prop)
    (show (0 : ℝ) ∈ Set.Icc (h a b c 5) (h a b c 4) from ⟨h5.le,h4.le⟩)
  refine ⟨e, ?_, ?_, heq⟩
  · have hn : (4 : ℝ) ≠ e := by intro hn; rw [← hn] at heq; linarith
    exact lt_of_le_of_ne he.1 hn
  · have hn : e ≠ (5 : ℝ) := by intro hn; rw [hn] at heq; linarith
    exact lt_of_le_of_ne he.2 hn

/-- Every integer triple in the complete tail acts on actual ideals. -/
theorem actual_nonintegral (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 40 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hz : h (a : ℝ) (b : ℝ) (c : ℝ) 2 = 0) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  obtain ⟨e, he4, he5, heq⟩ := result a b c (by exact_mod_cast ha)
    (by exact_mod_cast hab) (by exact_mod_cast hbc) hz
  have he0 : e ≠ 0 := by linarith
  exact nonintegral_of_unit_root p hp hinj a b c (by omega) (by omega) (by omega)
    e he0 heq 4 (by simpa using he4) (by norm_num; exact he5)

#print axioms rectangle
#print axioms endpoint_signs
#print axioms result
#print axioms actual_nonintegral

end D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointTwoTail
