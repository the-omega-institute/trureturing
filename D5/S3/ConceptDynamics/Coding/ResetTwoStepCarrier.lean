/- GID: D5/S3/ConceptDynamics/Coding/ResetTwoStepCarrier
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetTwoStepCarrier
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: The origin coefficients of the actual reset square preserve both identity-labelled boundary numbers. -/

import D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetNumberedHistories

open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat)
open Multiplicative
open scoped BigOperators Matrix

abbrev twoStepMatrix (q : ℕ) : GroupMat Sign q q := resetMatrix q * resetMatrix q

abbrev twoStepCarrier (q : ℕ) : GroupMat Sign q q :=
  (1 : GroupMat Sign q q) + twoStepMatrix q

def origin {q : ℕ} (hq : 0 < q) : Fin q := ⟨0, hq⟩

private theorem reset_coeff_support (q : ℕ) (i j : Fin q) :
    ((resetMatrix q) i j).coeff.support ⊆ {ofAdd true, (1 : Sign)} := by
  intro g hg
  have hne : ((resetMatrix q) i j).coeff g ≠ 0 :=
    Finsupp.mem_support_iff.mp hg
  rw [matrix_coefficient] at hne
  split_ifs at hne with h
  · rcases h with h | h
    · exact Finset.mem_insert.mpr (Or.inl h.2)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h.2))
  · exact (hne rfl).elim

theorem twoStep_origin_square_coeff (q : ℕ) (hq : 0 < q) :
    ((twoStepMatrix q) (origin hq) (origin hq)).coeff (1 : Sign) = 1 := by
  classical
  unfold twoStepMatrix
  have hmul :
      ((resetMatrix q * resetMatrix q) (origin hq) (origin hq)).coeff (1 : Sign) = 1 := by
    rw [Matrix.mul_apply]
    have hterm (k : Fin q) :
        (((resetMatrix q) (origin hq) k) * ((resetMatrix q) k (origin hq))).coeff
          (1 : Sign) = if k = origin hq then 1 else 0 := by
      rw [MonoidAlgebra.coeff_mul_apply_left]
      rw [Finsupp.sum_of_support_subset _ (reset_coeff_support q (origin hq) k) _]
      · by_cases hk : k = origin hq
        · subst k
          simp [matrix_coefficient, origin, show (ofAdd true : Sign) ≠ 1 by decide,
            show (1 : Sign) ≠ ofAdd true by decide,
            show (ofAdd true : Sign)⁻¹ = ofAdd true by decide]
        · have hk0 : k.val ≠ 0 := by
            intro hz
            apply hk
            exact Fin.ext hz
          have hkn : k ≠ (⟨0, hq⟩ : Fin q) := by simpa [origin] using hk
          simp [matrix_coefficient, hkn, hk0, origin,
            show (ofAdd true : Sign) ≠ 1 by decide,
            show (1 : Sign) ≠ ofAdd true by decide,
            show (ofAdd true : Sign)⁻¹ = ofAdd true by decide]
      · intro g hg
        simp
    have hcoeff :
        ((∑ i : Fin q,
          ((resetMatrix q) (origin hq) i * (resetMatrix q) i (origin hq))).coeff
          (1 : Sign)) =
          ∑ i : Fin q,
            (((resetMatrix q) (origin hq) i * (resetMatrix q) i (origin hq))).coeff
              (1 : Sign) := by
      have hs := MonoidAlgebra.coeff_sum (Finset.univ : Finset (Fin q))
        (fun i : Fin q =>
          ((resetMatrix q) (origin hq) i * (resetMatrix q) i (origin hq)))
      have hs1 := congrArg (fun f : Sign →₀ ℕ => f (1 : Sign)) hs
      simpa using hs1
    rw [hcoeff]
    simp_rw [hterm]
    simp
  exact hmul

theorem twoStep_origin_coeff (q : ℕ) (hq : 0 < q) :
    ((twoStepCarrier q) (origin hq) (origin hq)).coeff (1 : Sign) = 2 := by
  unfold twoStepCarrier
  change (((1 : GroupMat Sign q q) (origin hq) (origin hq)) +
    ((twoStepMatrix q) (origin hq) (origin hq))).coeff (1 : Sign) = 2
  rw [MonoidAlgebra.coeff_add]
  rw [Finsupp.add_apply, twoStep_origin_square_coeff q hq]
  simp


end D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
