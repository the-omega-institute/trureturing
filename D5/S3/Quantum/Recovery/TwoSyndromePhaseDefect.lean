/- GID: D5/S3/Quantum/Recovery/TwoSyndromePhaseDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/TwoSyndromePhaseDefect
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   digest: A two-syndrome phase mixture loses unit visibility unless its phases agree. -/

import Mathlib

/-!
# Two-syndrome phase defect

The exact loss of visibility of a two-phase mixture is a weighted squared
phase separation. The source treats complex scalars explicitly; the physical
probability specialization uses a real scalar in the unit interval.
-/

namespace D5.S3.Quantum.Recovery.TwoSyndromePhaseDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Coherence multiplier after forgetting which phase branch occurred. -/
def phaseMix (p u v : ℂ) : ℂ := (1 - p) * u + p * v

/-- The visibility deficit is exactly a weighted phase separation. -/
theorem weighted_phase_defect (p u v : ℂ)
    (hp : star p = p) (hu : star u * u = 1) (hv : star v * v = 1) :
    star (phaseMix p u v) * phaseMix p u v =
      1 - p * (1 - p) * (star (u - v) * (u - v)) := by
  calc
    star (phaseMix p u v) * phaseMix p u v =
        (1 - p) * (star u * u) + p * (star v * v) -
          p * (1 - p) * (star (u - v) * (u - v)) := by
      simp only [phaseMix, star_add, star_mul, star_sub, star_one, hp]
      ring
    _ = 1 - p * (1 - p) * (star (u - v) * (u - v)) := by
      rw [hu, hv]
      ring

/-- If both branches occur, unit visibility forces equality of their phases.
No postselection, numerical approximation, or finite grid is used. -/
theorem unit_visibility_iff_phases_equal (p u v : ℂ)
    (hp : star p = p) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hu : star u * u = 1) (hv : star v * v = 1) :
    star (phaseMix p u v) * phaseMix p u v = 1 ↔ u = v := by
  constructor
  · intro hVisible
    have h := weighted_phase_defect p u v hp hu hv
    rw [hVisible] at h
    have hzero : p * (1 - p) * (star (u - v) * (u - v)) = 0 := by
      linear_combination h
    have hweight : p * (1 - p) ≠ 0 :=
      mul_ne_zero hp0 (sub_ne_zero.mpr (Ne.symm hp1))
    have hdiff : star (u - v) * (u - v) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hweight
    rcases mul_eq_zero.mp hdiff with hs | hd
    · have hd : u - v = 0 := by
        simpa only [star_star, star_zero] using congrArg star hs
      exact sub_eq_zero.mp hd
    · exact sub_eq_zero.mp hd
  · intro huv
    subst v
    have hMix : phaseMix p u u = u := by unfold phaseMix; ring
    rw [hMix, hu]

/-- Equally weighted opposite phases erase the coherence exactly. -/
theorem opposite_phase_erasure :
    phaseMix (1 / 2) 1 (-1) = 0 := by
  norm_num [phaseMix]

#print axioms weighted_phase_defect
#print axioms unit_visibility_iff_phases_equal
#print axioms opposite_phase_erasure

end D5.S3.Quantum.Recovery.TwoSyndromePhaseDefect
