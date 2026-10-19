/- GID: D5/S3/Quantum/Fibers/TwoCopyReadoutFiber
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The real two-copy Bell readout has exactly the q ↔ 1-q observational fiber. -/

import D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder Kronecker

namespace D5.S3.Quantum.Fibers.TwoCopyReadoutFiber

open D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase

/-- The two-copy Bell readout identifies exactly the two points related by
    the hidden-phase involution `q ↦ 1 - q`. -/
theorem two_copy_bell_readout_fiber (q r : Set.Icc (0 : ℝ) 1) :
    twoCopyProbability q = twoCopyProbability r ↔
      ((q : ℝ) = (r : ℝ) ∨ (q : ℝ) + (r : ℝ) = 1) := by
  constructor
  · intro h
    have hq := (two_copy_bell_readout q).2.2.2
    have hr := (two_copy_bell_readout r).2.2.2
    rw [hq, hr] at h
    have hs : (1 - 2 * (q : ℝ)) ^ 2 = (1 - 2 * (r : ℝ)) ^ 2 := by
      nlinarith [h]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hsame | hneg
    · left
      linarith
    · right
      linarith
  · intro h
    have hq := (two_copy_bell_readout q).2.2.2
    have hr := (two_copy_bell_readout r).2.2.2
    rw [hq, hr]
    rcases h with hsame | hsum
    · rw [hsame]
    · have hlin : 1 - 2 * (r : ℝ) = -(1 - 2 * (q : ℝ)) := by
        linarith
      rw [hlin]
      ring

#print axioms two_copy_bell_readout_fiber

end D5.S3.Quantum.Fibers.TwoCopyReadoutFiber
