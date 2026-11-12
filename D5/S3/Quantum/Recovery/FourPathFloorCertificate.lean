/- GID: D5/S3/Quantum/Recovery/FourPathFloorCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathFloorCertificate
   mirror-E: none(waiver:finite-rational-section-71-certificate)
   anchors: []
   utility: none
   digest: The seven rational segment majorants in Section 71 are uniformly below the common floor 49359/40000. -/

import Mathlib.Tactic

/-! This is the finite arithmetic core of the Section 71 estimate.  It records
the seven displayed majorants only; it does not define the analytic quantity
`G_-`, the triangular domain, or the energy threshold. -/

noncomputable section
namespace D5.S3.Quantum.Recovery.FourPathFloorCertificate
set_option autoImplicit false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.setOption false

/-- The non-radical upper bounds in the seven rows of (71.8). -/
def segmentNonroot : Fin 7 → ℝ :=
  ![467893519 / 512000000, 36315767 / 40000000,
    284721081 / 320000000, 139458013 / 160000000,
    273110971 / 320000000, 66826479 / 80000000,
    261500861 / 320000000]

/-- The radical upper bounds in the seven rows of (71.8). -/
def segmentRadical : Fin 7 → ℝ :=
  ![1 / 5, 79 / 250, 67 / 200, 9 / 25, 7 / 20, 31 / 100, 137 / 500]

/-- Every displayed Section 71 segment majorant is strictly below the common
floor used in the final comparison.  This theorem is only the finite rational
certificate; the analytic and energy bridges of Theorem 71.1 remain open. -/
theorem segment_majorants_lt_floor :
    ∀ i : Fin 7,
      segmentNonroot i + segmentRadical i < (49359 : ℝ) / 40000 := by
  intro i
  fin_cases i <;> norm_num [segmentNonroot, segmentRadical]

end D5.S3.Quantum.Recovery.FourPathFloorCertificate
