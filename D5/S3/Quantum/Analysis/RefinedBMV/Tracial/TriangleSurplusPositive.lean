/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TriangleSurplusPositive
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative degree-seventeen triangle surpluses by six kernel sign checks. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleSurplusParity

/-! Positivity of the three weighted triangle surpluses on the ordered
spectral quadrant. Each edge and parity is checked in a separate declaration. -/

namespace RefinedBMV.Tracial.TriangleSurplus

section Checks

-- Each declaration reduces one large packed integer calculation in the kernel.
set_option maxHeartbeats 0
set_option maxRecDepth 8192

private theorem check01Even : packedCheck 1984 0 false = true := by
  decide +kernel

private theorem check01Odd : packedCheck 1984 0 true = true := by
  decide +kernel

private theorem check02Even : packedCheck 1984 1 false = true := by
  decide +kernel

private theorem check02Odd : packedCheck 1984 1 true = true := by
  decide +kernel

private theorem check12Even : packedCheck 1984 2 false = true := by
  decide +kernel

private theorem check12Odd : packedCheck 1984 2 true = true := by
  decide +kernel

end Checks

/-- The cleared surpluses are positive when both fourth-root ratios
exceed one. -/
theorem surplus_pos (x y : ℝ) (hx : 1 < x) (hy : 1 < y) :
    0 < (surplus x y).1 ∧ 0 < (surplus x y).2.1 ∧ 0 < (surplus x y).2.2 := by
  have hx' : 1 + (x - 1) = x := by ring
  have hy' : 1 + (y - 1) = y := by ring
  have aux (e : Fin 3) (he : packedCheck 1984 e.val false = true)
      (ho : packedCheck 1984 e.val true = true) : 0 < select e (surplus x y) := by
    simpa only [hx', hy'] using pos_of_packedChecks e (x - 1) (y - 1)
      (sub_pos.mpr hx) (sub_pos.mpr hy) he ho
  exact ⟨aux 0 check01Even check01Odd, aux 1 check02Even check02Odd, aux 2 check12Even check12Odd⟩

#print axioms surplus_pos

end RefinedBMV.Tracial.TriangleSurplus
