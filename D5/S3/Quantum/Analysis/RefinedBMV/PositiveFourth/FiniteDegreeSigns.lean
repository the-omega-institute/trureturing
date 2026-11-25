/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/FiniteDegreeSigns
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel verification of finite-degree four-copy signs below degree eleven. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FiniteGapCircuit

/-! A finite sum of composition monomials supplies all six signs below degree eleven. -/

open RefinedBMV.ThreeBlockGram.PositiveSpectrum


namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel reduces every coefficient sign at the fixed degree.
private theorem checked1 (sign : GramSign) : checkFiniteSign 1 sign = true := by
  cases sign <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel reduces every coefficient sign at the fixed degree.
private theorem checked2 (sign : GramSign) : checkFiniteSign 2 sign = true := by
  cases sign <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel reduces every coefficient sign at the fixed degree.
private theorem checked3 (sign : GramSign) : checkFiniteSign 3 sign = true := by
  cases sign <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel reduces every coefficient sign at the fixed degree.
private theorem checked4 (sign : GramSign) : checkFiniteSign 4 sign = true := by
  cases sign <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel reduces every coefficient sign at the fixed degree.
private theorem checked5 (sign : GramSign) : checkFiniteSign 5 sign = true := by
  cases sign <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel reduces every coefficient sign at the fixed degree.
private theorem checked6 (sign : GramSign) : checkFiniteSign 6 sign = true := by
  cases sign <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel reduces every coefficient sign at the fixed degree.
private theorem checked7 (sign : GramSign) : checkFiniteSign 7 sign = true := by
  cases sign <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel reduces every coefficient sign at the fixed degree.
private theorem checked8 (sign : GramSign) : checkFiniteSign 8 sign = true := by
  cases sign <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel reduces every coefficient sign at the fixed degree.
private theorem checked9 (sign : GramSign) : checkFiniteSign 9 sign = true := by
  cases sign <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel reduces every coefficient sign at the fixed degree.
private theorem checked10 (sign : GramSign) : checkFiniteSign 10 sign = true := by
  cases sign <;> decide +kernel

private theorem checked_small (p : ℕ) (hp : 0 < p) (hsmall : p < 11) (sign : GramSign) :
    checkFiniteSign p sign = true := by
  interval_cases p
  · exact checked1 sign
  · exact checked2 sign
  · exact checked3 sign
  · exact checked4 sign
  · exact checked5 sign
  · exact checked6 sign
  · exact checked7 sign
  · exact checked8 sign
  · exact checked9 sign
  · exact checked10 sign

theorem sixSigns_of_degree_lt_eleven (p : ℕ) (hp : 0 < p) (hsmall : p < 11)
    {r t : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (ht : 0 < t) (ht₁ : t ≤ 1) :
    (kernelQuarticData (fun i j k l ↦
      2 * spectralDefect p ![r ^ 4 * t ^ 4, t ^ 4, 1] i j k l)).SixSigns :=
  finiteSigns_of_checks p (checked_small p hp hsmall) hr hr₁ ht ht₁

#print axioms sixSigns_of_degree_lt_eleven

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
