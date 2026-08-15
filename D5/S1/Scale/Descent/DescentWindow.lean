/- GID: D5/S1/Scale/Descent/DescentWindow
   generality: I
   mirror-B: D5/B/S1/Scale/Descent/DescentWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pell-type square bounds force the strict descent window. -/

import Mathlib

namespace D5.S1.Scale.Descent.DescentWindow

/- Provenance: Native integer-arithmetic proof over pinned mathlib. Repository,
pinned-mathlib, and LeanSearch queries found no exact descent-window theorem. -/

/-- The two Pell-type square bounds force the descent window
`T <= c < 4T / 3`, with the strict upper bound written without division. -/
theorem descent_window {c T : ℤ} (hT : 3 ≤ T) (hc : 0 ≤ c)
    (hlower : T ^ 2 - 1 ≤ c ^ 2)
    (hupper : 3 * c ^ 2 ≤ 4 * (T ^ 2 - 1)) :
    T ≤ c ∧ 3 * c < 4 * T := by
  constructor
  · by_contra h
    have hdiff : (1 : ℤ) ≤ T - c := by omega
    have hsum : (3 : ℤ) ≤ T + c := by omega
    have hmul : (1 : ℤ) * 3 ≤ (T - c) * (T + c) :=
      mul_le_mul hdiff hsum (by norm_num) (by omega)
    ring_nf at hlower hmul
    omega
  · by_contra h
    have hratio : 4 * T ≤ 3 * c := by omega
    have hsq : (4 * T) * (4 * T) ≤ (3 * c) * (3 * c) :=
      mul_self_le_mul_self (by omega) hratio
    ring_nf at hupper hsq
    omega

end D5.S1.Scale.Descent.DescentWindow
