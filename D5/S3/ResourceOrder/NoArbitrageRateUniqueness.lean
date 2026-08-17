/- GID: D5/S3/ResourceOrder/NoArbitrageRateUniqueness
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/NoArbitrageRateUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive reversible rates are unique when neither cross-rate cycle admits gain. -/

import Mathlib.Data.Real.Basic

namespace D5.S3.ResourceOrder.NoArbitrageRateUniqueness

/-- Two positive reversible exchange rates are equal exactly when composing either rate with the
inverse of the other cannot produce a cycle multiplier greater than one. -/
theorem no_arbitrage_iff_reversible_rates_eq
    (rate1 rate2 : Real) (hrate1 : 0 < rate1) (hrate2 : 0 < rate2) :
    rate1 / rate2 <= 1 ∧ rate2 / rate1 <= 1 ↔ rate1 = rate2 := by
  constructor
  · rintro ⟨h12, h21⟩
    exact le_antisymm ((div_le_one hrate2).mp h12) ((div_le_one hrate1).mp h21)
  · rintro rfl
    simp [hrate1.ne']

end D5.S3.ResourceOrder.NoArbitrageRateUniqueness
