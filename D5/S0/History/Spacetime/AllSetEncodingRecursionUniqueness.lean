/- GID: D5/S0/History/Spacetime/AllSetEncodingRecursionUniqueness
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/AllSetEncodingRecursionUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every total set function satisfying the Zeckendorf membership recursion equals the recursive encoding. -/

import D5.S0.History.Spacetime.AllSetZeckendorfEncoding

set_option autoImplicit false

universe u

namespace D5.S0.History.Spacetime.AllSetEncodingRecursionUniqueness

open D5.S0.History.Spacetime.AllSetZeckendorfEncoding

noncomputable section

attribute [local instance] Classical.allZFSetDefinable Classical.propDecidable

/-- Every total set function satisfying the natural-leaf and member-image recursion equals Enc. -/
theorem enc_unique (f : ZFSet.{u} → ZFSet.{u})
    (hf : ∀ x, f x = if x ∈ ZFSet.omega then NatZ (natIndex x)
      else ZFSet.pair (natOrd 1) (ZFSet.image f x)) : f = Enc := by
  sorry

end

end D5.S0.History.Spacetime.AllSetEncodingRecursionUniqueness
