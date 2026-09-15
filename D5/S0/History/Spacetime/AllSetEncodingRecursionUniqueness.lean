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
  funext x
  induction x using ZFSet.mem_wf.induction with
  | h x ih =>
    rw [hf x, show Enc x = encStep x (fun y _ => Enc y) from
      WellFounded.fix_eq ZFSet.mem_wf encStep x]
    unfold encStep
    by_cases hx : x ∈ ZFSet.omega
    · simp only [if_pos hx]
    · simp only [if_neg hx]
      apply congrArg (ZFSet.pair (natOrd 1))
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_image]
      constructor
      · rintro ⟨y, hy, he⟩
        exact ⟨y, hy, by simpa only [dif_pos hy, ← ih y hy] using he⟩
      · rintro ⟨y, hy, he⟩
        exact ⟨y, hy, by simpa only [ih y hy, dif_pos hy] using he⟩

end

end D5.S0.History.Spacetime.AllSetEncodingRecursionUniqueness
