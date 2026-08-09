/- GID: D5/S0/Carrier/ZsqrtdImage
   generality: G
   mirror-B: D5/B/S0/Carrier/ZsqrtdImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The image of doubled golden coordinates is exactly the equal-parity Zsqrtd pairs. -/

import D5.S0.Carrier.Ring

namespace D5.S0.Carrier

theorem mem_range_toZsqrtd_iff (z : ℤ√5) :
    z ∈ Set.range toZsqrtd ↔ ∃ k : ℤ, z.re - z.im = 2 * k := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.a, by simp [toZsqrtd]⟩
  · rintro ⟨k, hk⟩
    refine ⟨⟨k, z.im⟩, ?_⟩
    apply Zsqrtd.ext
    · simp only [toZsqrtd]
      linarith
    · rfl

end D5.S0.Carrier
