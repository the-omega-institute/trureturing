/- GID: D5/S0/Conventions/CanonicalInterchangeability
   generality: I
   mirror-B: D5/B/S0/Conventions/CanonicalInterchangeability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Faithful digit specifications are canonically interchangeable through decoding. -/

import D5.S0.Conventions.WDigits

namespace D5.S0.Conventions

/-- Decoding transports words bijectively between any two faithful digit specifications,
preserving every property that factors through the decoded natural number. -/
theorem canonical_interchangeability :
    (∀ {Word₁ Word₂ : Type} (decode₁ : Word₁ ≃ ℕ) (decode₂ : Word₂ ≃ ℕ),
      Function.Bijective (fun w => decode₂.symm (decode₁ w)) ∧
      (∀ w : Word₁, decode₂ (decode₂.symm (decode₁ w)) = decode₁ w) ∧
      (∀ (φ : ℕ → Prop) (w : Word₁),
        φ (decode₁ w) ↔ φ (decode₂ (decode₂.symm (decode₁ w))))) ∧
    Function.Bijective (wEncoding.symm : WDigitString → ℕ) := by
  constructor
  · intro Word₁ Word₂ decode₁ decode₂
    refine ⟨(decode₁.trans decode₂.symm).bijective, ?_, ?_⟩
    · intro w
      exact decode₂.apply_symm_apply (decode₁ w)
    · intro φ w
      rw [decode₂.apply_symm_apply]
  · exact wEncoding.symm.bijective

end D5.S0.Conventions
