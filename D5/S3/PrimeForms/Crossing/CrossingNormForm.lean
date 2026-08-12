/- GID: D5/S3/PrimeForms/Crossing/CrossingNormForm
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/CrossingNormForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The one-parameter crossing form Q_t(P,Q) = P²−(2t+1)PQ+(t²+t+1)Q² has discriminant identically −3, and for every integer t reduces under the explicit unimodular substitution (P,Q) ↦ (P−(t+1)Q, Q) to the principal Eisenstein/Löschian norm form x²+xy+y², so the whole family represents exactly the Eisenstein norms. This is the algebraic unified foundation of residual E.63's norm-state criterion; the crossing ⟺ continued-fraction-orbit biconditional and the generation-mechanism sub-results are not covered. -/

import Mathlib

namespace D5.S3.PrimeForms.Crossing.CrossingNormForm

/-- The 1-parameter **crossing / norm-state** binary quadratic form (residual E.63):
`Q_t(P,Q) = P² − (2t+1)PQ + (t²+t+1)Q²`. -/
def Qform (t P Q : ℤ) : ℤ := P ^ 2 - (2 * t + 1) * P * Q + (t ^ 2 + t + 1) * Q ^ 2

/-- The principal Eisenstein (Löschian) norm form `x² + xy + y²`, the norm of `ℤ[ω]`. -/
def eisNorm (x y : ℤ) : ℤ := x ^ 2 + x * y + y ^ 2

/-- Reduction: `Q_t` is the principal Eisenstein form under the explicit unimodular substitution
`(P,Q) ↦ (P − (t+1)Q, Q)`. -/
theorem Qform_eq_eisNorm (t P Q : ℤ) :
    Qform t P Q = eisNorm (P - (t + 1) * Q) Q := by
  unfold Qform eisNorm; ring

/-- The discriminant `b² − 4ac` of `Q_t` (with `a = 1`, `b = −(2t+1)`, `c = t²+t+1`) is identically
`−3`, independent of the parameter `t`. -/
theorem Qform_discriminant (t : ℤ) :
    (2 * t + 1) ^ 2 - 4 * (t ^ 2 + t + 1) = -3 := by ring

/-- **Eisenstein-norm-curve identification (E.63 unified foundation).** For every integer `t`, the
values represented by the crossing form `Q_t` are exactly the Eisenstein/Löschian numbers — the whole
one-parameter family collapses to the single value-set of the principal form `x² + xy + y²`. This is
the algebraic foundation on which residual E.63's norm-state criterion rests; the criterion's
`crossing ⟺ continued-fraction-orbit touches the norm curve` biconditional is not covered here. -/
theorem Qform_range_eq_eisNorm (t : ℤ) :
    Set.range (fun p : ℤ × ℤ => Qform t p.1 p.2)
      = Set.range (fun p : ℤ × ℤ => eisNorm p.1 p.2) := by
  ext n
  constructor
  · rintro ⟨⟨P, Q⟩, rfl⟩
    exact ⟨(P - (t + 1) * Q, Q), (Qform_eq_eisNorm t P Q).symm⟩
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨(x + (t + 1) * y, y), ?_⟩
    have hx : (x + (t + 1) * y) - (t + 1) * y = x := by ring
    show Qform t (x + (t + 1) * y) y = eisNorm x y
    rw [Qform_eq_eisNorm, hx]

end D5.S3.PrimeForms.Crossing.CrossingNormForm
