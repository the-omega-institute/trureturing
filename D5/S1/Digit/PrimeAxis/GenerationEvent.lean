/- GID: D5/S1/Digit/PrimeAxis/GenerationEvent
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxis/GenerationEvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A legal generation event is a finitely supported vector of prime exponents. -/

import D5.S1.Digit.PrimeAxis.PrimeAxisNormalizationUnique

namespace D5.S1.Digit.PrimeAxis.GenerationEvent

open D5.S1.Digit

/- The clause defines a legal generation event as a finitely supported vector on the prime
axes. In this repository that finiteness is not a side condition to be checked: the state
type carries its digits as a `Finsupp`, so support is finite by construction and every axis
outside it contributes nothing.

Stating it is still the content of the clause. Without these, a reader has the type but
no theorem that says what the type buys, and the definition's own claim - finite support,
so only finitely many axes are ever active - is left to be read off a signature. -/

/-- Only finitely many prime axes carry a nonzero row. -/
theorem support_finite (u : PrimeAxisTable) : (u.digits.support : Set PrimeAxis).Finite :=
  u.digits.support.finite_toSet

/-- Off the support the row is zero, hence the exponent there is zero. -/
theorem axisExponent_eq_zero_of_not_mem (u : PrimeAxisTable) (p : PrimeAxis)
    (hp : p ∉ u.digits.support) : axisExponent u p = 0 := by
  have h : u.digits p = 0 := Finsupp.notMem_support_iff.mp hp
  simp [axisExponent, h, rawValue]

/-- A generation event is legal: finitely supported, with every axis outside the support
carrying exponent zero, and every axis inside carrying canonical digits. -/
theorem generation_event_is_legal (u : PrimeAxisTable) :
    (u.digits.support : Set PrimeAxis).Finite ∧
      (∀ p ∉ u.digits.support, axisExponent u p = 0) ∧
        ∀ p, CanonicalRaw (u.digits p) :=
  ⟨support_finite u, fun p hp => axisExponent_eq_zero_of_not_mem u p hp, u.canonical⟩

end D5.S1.Digit.PrimeAxis.GenerationEvent
