/- GID: D5/S1/Recurrence/CassiniFricke
   generality: G
   mirror-B: D5/B/S1/Recurrence/CassiniFricke
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Cassini-Fricke quadratic form is an alternating invariant of Binet recurrences. -/

import Mathlib

namespace D5.S1.Recurrence.CassiniFricke

theorem cassini_fricke {R : Type*} [CommRing R] (φ ψ A B : R) (K : ℕ)
    (hφ : φ ^ 2 = φ + 1) (hψ : ψ ^ 2 = ψ + 1)
    (hsum : φ + ψ = 1) (hprod : φ * ψ = -1) :
    (A * φ ^ (K + 1) + B * ψ ^ (K + 1)) ^ 2 -
        (A * φ ^ (K + 1) + B * ψ ^ (K + 1)) * (A * φ ^ K + B * ψ ^ K) -
      (A * φ ^ K + B * ψ ^ K) ^ 2 = -5 * A * B * (-1) ^ K := by
  have hpq : φ ^ K * ψ ^ K = (-1) ^ K := by
    rw [← mul_pow, hprod]
  rw [pow_succ, pow_succ]
  linear_combination
    (A ^ 2 * (φ ^ K) ^ 2) * hφ +
    (B ^ 2 * (ψ ^ K) ^ 2) * hψ +
    (2 * A * B * (φ ^ K) * (ψ ^ K)) * hprod +
    (-(A * B * (φ ^ K) * (ψ ^ K))) * hsum +
    (-5 * A * B) * hpq

end D5.S1.Recurrence.CassiniFricke
