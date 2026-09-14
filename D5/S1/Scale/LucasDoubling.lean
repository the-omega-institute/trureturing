/- GID: D5/S1/Scale/LucasDoubling
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The golden Lucas trace satisfies the doubling identity L_{2n} = L_n^2 - 2(-1)^n. Since goldenLucas n = trace (phi^n) and phi^(2n) = (phi^n)^2, the identity follows from the golden-ring trace-square relation trace (x^2) = trace x ^ 2 - 2 * norm x together with the multiplicativity of the norm norm (phi^n) = (-1)^n. The norm-one conjugate pair doubling frozen elsewhere is the product-one case; this is the discriminant-five (product minus-one) instance, which contributes the sign term. -/

import D5.S1.Scale.Lucas
import D5.S0.Carrier.Units

namespace D5.S1.Scale

open D5.S0.Carrier

/-- Golden-ring trace-square relation: for any golden integer `x`,
`trace (x^2) = trace x ^ 2 - 2 * norm x`. This is the `ℤ[φ]` analogue of the `2×2`-matrix identity
`tr(M²) = tr(M)² − 2·det(M)`. -/
theorem trace_sq (x : GoldenInt) : trace (x ^ 2) = trace x ^ 2 - 2 * norm x := by
  simp only [pow_two, trace, norm, a_mul, b_mul]
  ring

/-- **Golden Lucas doubling identity.** The integral Lucas sequence `goldenLucas n = trace (phi^n)`
satisfies `L_{2n} = L_n^2 - 2(-1)^n`:
`goldenLucas (2 * n) = goldenLucas n ^ 2 - 2 * (-1 : ℤ) ^ n`.

Since `phi^(2n) = (phi^n)^2`, this reduces to the trace-square relation `trace_sq` applied to `phi^n`,
using `norm (phi^n) = (-1)^n` (multiplicativity of the norm with `norm phi = -1`). -/
theorem golden_lucas_two_mul (n : ℕ) :
    goldenLucas (2 * n) = goldenLucas n ^ 2 - 2 * (-1 : ℤ) ^ n := by
  calc goldenLucas (2 * n)
      = trace ((phi ^ n) ^ 2) := by rw [goldenLucas, pow_mul']
    _ = trace (phi ^ n) ^ 2 - 2 * norm (phi ^ n) := trace_sq (phi ^ n)
    _ = goldenLucas n ^ 2 - 2 * (-1 : ℤ) ^ n := by
        rw [← golden_lucas_eq_trace_phi_pow, norm_phi_pow]

end D5.S1.Scale
