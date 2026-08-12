# The Zeckendorf Up-Shift Displacement Decode Is a Golden Beatty Reading

## Abstract

The Zeckendorf up-shift displacement decode equals the shifted golden Beatty reading.

**Theorem 1.1 (The up-shift displacement decode equals floor((v+1) phi) minus one).**

$$S(v) = \lfloor (v+1)\cdot\varphi \rfloor - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ZeckendorfDisplacementReading.displacement_decode_eq_beatty_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Zeckendorf up-shift displacement decode of v is S(v) = sum over the occupied Fibonacci indices k of the canonical Zeckendorf digits of v of F_{k+1} — each index k is shifted up to k+1 (the up-shift of slope phi, not the down-slope 1/phi). The identity is S(v) = floor((v+1) * phi) - 1 for every v; for instance S(0..6) = 0, 2, 3, 5, 7, 8, 10, matching floor((v+1) phi) - 1 including the boundary v = 0.

Aggregate Binet, F_{k+1} = phi * F_k + psi^k summed over the digit list, reduces the real value of S(v) to v * phi + sum_k psi^k. On a canonical Zeckendorf digit list (gaps at least 2, indices at least 2) the conjugate tail sum_k psi^k lies strictly in the interval (-1/phi^2, 1/phi), so S(v) is the unique integer in (v*phi - 1/phi^2, v*phi + 1/phi); Int.floor_eq_iff with phi - 1 = 1/phi closes the closed form.

Only the up-shift displacement reading identity S(v) = floor((v+1) phi) - 1 is recorded. The deficit forms beta'(v) = S(v) - v*phi and beta(v) = S(v) - v*psi, and the downstream length recovery ell = log n, are not covered by this statement.

## References

- Truth anchor: `D5/S1/Deficit/ZeckendorfDisplacementReading.displacement_decode_eq_beatty_floor`
- Dependency: [D5/S0/Conventions/WDigits](../../S0/Conventions/WDigits.md)
