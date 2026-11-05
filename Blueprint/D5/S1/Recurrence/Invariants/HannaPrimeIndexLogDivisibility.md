# Hanna's OEIS A381355 prime-index divisibility

## Abstract

An integral source series exists and its logarithmic derivative satisfies Hanna's prime divisibility.

The prime function is PrimePowerShiftLogDerivative.prime, the one-based prime schedule with prime(1)=2. The series have rational coefficients. Natural subtraction specifies the coefficient index n-1, and the asserted indices satisfy n>1. The inverse is formal power-series inversion. Casts to the rationals are displayed explicitly.

**Definition 1.1 (The source equations).**

$$\forall (F: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{IsSourceSeries}\left(F\right) \iff (\operatorname{coeff}\left(0, F\right) = 1) \land ((\operatorname{coeff}\left(1, F\right) = 1) \land (\forall (n: \mathbb{N}), (1 < n) \implies (\operatorname{coeff}\left(n, F^{\operatorname{PrimePowerShiftLogDerivative}.\operatorname{prime}\left(n\right)}\right) = 0)))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility.IsSourceSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A381355: prime-index divisibility of the logarithmic derivative of A381353*. URL: <https://oeis.org/A381355>.

*Commentary.*

OEIS A381353 NAME: "G.f. A(x) satisfies [x^n] A(x)^prime(n) = 0 for n > 1." Its PROGRAM initializes "my(A=[1,1])", fixing coefficients zero and one to one. These are the NAME and PROGRAM sections of revision 19; the entry has no page numbers. The source's A(x) is denoted F here, and coeff extracts a coefficient indexed from zero.

**Definition 1.2 (The sequence and its index).**

$$\forall (F: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \forall (n: \mathbb{N}), \operatorname{sourceTerm}\left(F, n\right) = \operatorname{coeff}\left(n - 1, (\operatorname{derivative}\left(F\right) \cdot (F)^{-1})\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility.sourceTerm` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A381355: prime-index divisibility of the logarithmic derivative of A381353*. URL: <https://oeis.org/A381355>.

*Commentary.*

OEIS A381355 NAME: "G.f. A(x) = x*F'(x)/F(x) where F(x) is the g.f. of A381353 that satisfies [x^n] F(x)^prime(n) = 0 for n > 1." This is the NAME section of revision 13, without page numbers. The entry's offset is one: its nth term is coeff (n-1) (derivative F * F⁻¹). The definition is total at zero, which is outside the asserted range.

**Definition 1.3 (Hanna's conjecture with source existence).**

$$claim = ((\exists (F: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{IsSourceSeries}\left(F\right)) \land (\forall (F: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), (\operatorname{IsSourceSeries}\left(F\right)) \implies (\forall (n: \mathbb{N}), (1 < n) \implies (\exists (z: \mathbb{Z}), \operatorname{sourceTerm}\left(F, n\right) = (\operatorname{PrimePowerShiftLogDerivative}.\operatorname{prime}\left(n\right): \mathbb{Q}) \cdot (z: \mathbb{Q})))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A381355: prime-index divisibility of the logarithmic derivative of A381353*. URL: <https://oeis.org/A381355>.

*Commentary.*

OEIS A381355 COMMENTS: "Conjecture: a(n) is divisible by prime(n) for n > 1." This is the COMMENTS section of revision 13, without page numbers. The first conjunct asserts existence of a rational source series. The second ranges over every such series. An integer z witnesses divisibility inside the rationals.

**Theorem 1.4 (Existence and prime divisibility).**

$$(\exists (F: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{IsSourceSeries}\left(F\right)) \land (\forall (F: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), (\operatorname{IsSourceSeries}\left(F\right)) \implies (\forall (n: \mathbb{N}), (1 < n) \implies (\exists (z: \mathbb{Z}), \operatorname{sourceTerm}\left(F, n\right) = (\operatorname{PrimePowerShiftLogDerivative}.\operatorname{prime}\left(n\right): \mathbb{Q}) \cdot (z: \mathbb{Q}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A381355: prime-index divisibility of the logarithmic derivative of A381353*. URL: <https://oeis.org/A381355>.

*Commentary.*

Reduction modulo a prime makes all positive coefficients below that prime vanish in the corresponding power. Exact integral corrections therefore construct a source series. The coefficient change under a power gives uniqueness among rational source series. The formal derivative identity makes the relevant product coefficient zero over the integers; cancellation of the nonzero prime and reduction modulo that prime isolate the coefficient of the logarithmic derivative.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility.IsSourceSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility.sourceTerm`
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport](../LinearRows/LinearExponentDyadicSupport.md)
- Dependency: [D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative](../Parity/PrimePowerShiftLogDerivative.md)
- Dependency: [D5/S1/Recurrence/Residue/ContinuedFractionOddSquare](../Residue/ContinuedFractionOddSquare.md)
