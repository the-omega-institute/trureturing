# Golden Radical Divided-Difference Certificate

## Abstract

A genuine square-modulus lift in the fixed golden ring constructs a divided geometric sum with an explicit quadratic equation and algebraic integrality.

**Definition 1.1 (Homogeneous power sum).**

Lean statement: `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.powerSum`

*Formalization.* `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.powerSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural n and elements x,a of a commutative ring, powerSum(n,x,a) is the sum of x^i*a^(n-1-i) over 0<=i<n. Its value at n=0 is zero. This is the polynomial divided difference of X^n, with no division by x-a and with coincident arguments allowed.

**Definition 1.2 (Integral second divided difference).**

Lean statement: `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.secondDifference`

*Formalization.* `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.secondDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

secondDifference(n,x,a) is the sum over 0<=i<n of a^(n-1-i)*powerSum(i,x,a). All coefficients are integers. Multiplication by x-a gives powerSum(n,x,a)-n*a^(n-1), including the n=0 and n=1 boundaries.

**Definition 1.3 (Specified candidate integral element).**

Lean statement: `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.dividedPowerSum`

*Formalization.* `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.dividedPowerSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In a field L, dividedPowerSum(n,x,a) is powerSum(n,x,a) divided by the natural-number cast of n. The public theorem explicitly requires positive n and characteristic zero. It never divides by x-a or by the lift witness b.

**Theorem 1.4 (Explicit integral generator from a square-modulus golden lift).**

$$\forall L \in Type, \operatorname{Implies}(\operatorname{And}(\operatorname{Field}(L), \operatorname{CharZero}(L)), \forall iota \in \operatorname{RingHom}(GoldenInt, L), \forall n \in Nat, \forall a \in GoldenInt, \forall b \in GoldenInt, \forall theta \in L, \operatorname{Implies}(\operatorname{And}(\operatorname{Lt}(0, n), \operatorname{And}(\operatorname{Eq}(theta^{n}, \operatorname{iota}(phi)), \operatorname{Eq}(phi, \operatorname{add}(a^{n}, \operatorname{mul}(\operatorname{NatCast}(GoldenInt, n)^{2}, b))))), \operatorname{And}(\operatorname{Eq}(\operatorname{mul}(\operatorname{sub}(theta, \operatorname{iota}(a)), \operatorname{dividedPowerSum}(n, theta, \operatorname{iota}(a))), \operatorname{mul}(\operatorname{NatCast}(L, n), \operatorname{iota}(b))), \operatorname{And}(\operatorname{Eq}(\operatorname{dividedPowerSum}(n, theta, \operatorname{iota}(a))^{2}, \operatorname{add}(\operatorname{mul}(\operatorname{iota}(a)^{\operatorname{natSub}(n, 1)}, \operatorname{dividedPowerSum}(n, theta, \operatorname{iota}(a))), \operatorname{mul}(\operatorname{iota}(b), \operatorname{secondDifference}(n, theta, \operatorname{iota}(a))))), \operatorname{IsIntegral}(Int, \operatorname{dividedPowerSum}(n, theta, \operatorname{iota}(a)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

L is any characteristic-zero field and iota is a ring homomorphism from the existing GoldenInt ring into L. For n>0, a,b in GoldenInt and theta in L, assume theta^n=iota(phi) and the actual equality phi=a^n+n^2*b in GoldenInt. The defined y is then integral over the integers and satisfies both displayed identities. No integral-basis or local-field theorem is assumed in the formal argument.

The proof sums the classical difference-of-powers identity twice. It obtains (theta-iota(a))*y=n*iota(b) and the quadratic equation, cancelling only the nonzero scalar n. Golden integers satisfy monic integer polynomials; theta is integral because its positive power is. Hence the second-difference coefficient is integral, and integrality transitivity through the explicit monic quadratic proves integrality of y.

The quadratic coefficients may contain theta. This is not a degree-at-most-two assertion over the golden number field. The lift hypothesis is not proved for an unknown WSS prime. The separate sharp n*rad(n) criterion and the full class-field statements are ordinary mathematical deductions in the existing WSS dossier, not further Lean conclusions here.

## References

- Truth anchor: `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.dividedPowerSum`
- Truth anchor: `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.powerSum`
- Truth anchor: `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.result`
- Truth anchor: `D5/S3/Arith/Radical/GoldenRadicalDividedDifference.secondDifference`
- Dependency: [D5/S0/Carrier/Ring](../../../S0/Carrier/Ring.md)
