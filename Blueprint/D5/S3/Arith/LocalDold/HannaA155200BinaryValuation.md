# Hanna A155200: exact binary valuation

## Abstract

Every coefficient of Hanna's A155200 exponential has an odd integer quotient by the power of two given by its binary digit sum.

**Definition 1.1 (The literal exponential and the odd quotient).**

$$claim = \left(\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{Odd}\left(z\right) \land \operatorname{PowerSeries}.\operatorname{coeff}\left(n, \operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{PowerSeries}.\operatorname{mk}\left((fun k: \mathbb{N} \mapsto \operatorname{ite}\left(k = 0, 0, \frac{(2: \mathbb{Q})^{k^{2}}}{(k: \mathbb{Q})}\right))\right), \operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right)\right)\right) = (2: \mathbb{Q})^{\operatorname{List}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{digits}\left(2, n\right)\right)} \cdot (z: \mathbb{Q})\right)$$

*Formalization.* `D5/S3/Arith/LocalDold/HannaA155200BinaryValuation.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2009). *OEIS A155200 exact binary valuation conjecture*. URL: <https://oeis.org/A155200/internal>.

*Commentary.*

%N G.f.: A(x) = exp( Sum_{n>=1} 2^(n^2) * x^n/n ), a power series in x with integer coefficients. %C Conjecture: highest exponent of 2 dividing a(n) = A000120(n) = number of 1's in binary expansion of n, so that a(n)/2^A000120(n) is odd for n >= 0. - _Paul D. Hanna_, Sep 01 2009 OEIS A155200 has no page number; these are its NAME and COMMENTS lines, revision #39. PowerSeries.exp and PowerSeries.subst describe the formal exponential over the rationals. PowerSeries.coeff extracts ordinary coefficients. The exponent has zero constant coefficient. Nat.digits 2 n lists the binary digits, whose List.sum is the number of ones; the empty list at zero sums to zero. Odd applies to the integer z, which is then cast to the rationals. All natural indices, including zero, occur.

**Theorem 1.2 (The exact valuation holds at every natural index).**

$$\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{Odd}\left(z\right) \land \operatorname{PowerSeries}.\operatorname{coeff}\left(n, \operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{PowerSeries}.\operatorname{mk}\left((fun k: \mathbb{N} \mapsto \operatorname{ite}\left(k = 0, 0, \frac{(2: \mathbb{Q})^{k^{2}}}{(k: \mathbb{Q})}\right))\right), \operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right)\right)\right) = (2: \mathbb{Q})^{\operatorname{List}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{digits}\left(2, n\right)\right)} \cdot (z: \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/HannaA155200BinaryValuation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155200 exact binary valuation conjecture*. URL: <https://oeis.org/A155200/internal>.

*Commentary.*

The geometric series with coefficients 2^n has integer coefficients. HannaDiagonalGhostPowerIntegrality.result transfers this integrality to the exponential with weights 2^(n^2). Differentiating gives the coefficient recurrence. Strong induction constructs integers b(n) with n! a(n)=2^n b(n) and b(n) congruent to one modulo four: the first normalized term is b(n-1), and every other term has a factor divisible by four. Legendre's factorial digit-sum identity and coprime cancellation give the odd integer z. No convergence or truncation condition is used.

## References

- Truth anchor: `D5/S3/Arith/LocalDold/HannaA155200BinaryValuation.claim`
- Truth anchor: `D5/S3/Arith/LocalDold/HannaA155200BinaryValuation.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](../../../S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](../../../S1/Recurrence/Invariants/CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity](../../../S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.md)
- Dependency: [D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality](../../../S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.md)
- Dependency: [D5/S3/Arith/FactorialRatio/BalaA361034Parity](../FactorialRatio/BalaA361034Parity.md)
