# Bala's even-step Fibonacci-polynomial quotient

## Abstract

Positive even Fibonacci-polynomial steps have integral odd product-sum quotients.

OEIS A349272, COMMENT 1: Let m be an even positive integer. We conjecture that the sequence defined by b_m(n) = Product_{k = 1..2*n+1} Fibonacci(m*k) / Sum_{k = 1..2*n+1} Fibonacci(m*k) is integral. The formula given below proves the conjecture in the present case m = 2. The cases m = 4 and m = 6 of the conjecture can be proved in a similar manner.

OEIS A349272, COMMENT 2 (an unpaginated entry): More generally, if F(n,x) denotes the n-th Fibonacci polynomial we conjecture that, for each n, the rational function Product_{k = 1..2*n+1} F(m*k,x) / Sum_{k = 1..2*n+1} F(m*k,x) is an integral polynomial.

The existing fibonacciRecurrencePolynomial has initial values 0 and 1 and recurrence fibonacciRecurrencePolynomial(j+2) = X*fibonacciRecurrencePolynomial(j+1) + fibonacciRecurrencePolynomial(j). The index n starts at zero, as in the entry's offset. Products and sums include both endpoints. An integral polynomial has integer coefficients. The quotient is an equality in RatFunc Rat; it makes no pointwise division assertion at a zero of the denominator.

**Definition 1.1 (The odd product).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \operatorname{numerator}\left(m, n\right) = \prod_{k \in \operatorname{Finset}.\operatorname{Icc}\left(1, 2 \cdot n + 1\right)} \operatorname{fibonacciRecurrencePolynomial}\left(m \cdot k\right)$$

*Formalization.* `D5/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality.numerator` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A349272, COMMENT 2: even-step Fibonacci-polynomial integrality*. URL: <https://oeis.org/A349272/internal>.

*Commentary.*

The product in COMMENT 2 runs over k from 1 through 2*n+1, at step m.

**Definition 1.2 (The odd partial sum).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \operatorname{denominator}\left(m, n\right) = \sum_{k \in \operatorname{Finset}.\operatorname{Icc}\left(1, 2 \cdot n + 1\right)} \operatorname{fibonacciRecurrencePolynomial}\left(m \cdot k\right)$$

*Formalization.* `D5/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality.denominator` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A349272, COMMENT 2: even-step Fibonacci-polynomial integrality*. URL: <https://oeis.org/A349272/internal>.

*Commentary.*

The sum in COMMENT 2 uses precisely the same indices as the product.

**Definition 1.3 (The polynomial assertion).**

$$claim \Leftrightarrow \left(\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; 2 \le m \Rightarrow \left(\operatorname{Even}\left(m\right) \Rightarrow \left(\operatorname{denominator}\left(m, n\right) \ne 0 \land \left(\exists H \in \operatorname{Polynomial}\left(\mathrm{Int}\right),\; \frac{\operatorname{algebraMap}\left(\operatorname{Polynomial}\left(\mathrm{Rat}\right), \operatorname{RatFunc}\left(\mathrm{Rat}\right)\right)\left(\operatorname{Polynomial}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\mathrm{Rat}\right), \operatorname{numerator}\left(m, n\right)\right)\right)}{\operatorname{algebraMap}\left(\operatorname{Polynomial}\left(\mathrm{Rat}\right), \operatorname{RatFunc}\left(\mathrm{Rat}\right)\right)\left(\operatorname{Polynomial}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\mathrm{Rat}\right), \operatorname{denominator}\left(m, n\right)\right)\right)} = \operatorname{algebraMap}\left(\operatorname{Polynomial}\left(\mathrm{Rat}\right), \operatorname{RatFunc}\left(\mathrm{Rat}\right)\right)\left(\operatorname{Polynomial}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\mathrm{Rat}\right), H\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality.claim` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A349272, COMMENT 2: even-step Fibonacci-polynomial integrality*. URL: <https://oeis.org/A349272/internal>.

*Commentary.*

OEIS A349272, COMMENT 2 (unpaginated): More generally, if F(n,x) denotes the n-th Fibonacci polynomial we conjecture that, for each n, the rational function Product_{k = 1..2*n+1} F(m*k,x) / Sum_{k = 1..2*n+1} F(m*k,x) is an integral polynomial. COMMENT 1 supplies the positive even step m, encoded by 2 <= m and Even m. Both m and n are natural numbers. The statement also requires a nonzero polynomial denominator. The coefficient map Int.castRingHom Rat followed by algebraMap embeds each integer polynomial into rational functions.

**Theorem 1.4 (The quotient has integer coefficients).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; 2 \le m \Rightarrow \left(\operatorname{Even}\left(m\right) \Rightarrow \left(\operatorname{denominator}\left(m, n\right) \ne 0 \land \left(\exists H \in \operatorname{Polynomial}\left(\mathrm{Int}\right),\; \frac{\operatorname{algebraMap}\left(\operatorname{Polynomial}\left(\mathrm{Rat}\right), \operatorname{RatFunc}\left(\mathrm{Rat}\right)\right)\left(\operatorname{Polynomial}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\mathrm{Rat}\right), \operatorname{numerator}\left(m, n\right)\right)\right)}{\operatorname{algebraMap}\left(\operatorname{Polynomial}\left(\mathrm{Rat}\right), \operatorname{RatFunc}\left(\mathrm{Rat}\right)\right)\left(\operatorname{Polynomial}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\mathrm{Rat}\right), \operatorname{denominator}\left(m, n\right)\right)\right)} = \operatorname{algebraMap}\left(\operatorname{Polynomial}\left(\mathrm{Rat}\right), \operatorname{RatFunc}\left(\mathrm{Rat}\right)\right)\left(\operatorname{Polynomial}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\mathrm{Rat}\right), H\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A349272, COMMENT 2: even-step Fibonacci-polynomial integrality*. URL: <https://oeis.org/A349272/internal>.

*Commentary.*

Even m makes the m-th power of the Fibonacci companion matrix have determinant one. Its trace t identifies the sampled polynomials as c*lucasU(t,1,k), where c is the m-th Fibonacci polynomial. The odd partial sum factors as lucasU(t,1,n+1)*(lucasU(t,1,n+1)+lucasU(t,1,n)). The doubling identity factors the last numerator term as a difference of squares. For n>0, take the integer polynomial c^(2*n)*(lucasU(t,1,n+1)-lucasU(t,1,n)) times the product of lucasU(t,1,k) over 1 <= k <= 2*n, excluding n+1. For n=0 take 1. This gives denominator*H=numerator without cancellation, over every commutative ring. The last summand has uniquely greatest degree and coefficient one for m>=2. Thus the denominator is nonzero and the multiplication identity gives the rational-function equality.

## References

- Truth anchor: `D5/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality.claim`
- Truth anchor: `D5/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality.denominator`
- Truth anchor: `D5/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality.numerator`
- Truth anchor: `D5/S3/ArithSums/BalaEvenStepFibonacciPolynomialIntegrality.result`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S1/Recurrence/LucasCompanion](../../S1/Recurrence/LucasCompanion.md)
- Dependency: [D5/S1/Recurrence/LucasEvenDescent](../../S1/Recurrence/LucasEvenDescent.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients](../Arith/Primes/FibonacciRecurrencePolynomialCoefficients.md)
