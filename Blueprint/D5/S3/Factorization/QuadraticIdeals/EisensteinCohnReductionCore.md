# The Eisenstein Reduction for All Integer Powers

## Abstract

The square-plus-three equation has no integer solution with x at least two and exponent at least two.

**Theorem 1.1 (Square plus three is not a nontrivial integer power).**

$$\forall x, y \in \mathbb{Z}, \forall e \in \mathbb{N}, 2 \le x \Rightarrow 2 \le e \Rightarrow \neg x^{2} + 3 = y^{e}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/EisensteinCohnReductionCore.int_sq_add_three_not_pow` (`✓ std3`). ∎

*Citation.* J. H. E. Cohn (1993). *The Diophantine equation x^2+3=y^n*. DOI: [10.1017/S0017089500009757](https://doi.org/10.1017/S0017089500009757).

*Commentary.*

The base y ranges over all integers, and the natural exponent e has no upper bound. Cohn's classical positive-base argument supplies the three-adic obstruction; the formal reduction here also handles the square case and retains the signed base throughout.

Suppose x squared plus three equals y to the power e. If e is even, write e=2k. Then the square of the integer absolute value of y to the power k is strictly between x squared and (x+1) squared, since x is at least two. For odd e, choose a prime divisor q and set Y=y^(e/q). The equation becomes x squared plus three equals Y to the power q, with q odd. If x were odd, Y would be even and reduction modulo eight would give a contradiction. If three divided x, reduction modulo three would force three to divide Y, and reduction modulo nine would again contradict the equation. Thus x is even, three does not divide x, and x squared plus three is coprime to twelve.

Work in the Eisenstein integer ring with omega squared plus omega plus one equal to zero. Set alpha=(x+1)+2 omega and beta equal to its conjugate. Their product is x squared plus three, and minus the square of their difference is twelve. The integer Bezout identity for the norm and twelve therefore gives an explicit Bezout identity for alpha and beta. The existing cyclotomic equivalence transports the principal ideal ring structure, so Mathlib's coprime power extraction produces gamma to the power q times a unit epsilon equal to alpha.

The ring and its cyclotomic equivalence are supplied by `D5/S3/Factorization/QuadraticIdeals/EisensteinOddQuotient` and `D5/S3/Factorization/QuadraticIdeals/EisensteinCyclotomicBridge`.

Reduction modulo two sends alpha to one. For an element z of this quadratic algebra over the two-element field, z cubed is the scalar norm of z. When q=3 this forces epsilon to reduce to one. Its norm is one, so its imaginary coordinate is zero; the imaginary coordinate of gamma cubed times epsilon is then divisible by three, contradicting the coordinate two of alpha. For q different from three, q is coprime to six. The existing cyclotomic classification of the six units allows epsilon to be absorbed into a qth root delta. Modulo two, delta has both qth power and cube equal to one. Coprimality forces delta itself to reduce to one, so its imaginary coordinate is even.

The injective map from the integral suborder sends a+b sqrt(-3) to (a+b)+2b omega. The even imaginary coordinate pulls delta back through this map and gives an actual identity (a+b sqrt(-3))^q=x+sqrt(-3). Induction shows that b divides the imaginary coefficient of every power, hence b divides one and is plus or minus one. Taking norms and reducing modulo four and three shows that a is even and three does not divide a.

Put xi=a squared minus one and m=(q-1)/2. The owner polynomial is P_q(T), the sum from k=0 to m of binom(q,2k+1)(-3)^k(1+T)^(m-k). Its existing polynomial identification and evaluation hom give P_q(xi) as the imaginary coordinate of (a+sqrt(-3))^q. The sign b=plus or minus one yields P_q(xi)=plus or minus one. Modulo four, only the k=m term survives and has value one, forcing P_q(xi)=1. Modulo three, only k=0 survives and has value q, forcing q congruent to one modulo three. Together with odd q at least five, this gives q at least seven and q congruent to one modulo six; three also divides xi. The uniform Cohn obstruction now contradicts P_q(xi)=1.

The polynomial identity, evaluation hom, and final obstruction are reused from `D5/S3/Arith/Congruence/CohnUniformThreeAdic`. The reduction assumes neither an Eisenstein root nor coprimality: both are derived from the original equation.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/EisensteinCohnReductionCore.int_sq_add_three_not_pow`
- Dependency: [D5/S3/Arith/Congruence/CohnUniformThreeAdic](../../Arith/Congruence/CohnUniformThreeAdic.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/EisensteinCyclotomicBridge](EisensteinCyclotomicBridge.md)
- Narrative reference: [D5/S3/Arith/Congruence/CohnUniformThreeAdic](../../Arith/Congruence/CohnUniformThreeAdic.md)
- Narrative reference: [D5/S3/Factorization/QuadraticIdeals/EisensteinCyclotomicBridge](EisensteinCyclotomicBridge.md)
- Narrative reference: [D5/S3/Factorization/QuadraticIdeals/EisensteinOddQuotient](EisensteinOddQuotient.md)
