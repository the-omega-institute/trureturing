# Unit Shift Norm Budget

## Abstract

Actual coordinate normalization imposes a cubic shift cost and joint growth budgets.

Write phi=(1+sqrt(5))/2, psi=1-phi, q(a,b)=2a+3b, and Q(a,b)=a^2+ab-b^2. For natural j and g, put A=F(j-1), B=F(j), where F is the Fibonacci sequence. The source quantity is N=gq(A,B)+1. The integer r shifts the composition after absorbing its unit bit. The two real embeddings and the golden norm are those of the golden integer ring.

**Definition 1.1 (The actual shift).**

$$\operatorname{y}\left(j, g, r\right)=(gA+3r-1,gB+1-2r)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.shiftedComposition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shifted golden integer has coordinates gA+3r-1 and gB+1-2r. Its quantity is N for every integer shift.

**Definition 1.2 (Source quantity).**

$$N=g(2A+3B)+1$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.sourceQuantity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unit bit contributes one to the multiplied Fibonacci composition quantity. For positive j, q(A,B)=F(j+3).

**Definition 1.3 (Primitive quantity).**

$$U=\frac{N}{d}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.primitiveQuantity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here d is the gcd of the absolute values of the two actual shifted coordinates. The normalized quantity U=N/d is defined by real division; the theorem ensures d is positive.

**Definition 1.4 (Primitive norm).**

$$D=\frac{\lvert\operatorname{Q}\left(y\right)\rvert}{d^{2}}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.primitiveNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized absolute norm divides the existing golden norm by d squared. It uses the same actual coordinate gcd as U.

**Theorem 1.5 (Cubic cost and joint budgets).**

$$(\forall j, g, r, (\operatorname{admissible}\left(j, g, r\right)) \implies ((D>\frac{N}{4(g^{2}+1)^{2}R^{3}}) \land (\forall alpha, beta, ((\operatorname{budget}\left(alpha, beta\right)) \land (\operatorname{growth}\left(j, g, r, alpha, beta\right))) \implies ((D>\frac{N^{1-4alpha-3beta}}{50}) \land (\frac{N^{1-2alpha-2beta}}{5} \le U))))) \land ((\forall alpha, beta, (\operatorname{budget}\left(alpha, beta\right)) \implies (\forall M, \exists T, \forall j, g, r, (((\operatorname{admissible}\left(j, g, r\right)) \land (\operatorname{growth}\left(j, g, r, alpha, beta\right))) \land (T \le N)) \implies (M \le U))) \land (\forall alpha, beta, (\operatorname{budget}\left(alpha, beta\right)) \implies (\forall omega, (0<omega<\frac{1}{2}) \implies (\exists T, \forall j, g, r, (((\operatorname{admissible}\left(j, g, r\right)) \land (\operatorname{growth}\left(j, g, r, alpha, beta\right))) \land (T \le N)) \implies (\operatorname{log}\left(\operatorname{log}\left(2+D\right)\right)>\operatorname{log}\left(\operatorname{log}\left(\operatorname{log}\left(U\right)\right)\right)^{omega})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every j>=3, g>=2, and integer r, assume -1<g(A+Bpsi)<phi-1 and both shifted coordinates are nonnegative. Then the first strict inequality in the display holds with R=1+abs(r). For every pair of nonnegative real exponents alpha and beta with 4alpha+3beta<1, the additional conditions g<=N^alpha and abs(r)<=N^beta give the two power inequalities uniformly over these sources and shifts. Moreover U tends uniformly to infinity: for each real M there is a threshold depending only on alpha, beta, and M above which every such U is at least M.

In the display, j and g range over natural numbers, r over integers, and alpha, beta, omega, M, T over real numbers. The predicate admissible(j,g,r) means j>=3, g>=2, -1<g(A+Bpsi)<phi-1, and both actual shifted coordinates are nonnegative. The predicate budget(alpha,beta) means alpha>=0, beta>=0, and 4alpha+3beta<1. The predicate growth(j,g,r,alpha,beta) means g<=N^alpha and abs(r)<=N^beta. N, U, D, and R=1+abs(r) always refer to the same quantified j,g,r.

The coordinate gcd divides P=r^2-3r+1+g^2(-1)^j. For g>=2 this polynomial never vanishes at an integer r: its even case is positive after completing a square; in its odd case a hypothetical zero would put an integer square strictly between (2g)^2 and (2g+1)^2. Consequently d<=(g^2+1)R^2.

The conjugate embedding of the actual shifted integer is w-phi+r(2phi+1), where w=g(A+Bpsi). The source interval gives its absolute value strictly greater than R/2. Nonnegative coordinates and phi>3/2 give the other embedding at least N/2. Their product therefore has absolute norm strictly greater than NR/4. Combining these bounds for the same shift proves the cubic cost. The estimates g^2+1<=5g^2/4 and R<=2N^beta yield the constants 50 and 5.

For each fixed 0<omega<1/2 there is a threshold T depending only on alpha, beta, and omega. Whenever N>=T and the same hypotheses hold, log(log(2+D)) is strictly larger than log(log(log(U)))^omega. The positive power lower bound on U ensures that these logarithms eventually lie in their positive domains. The gcd is at least one, so U<=N. A positive power lower bound on D makes its double logarithm grow at least as log(log(N)) plus a constant. The power of log(log(log(N))) is smaller than any fixed positive multiple of log(log(N)) eventually.

The interval condition is the only source-window hypothesis used here. The result does not assert that every pair j,g lies in that interval or that a nonnegative shifted composition is a canonical address.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.primitiveNorm`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.primitiveQuantity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.shiftedComposition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.sourceQuantity`
- Dependency: [D5/S1/Scale/Embedding](../../../S1/Scale/Embedding.md)
- Dependency: [D5/S1/Scale/Fibonacci](../../../S1/Scale/Fibonacci.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](GraftAffineClosure.md)
