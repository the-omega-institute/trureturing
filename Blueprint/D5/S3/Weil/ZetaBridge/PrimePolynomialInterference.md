# Prime polynomial interference on a dyadic block

## Abstract

A coefficient-energy bound for signed polynomial interference with the actual finite prime symbol.

**Theorem 1.1 (The signed cross error is bounded independently of the block length).**

Lean statement: `D5/S3/Weil/ZetaBridge/PrimePolynomialInterference.prime_polynomial_interference_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimePolynomialInterference.prime_polynomial_interference_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c with 2 <= c, every natural d, every natural N with 0 < N, and every pair F,B of polynomials with complex coefficients such that F.natDegree < d and B.natDegree < d, the following inequality holds. The absolute value of the real sum, over all natural m in the inclusive interval [N+1,2*N], of primeSymbol(c,(m : Int)) times Re(F.eval((m : Complex)/(N : Complex)) * star(B.eval((m : Complex)/(N : Complex)))) is at most primeFirstMoment(c) times (sum over r in range(d) of (4 : Real)^r) times ((sum over r in range(d) of norm(F.coeff(r))^2) + (sum over r in range(d) of norm(B.coeff(r))^2)). The real absolute value is outside the signed sum; the second factor in the product of polynomial evaluations is complex conjugated.

Here primeSymbol is exactly PrimeSymbolMeanSquare.primeSymbol and primeFirstMoment is exactly ActualFullSymbolTail.primeFirstMoment. Write primeIndices(c)=Finset.Ico(2,c), theta(c,q)=Real.log((q : Real))/logLength(c), and primePhase(c,q)=circleMap(0,1,2*pi*theta(c,q)). The actual symbol is the finite sum over q in primeIndices(c) of primeWeight(q)*sin(2*pi*(m : Real)*theta(c,q)), and the first moment is the finite sum over the same q of 2*abs(primeWeight(q))/norm(1-primePhase(c,q)). Every prime power remains in these native finite sums. No prime-only replacement, large-c limit or averaging assumption occurs.

Put H=primeFirstMoment(c), x_j=primeSymbol(c,Int.ofNat(N+j+1)), and t_j=(N+j+1)/N in the reals. The public prime_first_moment_block with integer start Int.ofNat(N)+1 bounds the absolute value of every prefix sum of x by H. The proof derives H>=0 directly from its finite-sum definition. For each natural k the weights t_j^k are nonnegative and nondecreasing. Finset.sum_range_by_parts' expresses the weighted sum as the terminal prefix times t_(N-1)^k minus the sum of prefixes times successive weight differences. Those differences telescope. Thus the absolute weighted sum is at most H*(2*t_(N-1)^k-t_0^k), hence at most 2*H*2^k, since t_(N-1)=2.

Polynomial.eval_eq_sum_range' expands both evaluations exactly over range(d). Conjugation fixes real powers, so taking real parts gives coefficients Re(F.coeff(r)*star(B.coeff(s))) multiplying t_j^(r+s). Finite sums are interchanged before estimating the monomial sums. The inequality abs(Re(z))<=norm(z), multiplicativity of norm and invariance of norm under star give an upper bound 2*H*L(F)*L(B), where L(P)=sum over r<d of norm(P.coeff(r))*2^r.

Finite squared Cauchy-Schwarz gives L(P)^2 <= R_d*E(P), with R_d=sum over r<d of 4^r and E(P)=sum over r<d of norm(P.coeff(r))^2. The nonnegative square (L(F)-L(B))^2 gives 2*L(F)*L(B) <= L(F)^2+L(B)^2. Multiplication by H>=0 yields exactly H*R_d*(E(F)+E(B)). The proof uses no square-root interface. The inclusive interval [N+1,2*N] is converted to exactly range(N) using m=N+j+1.

The constant depends only on c and d, and the energy factors are homogeneous in the arbitrary complex coefficients. No polynomial-dependent cutoff, head normalization, nonvanishing coefficient or degree-exactness assumption is imposed. N=1, k=0, c=2 and either or both zero polynomials are included whenever the stated degree hypotheses hold; d=0 has no qualifying polynomials because natDegree is natural-valued. At c=2 the actual prime index set is empty. The intended consumer is the coefficient-uniform actual paired-tail estimate, where this theorem supplies the signed polynomial prime cross error independently of N. This theorem itself is a finite-block inequality and makes no paired-tail, full-symbol positivity, RH or novelty claim.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimePolynomialInterference.prime_polynomial_interference_bound`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualFullSymbolTail](ActualFullSymbolTail.md)
