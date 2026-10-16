# Multinacci root location and irreducibility

## Abstract

The multinacci polynomial has a single simple root outside the open unit disc and is irreducible.

For every integer order q>=2, use the literal polynomial X^q-sum(i<q)X^i and the existing dbonacciPerronRoot(q) in (1,2). In the formulas, X(R) is the indeterminate over R and sumPowersBelow(X,q) is the finite sum of X^i over i<q; N,Z,Q,C denote the natural, integer, rational and complex number systems. This is a classical multinacci result associated with Alfred Brauer's paper On algebraic equations with all but one root in the interior of the unit circle, Mathematische Nachrichten 4, 250-257, DOI 10.1002/mana.3210040123. The proof here is independent of that paper's theorem text.

**Theorem 1.1 (Exact complex root location).**

$$\forall q \in N,\; 2 \le q \Rightarrow \left(\forall z \in C,\; \operatorname{IsRoot}\left(\operatorname{pow}\left(\operatorname{X}\left(C\right), q\right) - \operatorname{sumPowersBelow}\left(\operatorname{X}\left(C\right), q\right), z\right) \Rightarrow \left(1 \le \operatorname{norm}\left(z\right) \Leftrightarrow z = \operatorname{ofReal}\left(\operatorname{dbonacciPerronRoot}\left(q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Irreducibility.dbonacci_complex_root_location` (`✓ std3`). ∎

*Citation.* Alfred Brauer (1950). *On algebraic equations with all but one root in the interior of the unit circle*. DOI: [10.1002/mana.3210040123](https://doi.org/10.1002/mana.3210040123). URL: <https://doi.org/10.1002/mana.3210040123>.

*Commentary.*

For any complex root z with radius r>=1, the triangle inequality and the strictly decreasing reciprocal sum give r<=beta. The geometric-sum identity gives z^q(2-z)=1. Equality at r=1 forces z=1, contradicting q>=2. If 1<r<beta, the reciprocal inequality and geometric sum give r^q(2-r)>1, contrary to the reverse triangle inequality. Thus r=beta, and equality in that inequality forces z=r. The converse uses beta>1.

**Theorem 1.2 (The Perron root is simple).**

$$\forall q \in N,\; 2 \le q \Rightarrow \left(\operatorname{IsRoot}\left(\operatorname{pow}\left(\operatorname{X}\left(C\right), q\right) - \operatorname{sumPowersBelow}\left(\operatorname{X}\left(C\right), q\right), \operatorname{ofReal}\left(\operatorname{dbonacciPerronRoot}\left(q\right)\right)\right) \land \operatorname{eval}\left(\operatorname{derivative}\left(\operatorname{pow}\left(\operatorname{X}\left(C\right), q\right) - \operatorname{sumPowersBelow}\left(\operatorname{X}\left(C\right), q\right)\right), \operatorname{ofReal}\left(\operatorname{dbonacciPerronRoot}\left(q\right)\right)\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Irreducibility.dbonacciPerronRoot_simple` (`✓ std3`). ∎

*Citation.* Alfred Brauer (1950). *On algebraic equations with all but one root in the interior of the unit circle*. DOI: [10.1002/mana.3210040123](https://doi.org/10.1002/mana.3210040123). URL: <https://doi.org/10.1002/mana.3210040123>.

*Commentary.*

Euler's identity at a root gives beta*f'(beta)=sum(i<q)(q-i)beta^i. Every summand is nonnegative and the term i=0 is strictly positive. The formal derivative is therefore nonzero, without assuming irreducibility or squarefreeness.

**Theorem 1.3 (Integer and rational irreducibility).**

$$\forall q \in N,\; 2 \le q \Rightarrow \left(\operatorname{Irreducible}\left(\operatorname{pow}\left(\operatorname{X}\left(Z\right), q\right) - \operatorname{sumPowersBelow}\left(\operatorname{X}\left(Z\right), q\right)\right) \land \operatorname{Irreducible}\left(\operatorname{pow}\left(\operatorname{X}\left(Q\right), q\right) - \operatorname{sumPowersBelow}\left(\operatorname{X}\left(Q\right), q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Irreducibility.dbonacci_irreducible` (`✓ std3`). ∎

*Citation.* Alfred Brauer (1950). *On algebraic equations with all but one root in the interior of the unit circle*. DOI: [10.1002/mana.3210040123](https://doi.org/10.1002/mana.3210040123). URL: <https://doi.org/10.1002/mana.3210040123>.

*Commentary.*

A monic integer factorization has nonzero factor constants because their product is -1. Exactly one factor can vanish at beta: if both did, the product derivative would vanish. Every root of the other factor lies strictly inside the unit circle. If this complementary factor were nonconstant, its full complex root multiset, with multiplicities, would have product of norms below one. The monic constant-product formula would make its nonzero integer constant have absolute value below one, a contradiction. The complementary factor is one in either factor case. Monicity supplies primitivity, and Gauss's lemma transfers to Q. This irreducibility makes the actual integral Plus evaluation at beta faithful, which detects original finite-order scalar actions.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/Irreducibility.dbonacciPerronRoot_simple`
- Truth anchor: `D5/S0/Tower/DBonacci/Irreducibility.dbonacci_complex_root_location`
- Truth anchor: `D5/S0/Tower/DBonacci/Irreducibility.dbonacci_irreducible`
- Dependency: [D5/S0/Tower/DBonacci/PerronRoot](PerronRoot.md)
