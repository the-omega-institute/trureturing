# Conditional Integer-to-Rational Polynomial Reduction

## Abstract

A finite polynomial definition of the integers yields a joint-assignment solvability reduction.

**Theorem 1.1 (The finite joint-assignment reduction).**

$$\forall n \in N,\; \forall m \in N,\; \forall P \in \operatorname{IntegerPolynomial}\left(\operatorname{succ}\left(m\right)\right),\; \forall f \in \operatorname{IntegerPolynomial}\left(n\right),\; \operatorname{DefinesIntegers}\left(P\right) \Rightarrow (\exists x \in \operatorname{FinRatVec}\left(\operatorname{mul}\left(n, \operatorname{succ}\left(m\right)\right)\right),\; \operatorname{evalCompiled}\left(P, f, x, zero\right)) \iff (\exists z \in \operatorname{FinIntVec}\left(n\right),\; \operatorname{evalInput}\left(f, z, zero\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Diophantine/IntegerToRational.solvability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an integer polynomial P in one input coordinate and m witness coordinates that existentially defines the integers inside the rationals. For an arbitrary input polynomial f in n integer variables, the compiler uses n disjoint blocks of m+1 rational coordinates. The first coordinate of each block is the corresponding input variable; the remaining m coordinates are that variable's defining witnesses.

The output is one integer-coefficient polynomial: the square of f on the first coordinates plus the sum of the squares of the n translated copies of P. Every equation is evaluated under one joint assignment. A zero sum of rational squares forces every summand to vanish, giving soundness; an integer zero of f and one defining witness block per coordinate give completeness. The proof includes n=0, constant and zero inputs, signs and all finite dimensions.

This is conditional. It neither constructs the defining polynomial P nor proves integer Hilbert-tenth undecidability. The semantic compiler is formalized here; an explicit standard polynomial-code implementation and its compiled computability proof remain a separate downstream obligation before the full effective H10-END interface can be claimed.

## References

- Truth anchor: `D5/S0/Computability/Diophantine/IntegerToRational.solvability`
