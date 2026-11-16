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

This is conditional. It neither constructs the defining polynomial P nor proves integer Hilbert-tenth undecidability. The semantic compiler is formalized here. The companion effective theorem fixes a total raw Nat code, proves code completeness, and supplies a primitive-recursive compiler whose decoded output is this same semantic compiler.

**Theorem 1.2 (The total primitive-recursive code compiler).**

$$\operatorname{Computable}\left(K\right) \land (\forall n \in N,\; \forall f \in \operatorname{IntegerPolynomial}\left(n\right),\; \exists k \in N,\; \operatorname{D}\left(n, k\right) = f) \land (\forall n \in N,\; \forall m \in N,\; \forall p \in N,\; \forall f \in N,\; \operatorname{DefinesIntegers}\left(\operatorname{D}\left(\operatorname{succ}\left(m\right), p\right)\right) \Rightarrow (\exists x \in \operatorname{FinRatVec}\left(\operatorname{mul}\left(n, \operatorname{succ}\left(m\right)\right)\right),\; \operatorname{evalRat}\left(\operatorname{D}\left(\operatorname{mul}\left(n, \operatorname{succ}\left(m\right)\right), \operatorname{snd}\left(\operatorname{K}\left(n, m, p, f\right)\right)\right), x\right) = 0) \iff (\exists z \in \operatorname{FinIntVec}\left(n\right),\; \operatorname{evalInt}\left(\operatorname{D}\left(n, f\right), z\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Diophantine/IntegerToRational.effective_compiler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial codes are finite lists of signed-coefficient monomials. A coefficient is a difference of naturals and a variable word uses natural indices; an index outside the declared finite dimension is interpreted as zero. Raw Nat codes use Mathlib's Encodable numbering; malformed numerals decode to the empty code.

The compiler takes both dimensions and both raw codes as inputs. Its natural/list operations are proved primitive recursive, every finite MvPolynomial has a code, and the decoded result has the same rational solvability equivalence as the semantic joint-assignment reduction. In the formula, K denotes the uncurried map compileCodeNat on the right-associated tuple (n,m,p,f), returning the output dimension and raw polynomial code. D(n,k) denotes decodePolynomial n (decodeCode k), and snd selects the output code. The theorem compileCodeNat_primrec proves the stronger primitive-recursive property; effective_compiler combines its computability consequence with completeness and solvability.

## References

- Truth anchor: `D5/S0/Computability/Diophantine/IntegerToRational.effective_compiler`
- Truth anchor: `D5/S0/Computability/Diophantine/IntegerToRational.solvability`
