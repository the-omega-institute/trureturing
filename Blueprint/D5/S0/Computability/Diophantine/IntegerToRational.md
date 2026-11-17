# Conditional Integer-to-Rational Polynomial Reduction

## Abstract

A finite polynomial definition of the integers yields a joint-assignment solvability reduction.

**Theorem 1.1 (The finite joint-assignment reduction).**

$$\forall n \in N,\; \forall m \in N,\; \forall P \in \operatorname{IntegerPolynomial}\left(\operatorname{succ}\left(m\right)\right),\; \forall f \in \operatorname{IntegerPolynomial}\left(n\right),\; \operatorname{DefinesIntegers}\left(P\right) \Rightarrow ((\exists x \in \operatorname{FinRatVec}\left(\operatorname{mul}\left(n, \operatorname{succ}\left(m\right)\right)\right),\; \operatorname{evalCompiled}\left(P, f, x, zero\right)) \iff (\exists z \in \operatorname{FinIntVec}\left(n\right),\; \operatorname{evalInput}\left(f, z, zero\right)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Diophantine/IntegerToRational.solvability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an integer polynomial P in one input coordinate and m witness coordinates that existentially defines the integers inside the rationals. For an arbitrary input polynomial f in n integer variables, the compiler uses n disjoint blocks of m+1 rational coordinates. The first coordinate of each block is the corresponding input variable; the remaining m coordinates are that variable's defining witnesses. DefinesIntegers P means: for every rational q, there exist m rational witnesses w with P(q,w)=0 if and only if there exists an integer z whose rational cast equals q. No integrality condition is imposed on the witnesses.

The output is one integer-coefficient polynomial: the square of f on the first coordinates plus the sum of the squares of the n translated copies of P. Every equation is evaluated under one joint assignment. A zero sum of rational squares forces every summand to vanish, giving soundness; an integer zero of f and one defining witness block per coordinate give completeness. The proof includes n=0, constant and zero inputs, signs and all finite dimensions.

This is conditional. It neither constructs the defining polynomial P nor proves integer Hilbert-tenth undecidability. The semantic compiler is formalized here. The companion effective theorem fixes a total raw Nat code, proves code completeness, and supplies a primitive-recursive compiler whose decoded output is this same semantic compiler. The implication is classical; the finite code construction below is an explicit realization. The entire integrality clause of ZInQ.FrozenTarget is an admissible premise; its degree and coefficient bounds are not needed.

**Theorem 1.2 (Primitive recursiveness at the fixed raw coding).**

$$\operatorname{Primrec}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Diophantine/IntegerToRational.compileCodeNat_primrec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K is the uncurried map compileCodeNat on the right-associated natural tuple (n,m,p,f). It returns (n*(m+1),k), where k encodes the compiled polynomial. Both dimensions vary uniformly. The proof composes Mathlib's primitive-recursive natural arithmetic, bounded comparison, canonical decoding and encoding, list map, concatenation, flatMap and range operations. The claim uses Mathlib.Primrec, with its natural-number encoding semantics.

**Theorem 1.3 (The total primitive-recursive code compiler).**

$$\operatorname{Computable}\left(K\right) \land (\forall n \in N,\; \forall f \in \operatorname{IntegerPolynomial}\left(n\right),\; \exists k \in N,\; \operatorname{D}\left(n, k\right) = f) \land (\forall n \in N,\; \forall m \in N,\; \forall p \in N,\; \forall f \in N,\; \operatorname{DefinesIntegers}\left(\operatorname{D}\left(\operatorname{succ}\left(m\right), p\right)\right) \Rightarrow ((\exists x \in \operatorname{FinRatVec}\left(\operatorname{mul}\left(n, \operatorname{succ}\left(m\right)\right)\right),\; \operatorname{evalRat}\left(\operatorname{D}\left(\operatorname{mul}\left(n, \operatorname{succ}\left(m\right)\right), \operatorname{snd}\left(\operatorname{K}\left(n, m, p, f\right)\right)\right), x\right) = 0) \iff (\exists z \in \operatorname{FinIntVec}\left(n\right),\; \operatorname{evalInt}\left(\operatorname{D}\left(n, f\right), z\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Diophantine/IntegerToRational.effective_compiler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial codes are finite lists of signed-coefficient monomials. A coefficient is a difference of naturals and a variable word uses natural indices; an index outside the declared finite dimension is interpreted as zero. A term ((a,b),[k,...]) decodes to the constant a-b times the product of those variables. Repeated indices give powers; the empty product is one and the empty term list is zero. Raw Nat codes use the pinned Mathlib Encodable product/list numbering; a failed decode returns the empty code. Every signed coefficient and every finite MvPolynomial, including dimension zero, is represented.

Coordinate j of block i has index j+(m+1)*i. Input variables are renamed to (m+1)*i, and each copy of P is renamed to its own block. Invalid source indices are sent to the output dimension, so they still denote zero. Code multiplication distributes terms and concatenates variable words; the compiler squares the renamed input and adds the n squared row codes. Polynomial induction proves completeness. decode_compileCode proves that this code operation decodes to the semantic sum of squares.

The compiler takes both dimensions and both raw codes as inputs. Its natural/list operations are proved primitive recursive, every finite MvPolynomial has a code, and the decoded result has the same rational solvability equivalence as the semantic joint-assignment reduction. In the formula, K denotes the uncurried map compileCodeNat on the right-associated tuple (n,m,p,f), returning the output dimension and raw polynomial code. D(n,k) denotes decodePolynomial n (decodeCode k), and snd selects the output code. The theorem compileCodeNat_primrec proves the stronger primitive-recursive property; effective_compiler combines its computability consequence with completeness and solvability.

## References

- Truth anchor: `D5/S0/Computability/Diophantine/IntegerToRational.compileCodeNat_primrec`
- Truth anchor: `D5/S0/Computability/Diophantine/IntegerToRational.effective_compiler`
- Truth anchor: `D5/S0/Computability/Diophantine/IntegerToRational.solvability`
