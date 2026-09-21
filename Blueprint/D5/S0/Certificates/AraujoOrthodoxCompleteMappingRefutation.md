# Problem 15.5 on Complete Mappings of Orthodox Semigroups

## Abstract

A five-element orthodox semigroup with an idempotent full-ordering product has no complete mapping.

**Definition 1.1 (Orthodox semigroups).**

$$\forall S \in \mathrm{Type},\; (Semigroup\left(S\right)) \Rightarrow ((Orthodox\left(S\right)) \Leftrightarrow ((\forall x \in S,\; \exists y \in S,\; x \cdot y \cdot x = x) \land (\forall e \in S, f \in S,\; (e \cdot e = e) \Rightarrow ((f \cdot f = f) \Rightarrow ((e \cdot f) \cdot (e \cdot f) = e \cdot f)))))$$

*Formalization.* `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.Orthodox` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups*. DOI: [10.48550/arXiv.2608.25092](https://doi.org/10.48550/arXiv.2608.25092). URL: <https://arxiv.org/abs/2608.25092>.

*Commentary.*

In every display the antecedent Semigroup(S) renders Lean's typeclass binder [Semigroup S]. Regularity requires, for every x, an element y with x*y*x = x. The second conjunct says that the product of any two idempotents is idempotent, exactly the E-semigroup condition. Their conjunction is the paper's definition of orthodox.

**Definition 1.2 (Complete mappings).**

$$\forall S \in \mathrm{Type},\; (Semigroup\left(S\right)) \Rightarrow (\forall alpha \in S \to S,\; (CompleteMapping\left(alpha\right)) \Leftrightarrow ((Bijective\left(alpha\right)) \land (Bijective\left(\lambda x, x \cdot alpha\left(x\right)\right))))$$

*Formalization.* `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.CompleteMapping` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups*. DOI: [10.48550/arXiv.2608.25092](https://doi.org/10.48550/arXiv.2608.25092). URL: <https://arxiv.org/abs/2608.25092>.

*Commentary.*

The word Bijective in the display denotes Lean's Function.Bijective. Thus alpha and the product map x |-> x*alpha(x) must both be bijections, matching the definition in the abstract.

**Definition 1.3 (An ordering with idempotent product).**

$$\forall S \in \mathrm{Type},\; (Semigroup\left(S\right)) \Rightarrow ((IdempotentOrdering\left(S\right)) \Leftrightarrow (\exists c \in S, l \in List\left(S\right),\; (Nodup\left(cons\left(c, l\right)\right)) \land ((\forall x \in S,\; x \in cons\left(c, l\right)) \land (foldl\left(mul, c, l\right) \cdot foldl\left(mul, c, l\right) = foldl\left(mul, c, l\right)))))$$

*Formalization.* `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.IdempotentOrdering` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups*. DOI: [10.48550/arXiv.2608.25092](https://doi.org/10.48550/arXiv.2608.25092). URL: <https://arxiv.org/abs/2608.25092>.

*Commentary.*

Here cons(c,l) is Lean's list c :: l, Nodup excludes repeated elements, and the universal membership clause makes the list exhaustive. The expression foldl(mul,c,l) is l.foldl (dot * dot) c, so p is the left-associated product of the ordering. The final clause is p*p = p.

**Definition 1.4 (Problem 15.5 as a universal claim).**

$$(claim) \Leftrightarrow (\forall S \in \mathrm{Type},\; (Semigroup\left(S\right)) \Rightarrow ((Orthodox\left(S\right)) \Rightarrow ((IdempotentOrdering\left(S\right)) \Rightarrow (\exists alpha \in S \to S,\; CompleteMapping\left(alpha\right)))))$$

*Formalization.* `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.claim` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups*. DOI: [10.48550/arXiv.2608.25092](https://doi.org/10.48550/arXiv.2608.25092). URL: <https://arxiv.org/abs/2608.25092>.

*Commentary.*

The question is read universally over every type carrying a semigroup structure. An orthodox semigroup with an idempotent ordering product is asserted to admit a complete mapping.

**Theorem 1.5 (Problem 15.5 has a negative answer).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups*. DOI: [10.48550/arXiv.2608.25092](https://doi.org/10.48550/arXiv.2608.25092). URL: <https://arxiv.org/abs/2608.25092>.

*Commentary.*

The counterexample has elements w0, w1, w2, w3, w4 and multiplication rows [w0,w1,w2,w3,w4], [w1,w0,w2,w3,w4], [w2,w2,w2,w3,w4], [w3,w3,w3,w4,w2], and [w4,w4,w4,w2,w3]. It is associative and regular; its idempotents are w0 and w2 and are closed under multiplication. The ordering [w0,w1,w2,w3,w4] has product w2. Exhaustive kernel reduction checks all 3125 maps from the carrier to itself and finds no complete mapping. The semigroup has no absorbing zero.

## References

- Truth anchor: `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.CompleteMapping`
- Truth anchor: `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.IdempotentOrdering`
- Truth anchor: `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.Orthodox`
- Truth anchor: `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.claim`
- Truth anchor: `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.result`
