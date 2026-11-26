# Nil semigroups of linear endomorphisms

## Abstract

Multiplicative closure turns pointwise nilpotence into joint extinction in finite dimension.

**Theorem 1.1 (A common annihilated vector).**

Lean statement: `D5/S1/Eigenstructure/NilSemigroup.exists_common_annihilator`

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/NilSemigroup.exists_common_annihilator` (`✓ std3`). ∎

*Citation.* Bamdad Reza Yahaghi (2002). *Reducibility Results on Operator Semigroups*. URL: <https://dal.scholaris.ca/bitstreams/d3c9f1ef-bef0-46d6-a7d1-03940bf895be/download>.

*Commentary.*

Let V be a nonzero finite-dimensional left vector space over a division ring K. Let S be any multiplicatively closed set of K-linear endomorphisms, each of which is nilpotent. Then there is a nonzero vector annihilated by every member of S. The family may be empty or infinite, and no identity or commutativity assumption is imposed.

If every member of S is zero, any nonzero vector is annihilated by the whole family; this also covers the empty family. Otherwise choose a nonzero member T with minimum positive rank. For each A in S, the range of TAT lies in the range of T. If TAT is nonzero, minimality forces equality of these ranges. The nilpotent operator TA would then map the nonzero range of T onto itself, a contradiction. Hence TAT vanishes for every A in S.

For a vector with Tx nonzero, consider the span of all ATx. This span is invariant under S and is killed by T. If it vanishes, Tx is the desired vector. Otherwise it is a nonzero proper invariant subspace, and induction on dimension supplies the vector inside it.

Yahaghi, Reducibility Results on Operator Semigroups, Chapter 4, Corollary 4.2.3, states Levitzki triangularization on printed page 108 and proves it on page 109; the chapter fixes finite-dimensional left vector spaces over division rings on page 105. The common-annihilator conclusion is a mathematical consequence of that classical theorem, not a verbatim statement of the corollary. The repository supplies an independent minimum-rank proof of this consequence.

**Theorem 1.2 (The dimension bounds all word lengths).**

Lean statement: `D5/S1/Eigenstructure/NilSemigroup.list_prod_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/NilSemigroup.list_prod_eq_zero` (`✓ std3`). ∎

*Citation.* Bamdad Reza Yahaghi (2002). *Reducibility Results on Operator Semigroups*. URL: <https://dal.scholaris.ca/bitstreams/d3c9f1ef-bef0-46d6-a7d1-03940bf895be/download>.

*Commentary.*

For the same nil semigroup S, every list of members of S whose length is at least the dimension of V has product zero. Multiplication is actual endomorphism composition: in a list A, B, C, the operator C acts first, followed by B and A. No bound on the individual nilpotence exponents is supplied.

In positive dimension, take a nonzero common annihilated vector and quotient by its one-dimensional span. The induced family remains multiplicatively closed and nil. By induction, the tail of a sufficiently long word has image in the annihilated line; its first factor kills that image. In dimension zero every endomorphism is zero, so the conclusion also covers the empty product, which is the identity.

The dimension bound is also a mathematical consequence of Levitzki triangularization as stated by Yahaghi in Corollary 4.2.3, not a verbatim statement in that source. The repository supplies an independent quotient-induction proof. No uniform nilpotence exponent is assumed.

## References

- Truth anchor: `D5/S1/Eigenstructure/NilSemigroup.exists_common_annihilator`
- Truth anchor: `D5/S1/Eigenstructure/NilSemigroup.list_prod_eq_zero`
