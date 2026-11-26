# Complementary exclusion on two columns

## Abstract

Barker's generating function for normalized six-colour two-column arrays.

**Definition 1.1 (Literal legality).**

$$\forall n: Nat, (\forall A: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)) \to \operatorname{Fin}\left(6\right), (\operatorname{Legal}\left(A\right) \iff ((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin.val}\left(i\right) = 0) \land (A\left((i, 0)\right) = 0))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\operatorname{Fin.val}\left(A\left((i, 0)\right)\right) + \operatorname{Fin.val}\left(A\left((i, 1)\right)\right) \neq 5)) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall h: \operatorname{Fin.val}\left(i\right) + 1 < n, ((\operatorname{Fin.val}\left(A\left((i, 0)\right)\right) + \operatorname{Fin.val}\left(A\left((\operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(i\right) + 1, h\right), 0)\right)\right) \neq 5) \land ((\operatorname{Fin.val}\left(A\left((i, 1)\right)\right) + \operatorname{Fin.val}\left(A\left((\operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(i\right) + 1, h\right), 1)\right)\right) \neq 5) \land (\operatorname{Fin.val}\left(A\left((i, 1)\right)\right) + \operatorname{Fin.val}\left(A\left((\operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(i\right) + 1, h\right), 0)\right)\right) \neq 5))))) \land (\forall p: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)), ((((A\left(p\right) = 2) \lor ((A\left(p\right) = 3) \lor (A\left(p\right) = 4))) \implies (\exists q: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)), ((2 \cdot \operatorname{Fin.val}\left(\operatorname{Prod.fst}\left(q\right)\right) + \operatorname{Fin.val}\left(\operatorname{Prod.snd}\left(q\right)\right) < 2 \cdot \operatorname{Fin.val}\left(\operatorname{Prod.fst}\left(p\right)\right) + \operatorname{Fin.val}\left(\operatorname{Prod.snd}\left(p\right)\right)) \land (A\left(q\right) = 1)))) \land ((A\left(p\right) = 3) \implies (\exists q: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)), ((2 \cdot \operatorname{Fin.val}\left(\operatorname{Prod.fst}\left(q\right)\right) + \operatorname{Fin.val}\left(\operatorname{Prod.snd}\left(q\right)\right) < 2 \cdot \operatorname{Fin.val}\left(\operatorname{Prod.fst}\left(p\right)\right) + \operatorname{Fin.val}\left(\operatorname{Prod.snd}\left(p\right)\right)) \land (A\left(q\right) = 2)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141.Legal` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233141: complementary exclusion on a six-colour two-column strip*. URL: <https://oeis.org/A233141>.

*Commentary.*

All entries are in 0 through 5. A bond forbids precisely a sum of five, so equal adjacent colours are permitted. The constrained edges are horizontal, vertical, and antidiagonal from the right cell of one row to the left cell of the next. The first cell must exist and equal zero. Every occurrence of 2, 3 or 4 has a strictly earlier 1, and every 3 has a strictly earlier 2, using the rank 2i+j.

**Definition 1.2 (Deciding literal legality).**

$$\forall n: Nat, (\forall A: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)) \to \operatorname{Fin}\left(6\right), ((\operatorname{instDecidableLegal}\left(A\right): \operatorname{Decidable}\left(\operatorname{Legal}\left(A\right)\right)) = \operatorname{inferInstanceAs}\left(\operatorname{Decidable}\left(((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin.val}\left(i\right) = 0) \land (A\left((i, 0)\right) = 0))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\operatorname{Fin.val}\left(A\left((i, 0)\right)\right) + \operatorname{Fin.val}\left(A\left((i, 1)\right)\right) \neq 5)) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall h: \operatorname{Fin.val}\left(i\right) + 1 < n, ((\operatorname{Fin.val}\left(A\left((i, 0)\right)\right) + \operatorname{Fin.val}\left(A\left((\operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(i\right) + 1, h\right), 0)\right)\right) \neq 5) \land ((\operatorname{Fin.val}\left(A\left((i, 1)\right)\right) + \operatorname{Fin.val}\left(A\left((\operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(i\right) + 1, h\right), 1)\right)\right) \neq 5) \land (\operatorname{Fin.val}\left(A\left((i, 1)\right)\right) + \operatorname{Fin.val}\left(A\left((\operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(i\right) + 1, h\right), 0)\right)\right) \neq 5))))) \land (\forall p: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)), ((((A\left(p\right) = 2) \lor ((A\left(p\right) = 3) \lor (A\left(p\right) = 4))) \implies (\exists q: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)), ((2 \cdot \operatorname{Fin.val}\left(\operatorname{Prod.fst}\left(q\right)\right) + \operatorname{Fin.val}\left(\operatorname{Prod.snd}\left(q\right)\right) < 2 \cdot \operatorname{Fin.val}\left(\operatorname{Prod.fst}\left(p\right)\right) + \operatorname{Fin.val}\left(\operatorname{Prod.snd}\left(p\right)\right)) \land (A\left(q\right) = 1)))) \land ((A\left(p\right) = 3) \implies (\exists q: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)), ((2 \cdot \operatorname{Fin.val}\left(\operatorname{Prod.fst}\left(q\right)\right) + \operatorname{Fin.val}\left(\operatorname{Prod.snd}\left(q\right)\right) < 2 \cdot \operatorname{Fin.val}\left(\operatorname{Prod.fst}\left(p\right)\right) + \operatorname{Fin.val}\left(\operatorname{Prod.snd}\left(p\right)\right)) \land (A\left(q\right) = 2)))))))))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141.instDecidableLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233141: complementary exclusion on a six-colour two-column strip*. URL: <https://oeis.org/A233141>.

*Commentary.*

The deciding instance combines the four finite clauses in the legality predicate.

**Definition 1.3 (Filtered array count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda A: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)) \to \operatorname{Fin}\left(6\right) \mapsto \operatorname{Legal}\left(A\right), \operatorname{Finset.univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233141: complementary exclusion on a six-colour two-column strip*. URL: <https://oeis.org/A233141>.

*Commentary.*

Every function on the indicated finite cell domain is included in the filter's universe. The anchor fails at height zero, giving a(0)=0.

**Theorem 1.4 (Barker's complete generating function).**

$$\operatorname{PowerSeries.mk}\left(\lambda n: Nat \mapsto (\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda A: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)) \to \operatorname{Fin}\left(6\right) \mapsto \operatorname{Legal}\left(A\right), \operatorname{Finset.univ}\right)\right): Rat)\right) = X \cdot \left(2 - 34 \cdot X + 93 \cdot X^{2} - 22 \cdot X^{3} + X^{4}\right) \cdot (\left(1 - X\right) \cdot \left(1 - 18 \cdot X + X^{2}\right) \cdot \left(1 - 6 \cdot X + X^{2}\right))^{-1} \operatorname{in} \operatorname{PowerSeries}\left(Rat\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233141: complementary exclusion on a six-colour two-column strip*. URL: <https://oeis.org/A233141>.

*Commentary.*

The width_counting_bridge of HardinA233251TriangleStrip identifies the literal count with the continuation transfer for width two. The two first-use flags and two row colours give 144 states. The integer transfer matrix has an entry one exactly when a legal next row updates the flags and row colours to the destination state, and zero otherwise.

The six certified continuation vectors establish a degree-five relation after one transfer step on every state. TransferMatrix.scalarRelationShift propagates it to all subsequent continuations. The first six positive counts are 2, 16, 225, 3727, 65120 and 1158334. The recurrence for index at least six has signed coefficients 25, -134, 134, -25, 1 in decreasing lag order. Coefficient comparison, including index zero, gives the polynomial product identity. The denominator has constant coefficient one, allowing its inverse in the rational formal power series ring.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141.instDecidableLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](../HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../TransferMatrix.md)
