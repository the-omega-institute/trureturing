# Equal parity in the first two values

## Abstract

The source permutation count in OEIS A152661 satisfies Mathar's first recurrence at every natural index at least four.

OEIS A152661 defines a(n) as the number of permutations of {1,...,n} whose first two entries have the same parity, for n at least two. Its first conjectural FORMULA, attributed to R. J. Mathar, is the recurrence below. The source is OEIS A152661, revision 23 (https://oeis.org/A152661). The entry's even and odd factorial-binomial formulas are prior formulas; the recurrence proof and its cardinality bridge are repository-derived. Parity here always means parity of a natural value, rather than parity in a finite ring.

**Definition 1.1 (The permutation count).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{if} 2 \le n \operatorname{then} (\operatorname{Natcard}\left(\{p:\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right) \mid (\operatorname{val}\left(p\left(0\right)\right) + 1) \bmod 2 = (\operatorname{val}\left(p\left(1\right)\right) + 1) \bmod 2\}\right):\mathbb{Z}) \operatorname{else} (0:\mathbb{Z})$$

*Formalization.* `D5/S3/Combinatorics/Permutation/MatharSameParityRecurrence.a` (`✓ std3`).

*Citation.* Emeric Deutsch; R. J. Mathar (2008). *OEIS A152661: permutations whose first two elements have the same parity*. URL: <https://oeis.org/A152661>.

*Commentary.*

A permutation p of Fin n represents the natural word with value p(i).val+1 in position i+1. For n at least two, a(n) is the integer cast of the cardinality of the permutations satisfying (p(0).val+1) mod 2 = (p(1).val+1) mod 2. Here Perm(Fin(n)) is the type of bijections Fin(n) to itself, Natcard is Nat.card of the displayed subtype, val takes the natural value of a Fin(n) element, and the annotation Z casts that natural cardinality to the integers. The numerals 0 and 1 in the guarded branch are the elements of Fin(n) with those natural values; the guard supplies their bounds. For the two indices below this domain, a(n) is defined to be integer zero.

**Theorem 1.2 (The integer recurrence).**

$$\forall n \in \mathbb{N},\; 4 \le n \Rightarrow ((3 - n) \cdot \operatorname{a}\left(n\right) + 2 \cdot (n - 2) \cdot \operatorname{a}\left(n - 1\right) + (n - 1) \cdot (n - 2) \cdot (n - 3) \cdot \operatorname{a}\left(n - 2\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/MatharSameParityRecurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emeric Deutsch; R. J. Mathar (2008). *OEIS A152661: permutations whose first two elements have the same parity*. URL: <https://oeis.org/A152661>.

*Commentary.*

There are e natural values of one parity and o of the other. An ordered distinct first pair therefore has e(e-1)+o(o-1) choices. Reading this pair decomposes the actual permutation subtype into disjoint completion fibers. Each fiber has (n-2)! elements by the finite partial-injection extension count. Consequently a(n) is [e(e-1)+o(o-1)](n-2)!; this is an equality with the source cardinality.

At n=2k+2 the pair count is 2k(k+1), and at n=2k+3 it is 2(k+1)^2. In particular a(2)=0 and a(4)=8. Substituting these two count formulas and the factorial successor identity proves the recurrence in both parity cases, including n=4. All coefficients and sequence values in the displayed equality are integers; the indices n-1 and n-2 are natural indices.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/MatharSameParityRecurrence.a`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MatharSameParityRecurrence.result`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphCounting](../EdgeLabeling/CubicARGraphCounting.md)
