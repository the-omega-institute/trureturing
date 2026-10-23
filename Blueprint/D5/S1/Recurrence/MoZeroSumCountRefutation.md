# A Counterexample to the Zero-Sum Count Characterization

## Abstract

An alternating positive integer sequence has C-finite zero-sum counts for every finite integer digit set while its expanding characteristic roots have a ratio which is not a root of unity.

John C's MathOverflow question 516232, revision 2, proposes a characterization of constant-coefficient recurrences for exact zero-sum prefix counts. The statement concerns every positive integer recurrence sequence and every finite integer digit set. The counterexample below refutes that entire iff. Historical priority and complete earlier coverage remain UNKNOWN: the original full Frougny 1992 article has not been obtained. Standard bounded binary carries and finite automata are not claimed as new methods.

**Definition 1.1 (The alternating sequence).**

$$\forall k \in \mathbb{N},\; \operatorname{a}\left(2 \cdot k\right) = 4^{k + 1} \land \operatorname{a}\left(2 \cdot k + 1\right) = 2^{k + 1}$$

*Formalization.* `D5/S1/Recurrence/MoZeroSumCountRefutation.sequence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* John C (2026). *When does the zero-sum sign count satisfy a linear recurrence?, MathOverflow 516232 revision 2*. URL: <https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare>.

*Commentary.*

Lean index zero is source index one. Thus the source sequence has a(2k-1)=4^k and a(2k)=2^k for k at least one; its first terms are 4,2,16,4,64,8. Every term is positive. For every original index it satisfies a(n+4)=6a(n+2)-8a(n). The decreases at some indices are permitted by the source.

**Definition 1.2 (The minimal characteristic polynomial).**

$$P = \left(X^{2} - 4\right) \cdot \left(X^{2} - 2\right)$$

*Formalization.* `D5/S1/Recurrence/MoZeroSumCountRefutation.characteristic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* John C (2026). *When does the zero-sum sign count satisfy a linear recurrence?, MathOverflow 516232 revision 2*. URL: <https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare>.

*Commentary.*

The monic polynomial is X^4-6X^2+8. An annihilator of degree below four would give four linear equations from the first four shifts of the sequence. Their values 4,2,16,4,64,8,256 force all four possible coefficients to vanish. Hence no monic integer annihilator of smaller degree exists.

**Definition 1.3 (Annihilation in the forward shift).**

Lean statement: `D5/S1/Recurrence/MoZeroSumCountRefutation.Annihilates`

*Formalization.* `D5/S1/Recurrence/MoZeroSumCountRefutation.Annihilates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* John C (2026). *When does the zero-sum sign count satisfy a linear recurrence?, MathOverflow 516232 revision 2*. URL: <https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare>.

*Commentary.*

Annihilates(a,p) means that, for every natural n, the sum of p's coefficient at j times a(n+j), over p's support, is zero. Integer coefficients and the original sequence indices are retained.

**Definition 1.4 (The actual minimal integer recurrence).**

Lean statement: `D5/S1/Recurrence/MoZeroSumCountRefutation.MinimalCharacteristic`

*Formalization.* `D5/S1/Recurrence/MoZeroSumCountRefutation.MinimalCharacteristic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* John C (2026). *When does the zero-sum sign count satisfy a linear recurrence?, MathOverflow 516232 revision 2*. URL: <https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare>.

*Commentary.*

MinimalCharacteristic(a,p) requires p to be monic, to annihilate a at every index, and to have degree at most that of every other monic integer annihilator. These clauses include the original constant integer recurrence hypothesis; they do not postulate a candidate polynomial without proving its minimality.

**Definition 1.5 (Ordered original-coordinate assignments).**

Lean statement: `D5/S1/Recurrence/MoZeroSumCountRefutation.zeroAssignments`

*Formalization.* `D5/S1/Recurrence/MoZeroSumCountRefutation.zeroAssignments` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* John C (2026). *When does the zero-sum sign count satisfy a linear recurrence?, MathOverflow 516232 revision 2*. URL: <https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare>.

*Commentary.*

An assignment is a function from Fin(n) to the given finite integer set D whose sum of digit times the original sequence weight is zero. Two different original coordinates remain distinct even when their weights coincide. No set of possible digit sums replaces the ordered assignments.

**Definition 1.6 (Exact prefix counts).**

Lean statement: `D5/S1/Recurrence/MoZeroSumCountRefutation.sourceCount`

*Formalization.* `D5/S1/Recurrence/MoZeroSumCountRefutation.sourceCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* John C (2026). *When does the zero-sum sign count satisfy a linear recurrence?, MathOverflow 516232 revision 2*. URL: <https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare>.

*Commentary.*

sourceCount(a,D,n) is the cardinality of zeroAssignments(a,D,n). For positive n this is exactly the source count. Length zero has one empty assignment; its value is used only to simplify the finite state evolution and is removed by the explicit length-one shift in CountRecurrence.

**Definition 1.7 (The source recurrence convention).**

Lean statement: `D5/S1/Recurrence/MoZeroSumCountRefutation.CountRecurrence`

*Formalization.* `D5/S1/Recurrence/MoZeroSumCountRefutation.CountRecurrence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* John C (2026). *When does the zero-sum sign count satisfy a linear recurrence?, MathOverflow 516232 revision 2*. URL: <https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare>.

*Commentary.*

CountRecurrence(s) allows any positive order k, any complex coefficient vector, and any initial cutoff N; at every n at least N it asserts s(n+k+1)=sum c(i)s(n+i+1). Thus it imposes neither a coefficient restriction nor a common order for different digit sets. The proof constructs integer coefficients valid from length zero, casts them to the complex numbers, and applies the recurrence at n+1.

**Definition 1.8 (All three complex-root clauses).**

$$\forall P \in \operatorname{IntegerPolynomials}\left(\right),\; \operatorname{RootConditions}\left(P\right) \Leftrightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{Root}\left(P, z\right) \Rightarrow \left(\neg \operatorname{norm}\left(z\right) = 1\right)\right) \land \left(\left(\forall z \in \mathbb{C},\; \operatorname{Root}\left(P, z\right) \Rightarrow \left(1 < \operatorname{norm}\left(z\right) \Rightarrow \operatorname{rootMultiplicity}\left(P, z\right) = 1\right)\right) \land \left(\forall z \in \mathbb{C},\; \forall w \in \mathbb{C},\; \operatorname{Root}\left(P, z\right) \Rightarrow \left(\operatorname{Root}\left(P, w\right) \Rightarrow \left(1 < \operatorname{norm}\left(z\right) \Rightarrow \left(1 < \operatorname{norm}\left(w\right) \Rightarrow \left(\exists k \in \mathbb{N},\; 0 < k \land \frac{z}{w}^{k} = 1\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/MoZeroSumCountRefutation.RootConditions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* John C (2026). *When does the zero-sum sign count satisfy a linear recurrence?, MathOverflow 516232 revision 2*. URL: <https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare>.

*Commentary.*

The roots are complex roots of the integer polynomial after coefficient casting. The first clause excludes norm one. The second requires multiplicity one at every root of norm greater than one. The third quantifies over every pair of such roots and requires a positive integer power of their ratio to equal one.

**Definition 1.9 (The entire displayed iff).**

$$claim \Leftrightarrow \left(\forall a \in \operatorname{IntegerSequences}\left(\right),\; \forall P \in \operatorname{IntegerPolynomials}\left(\right),\; \left(\forall n \in \mathbb{N},\; 0 < \operatorname{a}\left(n\right)\right) \Rightarrow \left(\operatorname{MinimalCharacteristic}\left(a, P\right) \Rightarrow \left(\left(\forall D \in \operatorname{FiniteIntegerSets}\left(\right),\; \operatorname{CountRecurrence}\left(\operatorname{sourceCount}\left(a, D\right)\right)\right) \Leftrightarrow \operatorname{RootConditions}\left(P\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/MoZeroSumCountRefutation.claim` (`✓ std3`).

*Citation.* John C (2026). *When does the zero-sum sign count satisfy a linear recurrence?, MathOverflow 516232 revision 2*. URL: <https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare>.

*Commentary.*

The quantifiers include every integer-valued sequence with positive terms, its actual minimal characteristic polynomial, and every finite integer digit set. There is no increasing-sequence assumption, bounded alphabet, bounded order, selected prefix, or omitted root clause.

**Theorem 1.10 (The characterization is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MoZeroSumCountRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mo516232-zero-sum-count-characterization` (refuted) by `D5/S1/Recurrence/MoZeroSumCountRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mo516232-zero-sum-count-characterization","declaration_gid":"D5/S1/Recurrence/MoZeroSumCountRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* John C (2026). *When does the zero-sum sign count satisfy a linear recurrence?, MathOverflow 516232 revision 2*. URL: <https://mathoverflow.net/questions/516232/when-does-the-zero-sum-sign-count-s-nd-varepsilon-in-dn-sum-vare>.

*Commentary.*

Fix any finite integer D, including the empty set, and let M be the supremum of its digits' absolute values, with empty supremum zero. Carries range from -2M through 2M. The matrix T(m) counts ordered m-tuples of digits satisfying c+sum(d)=2c'. Only m=0,1,2 occurs. A zero assignment splits uniquely into its first local tuple and its suffix, with next carry equal to minus the suffix's binary value. The local digit bound proves that this integer carry remains in the stated interval. This bijection proves exact counting by matrix multiplication, with both endpoint carries zero.

At Lean coordinate i, the binary exponent after division of all weights by two is i+1 for even i and floor(i/2) for odd i. Each exponent fiber has at most two coordinates. Reindexing the original assignments by these fibers is a bijection and preserves their weighted sum. At exponent j its cardinality is the sum of the indicator that j is odd and the indicator that j is below floor(n/2). Missing exponents have cardinality zero and retain their T(0) factor.

Increasing the prefix length by four prepends multiplicities (1,2) and appends (0,1). Therefore the entire product Q(n) satisfies Q(n+4)=A Q(n) B, where A=T(1)T(2) and B=T(0)T(1). This identity holds for all n, including zero, and covers all four residue classes. Column vectorization turns it into v(n+4)=(transpose(B) tensor A)v(n), using mathlib's exact Kronecker identity.

The state consisting of v(n),v(n+1),v(n+2),v(n+3) advances by one fixed integer matrix W. Cayley-Hamilton gives a monic integer recurrence for every coordinate, including the zero-carry entry equal to the exact original count. Its positive order is the cardinality of the four-phase state space. The construction is uniform in D and proves the required recurrence at every source index.

The actual minimal polynomial has roots 2 and sqrt(2). Both have norm greater than one, and their ratio has norm greater than one. Its positive powers cannot equal one. Thus the universal-D count property holds for this sequence while the asserted conjunction of root conditions fails. This contradicts the only-if implication and refutes the entire iff. No replacement classification or historical originality claim is asserted.

## References

- Truth anchor: `D5/S1/Recurrence/MoZeroSumCountRefutation.Annihilates`
- Truth anchor: `D5/S1/Recurrence/MoZeroSumCountRefutation.CountRecurrence`
- Truth anchor: `D5/S1/Recurrence/MoZeroSumCountRefutation.MinimalCharacteristic`
- Truth anchor: `D5/S1/Recurrence/MoZeroSumCountRefutation.RootConditions`
- Truth anchor: `D5/S1/Recurrence/MoZeroSumCountRefutation.characteristic`
- Truth anchor: `D5/S1/Recurrence/MoZeroSumCountRefutation.claim`
- Truth anchor: `D5/S1/Recurrence/MoZeroSumCountRefutation.result`
- Truth anchor: `D5/S1/Recurrence/MoZeroSumCountRefutation.sequence`
- Truth anchor: `D5/S1/Recurrence/MoZeroSumCountRefutation.sourceCount`
- Truth anchor: `D5/S1/Recurrence/MoZeroSumCountRefutation.zeroAssignments`
