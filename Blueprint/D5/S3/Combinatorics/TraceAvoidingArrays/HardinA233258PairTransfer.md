# Three-row pair patterns

## Abstract

The five-orbit transfer for three-row horizontal and antidiagonal pair patterns.

A column has three labels and no internal bond. Consecutive columns c,d satisfy c(r) != d(r) and d(r) != c(r+1) whenever r+1<3. The five first-appearance column representatives are 000, 001, 010, 011 and 012, with orbit sizes 3,6,6,6,6. Their successor matrix is [[2,2,2,2,0],[1,1,0,1,1],[1,1,0,0,0],[1,1,1,1,0],[0,0,0,1,1]]. After two columns, the weights are [24,24,12,24,12]. Thus L(n+2) is the weighted sum of the continuation vector Q^n*1. The vectors satisfy Q^5*1 = 2*Q^2*1 - 7*Q^3*1 + 6*Q^4*1. TransferMatrix.cardMatrix, tabulatedPowers and scalarRelationShift propagate these finite identities to all widths. The constant six satisfies the same cubic relation. The width-six identity is checked from the displayed initial counts.

**Definition 1.1 (Proper pair patterns).**

$$\forall (n: \operatorname{Nat}), (\forall (P: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{Proper}\left(P\right) = (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(3\right)), (\forall (s: \operatorname{Fin}\left(3\right)), (((r = s) \lor (\operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1))) \Rightarrow (P\left((r, j)\right) \ne P\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

Proper pair patterns.

**Definition 1.2 (Literal pair-pattern count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left(n\right) = (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (P: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{Proper}\left(P\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

Literal pair-pattern count.

**Theorem 1.3 (Six initial transfer counts).**

$$\forall (k: \operatorname{Fin}\left(6\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((\operatorname{Fin}.\operatorname{val}\left(k\right)) + (2)\right): \operatorname{Int}) = (![96, 432, 1944, 8856, 40392, 184248]: \operatorname{Fin}\left(6\right) \to \operatorname{Int})\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.initial_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

Six initial transfer counts.

**Theorem 1.4 (The constant-adjusted cubic relation).**

$$\forall (n: \operatorname{Nat}), (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((n) + (6)\right): \operatorname{Int})) + (6) = (((6) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((n) + (5)\right): \operatorname{Int})) + (6))) - ((7) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((n) + (4)\right): \operatorname{Int})) + (6)))) + ((2) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((n) + (3)\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

The constant-adjusted cubic relation.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.L`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.initial_values`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.recurrence`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
