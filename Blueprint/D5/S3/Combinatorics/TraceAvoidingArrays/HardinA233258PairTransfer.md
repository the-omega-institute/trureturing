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

**Definition 1.3 (Three-label columns).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{Col}\left(\right) = (\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.Col` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

Three-label columns.

**Definition 1.4 (The five equality classes).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{Col}\left(\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{cls}\left(c\right) = ((\operatorname{if} \operatorname{Prod}.\operatorname{fst}\left(c\right) = \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right) \operatorname{then} (\operatorname{if} \operatorname{Prod}.\operatorname{fst}\left(c\right) = \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right) \operatorname{then} 0 \operatorname{else} 1) \operatorname{else} (\operatorname{if} \operatorname{Prod}.\operatorname{fst}\left(c\right) = \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right) \operatorname{then} 2 \operatorname{else} (\operatorname{if} \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right) = \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right) \operatorname{then} 3 \operatorname{else} 4))): \operatorname{Fin}\left(5\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.cls` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

The five equality classes.

**Definition 1.5 (The five-orbit successor matrix).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{Q}\left(\right) = ![![2, 2, 2, 2, 0], ![1, 1, 0, 1, 1], ![1, 1, 0, 0, 0], ![1, 1, 1, 1, 0], ![0, 0, 0, 1, 1]]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

The five-orbit successor matrix.

**Definition 1.6 (Two-column orbit multiplicities).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{weights}\left(\right) = ![24, 24, 12, 24, 12]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

Two-column orbit multiplicities.

**Theorem 1.7 (All labelled continuation counts).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((n) + (2)\right): \operatorname{Int}) = \operatorname{dotProduct}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{weights}\left(\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{Q}\left(\right)^{n}, (1: \operatorname{Fin}\left(5\right) \to \operatorname{Int})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.count_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

All labelled continuation counts.

**Definition 1.8 (Six continuation vectors).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{W}\left(\right) = ![![1, 1, 1, 1, 1], ![8, 4, 2, 4, 2], ![36, 18, 12, 18, 6], ![168, 78, 54, 84, 24], ![768, 354, 246, 384, 108], ![3504, 1614, 1122, 1752, 492]]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

Six continuation vectors.

**Theorem 1.9 (Certified continuation vectors).**

$$\forall (k: \operatorname{Fin}\left(6\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{Q}\left(\right)^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, (1: \operatorname{Fin}\left(5\right) \to \operatorname{Int})\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{W}\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.powers_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

Certified continuation vectors.

**Theorem 1.10 (Six initial transfer counts).**

$$\forall (k: \operatorname{Fin}\left(6\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((\operatorname{Fin}.\operatorname{val}\left(k\right)) + (2)\right): \operatorname{Int}) = (![96, 432, 1944, 8856, 40392, 184248]: \operatorname{Fin}\left(6\right) \to \operatorname{Int})\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.initial_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

Six initial transfer counts.

**Theorem 1.11 (The constant-adjusted cubic relation).**

$$\forall (n: \operatorname{Nat}), (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((n) + (6)\right): \operatorname{Int})) + (6) = (((6) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((n) + (5)\right): \operatorname{Int})) + (6))) - ((7) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((n) + (4)\right): \operatorname{Int})) + (6)))) + ((2) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left((n) + (3)\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

The constant-adjusted cubic relation.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.Col`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.L`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.Q`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.W`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.cls`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.count_transfer`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.initial_values`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.powers_table`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.recurrence`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.weights`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
