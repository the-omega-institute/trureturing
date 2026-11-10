# Pair-label patterns and their column classes

## Abstract

A fourteen-class transfer for proper four-row pair-label patterns.

A column has four labels in Fin 3. Two consecutive columns are compatible when labels at row distance at most one differ. Relabelling the three labels preserves compatibility. The fourteen first-appearance representatives are 0000, 0001, 0010, 0011, 0012, 0100, 0101, 0102, 0110, 0111, 0112, 0120, 0121 and 0122. The constant column has three relabellings; each other representative has six. A finite check counts all compatible successors in every class for every one of the 81 columns. TransferMatrix.cardMatrix propagates these equalities to arbitrary width.

**Definition 1.1 (Proper pair-label patterns).**

$$\forall (n: \operatorname{Nat}), (\forall (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Proper}\left(P\right) = (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(4\right)), (\forall (s: \operatorname{Fin}\left(4\right)), (((\operatorname{Fin}.\operatorname{val}\left(r\right) \le (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)) \land (\operatorname{Fin}.\operatorname{val}\left(s\right) \le (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1))) \Rightarrow (P\left((r, j)\right) \ne P\left((s, \operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right))\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Proper pair-label patterns.

**Definition 1.2 (Literal pair-pattern count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Proper}\left(P\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal pair-pattern count.

**Theorem 1.3 (Eight initial pair-pattern counts).**

$$\forall (k: \operatorname{Fin}\left(8\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((\operatorname{Fin}.\operatorname{val}\left(k\right)) + (2)\right): \operatorname{Int}) = (![162, 1122, 5808, 33702, 186720, 1054446, 5907444, 33206862]: \operatorname{Fin}\left(8\right) \to \operatorname{Int})\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.initial_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eight initial pair-pattern counts.

**Theorem 1.4 (The constant-adjusted pair-pattern recurrence).**

$$\forall (n: \operatorname{Nat}), (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (10)\right): \operatorname{Int})) + (6) = (((((((4) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (9)\right): \operatorname{Int})) + (6))) + ((13) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (8)\right): \operatorname{Int})) + (6)))) - ((19) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (7)\right): \operatorname{Int})) + (6)))) - ((22) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (6)\right): \operatorname{Int})) + (6)))) + ((27) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (5)\right): \operatorname{Int})) + (6)))) + ((2) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (4)\right): \operatorname{Int})) + (6)))) - ((4) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (3)\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant-adjusted pair-pattern recurrence.

The continuation vectors satisfy the sextic x^6-3*x^5-16*x^4+3*x^3+25*x^2-2*x-4 after one transition. TransferMatrix.tabulatedPowers verifies the first eight vectors and TransferMatrix.scalarRelationShift propagates the finite relation. Subtracting consecutive sextic relations multiplies by x-1 and also annihilates the constant six.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.L`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.initial_values`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.recurrence`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
