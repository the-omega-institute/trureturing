# Six-row column transfer

## Abstract

Proper pair-label patterns on a six-row ladder.

A column has six labels in Fin 3. Relabelling the palette gives 122 orbits of the 729 columns. Fifty orbits have compatible successors. The remaining orbits have no successors and are combined into one zero state, giving a transfer matrix with 51 states. Compatibility only compares rows at distance at most one across consecutive columns.

**Definition 1.1 (Proper pair-label patterns).**

$$\forall (n: \operatorname{Nat}), (\forall (P: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{Proper}\left(P\right) = (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(6\right)), (\forall (s: \operatorname{Fin}\left(6\right)), (((\operatorname{Fin}.\operatorname{val}\left(r\right) \le (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)) \land (\operatorname{Fin}.\operatorname{val}\left(s\right) \le (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1))) \Rightarrow (P\left((r, j)\right) \ne P\left((s, \operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right))\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

Proper pair-label patterns.

**Definition 1.2 (The literal pair-label count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (P: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{Proper}\left(P\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

The literal pair-label count.

**Definition 1.3 (Six-label columns).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{Col}\left(\right) = (\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.Col` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

Six-label columns.

**Definition 1.4 (Column coordinates).**

$$\forall (c: (\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right))))))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{column}\left(c\right) = ![\operatorname{Prod}.\operatorname{fst}\left(c\right), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right)\right)])$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.column` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

Column coordinates.

**Definition 1.5 (Equality-pattern index).**

$$\forall (c: (\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right))))))), (\forall (i: \operatorname{Fin}\left(122\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{orbit}\left(c\right) = i) \Leftrightarrow (\forall (r: \operatorname{Fin}\left(6\right)), (\forall (s: \operatorname{Fin}\left(6\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{column}\left(c, r\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{column}\left(c, s\right)) \Leftrightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{column}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{representatives}\left(i\right), r\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{column}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{representatives}\left(i\right), s\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.orbit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

Equality-pattern index.

The displayed formula is the equality-pattern property computed by the 122-leaf case split that defines orbit. The property is confirmed by evaluating that case split on all 729 columns and is not proved as a separate theorem here; its forward direction is the content of class_rep.

**Definition 1.6 (The 122 equality-pattern representatives).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{representatives}\left(\right) = ![(0, (0, (0, (0, (0, 0))))), (0, (0, (0, (0, (0, 1))))), (0, (0, (0, (0, (1, 0))))), (0, (0, (0, (0, (1, 1))))), (0, (0, (0, (0, (1, 2))))), (0, (0, (0, (1, (0, 0))))), (0, (0, (0, (1, (0, 1))))), (0, (0, (0, (1, (0, 2))))), (0, (0, (0, (1, (1, 0))))), (0, (0, (0, (1, (1, 1))))), (0, (0, (0, (1, (1, 2))))), (0, (0, (0, (1, (2, 0))))), (0, (0, (0, (1, (2, 1))))), (0, (0, (0, (1, (2, 2))))), (0, (0, (1, (0, (0, 0))))), (0, (0, (1, (0, (0, 1))))), (0, (0, (1, (0, (0, 2))))), (0, (0, (1, (0, (1, 0))))), (0, (0, (1, (0, (1, 1))))), (0, (0, (1, (0, (1, 2))))), (0, (0, (1, (0, (2, 0))))), (0, (0, (1, (0, (2, 1))))), (0, (0, (1, (0, (2, 2))))), (0, (0, (1, (1, (0, 0))))), (0, (0, (1, (1, (0, 1))))), (0, (0, (1, (1, (0, 2))))), (0, (0, (1, (1, (1, 0))))), (0, (0, (1, (1, (1, 1))))), (0, (0, (1, (1, (1, 2))))), (0, (0, (1, (1, (2, 0))))), (0, (0, (1, (1, (2, 1))))), (0, (0, (1, (1, (2, 2))))), (0, (0, (1, (2, (0, 0))))), (0, (0, (1, (2, (0, 1))))), (0, (0, (1, (2, (0, 2))))), (0, (0, (1, (2, (1, 0))))), (0, (0, (1, (2, (1, 1))))), (0, (0, (1, (2, (1, 2))))), (0, (0, (1, (2, (2, 0))))), (0, (0, (1, (2, (2, 1))))), (0, (0, (1, (2, (2, 2))))), (0, (1, (0, (0, (0, 0))))), (0, (1, (0, (0, (0, 1))))), (0, (1, (0, (0, (0, 2))))), (0, (1, (0, (0, (1, 0))))), (0, (1, (0, (0, (1, 1))))), (0, (1, (0, (0, (1, 2))))), (0, (1, (0, (0, (2, 0))))), (0, (1, (0, (0, (2, 1))))), (0, (1, (0, (0, (2, 2))))), (0, (1, (0, (1, (0, 0))))), (0, (1, (0, (1, (0, 1))))), (0, (1, (0, (1, (0, 2))))), (0, (1, (0, (1, (1, 0))))), (0, (1, (0, (1, (1, 1))))), (0, (1, (0, (1, (1, 2))))), (0, (1, (0, (1, (2, 0))))), (0, (1, (0, (1, (2, 1))))), (0, (1, (0, (1, (2, 2))))), (0, (1, (0, (2, (0, 0))))), (0, (1, (0, (2, (0, 1))))), (0, (1, (0, (2, (0, 2))))), (0, (1, (0, (2, (1, 0))))), (0, (1, (0, (2, (1, 1))))), (0, (1, (0, (2, (1, 2))))), (0, (1, (0, (2, (2, 0))))), (0, (1, (0, (2, (2, 1))))), (0, (1, (0, (2, (2, 2))))), (0, (1, (1, (0, (0, 0))))), (0, (1, (1, (0, (0, 1))))), (0, (1, (1, (0, (0, 2))))), (0, (1, (1, (0, (1, 0))))), (0, (1, (1, (0, (1, 1))))), (0, (1, (1, (0, (1, 2))))), (0, (1, (1, (0, (2, 0))))), (0, (1, (1, (0, (2, 1))))), (0, (1, (1, (0, (2, 2))))), (0, (1, (1, (1, (0, 0))))), (0, (1, (1, (1, (0, 1))))), (0, (1, (1, (1, (0, 2))))), (0, (1, (1, (1, (1, 0))))), (0, (1, (1, (1, (1, 1))))), (0, (1, (1, (1, (1, 2))))), (0, (1, (1, (1, (2, 0))))), (0, (1, (1, (1, (2, 1))))), (0, (1, (1, (1, (2, 2))))), (0, (1, (1, (2, (0, 0))))), (0, (1, (1, (2, (0, 1))))), (0, (1, (1, (2, (0, 2))))), (0, (1, (1, (2, (1, 0))))), (0, (1, (1, (2, (1, 1))))), (0, (1, (1, (2, (1, 2))))), (0, (1, (1, (2, (2, 0))))), (0, (1, (1, (2, (2, 1))))), (0, (1, (1, (2, (2, 2))))), (0, (1, (2, (0, (0, 0))))), (0, (1, (2, (0, (0, 1))))), (0, (1, (2, (0, (0, 2))))), (0, (1, (2, (0, (1, 0))))), (0, (1, (2, (0, (1, 1))))), (0, (1, (2, (0, (1, 2))))), (0, (1, (2, (0, (2, 0))))), (0, (1, (2, (0, (2, 1))))), (0, (1, (2, (0, (2, 2))))), (0, (1, (2, (1, (0, 0))))), (0, (1, (2, (1, (0, 1))))), (0, (1, (2, (1, (0, 2))))), (0, (1, (2, (1, (1, 0))))), (0, (1, (2, (1, (1, 1))))), (0, (1, (2, (1, (1, 2))))), (0, (1, (2, (1, (2, 0))))), (0, (1, (2, (1, (2, 1))))), (0, (1, (2, (1, (2, 2))))), (0, (1, (2, (2, (0, 0))))), (0, (1, (2, (2, (0, 1))))), (0, (1, (2, (2, (0, 2))))), (0, (1, (2, (2, (1, 0))))), (0, (1, (2, (2, (1, 1))))), (0, (1, (2, (2, (1, 2))))), (0, (1, (2, (2, (2, 0))))), (0, (1, (2, (2, (2, 1))))), (0, (1, (2, (2, (2, 2)))))]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

The 122 equality-pattern representatives.

**Definition 1.7 (Coordinatewise label permutations).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{relabel}\left(e\right) = \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, e\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

Coordinatewise label permutations.

**Theorem 1.8 (Every column has its indexed representative).**

$$\forall (c: (\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right))))))), (\exists e \in \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right),\; (e\left(\operatorname{Prod}.\operatorname{fst}\left(c\right)\right), (e\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right), (e\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right), (e\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right)\right), (e\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right)\right)\right), e\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right)\right)\right)))))) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{representatives}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{orbit}\left(c\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.class_rep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

Every column has its indexed representative.

**Theorem 1.9 (Initial pair-label counts).**

$$\forall (k: \operatorname{Fin}\left(26\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((\operatorname{Fin}.\operatorname{val}\left(k\right)) + (2)\right): \operatorname{Int}) = (![1458, 23346, 235824, 2986152, 33994188, 409408542, 4791504648, 56948232390, 671408641884, 7950212281224, 93923210426688, 1110971521842576, 13132515793768920, 155290791915166218, 1835954950424998884, 21708106678579996182, 256660237490505696204, 3034643594159596884672, 35879810376487028900160, 424224888649277811420648, 5015800426651629427544760, 59304188625218088516497046, 701180686835907546543927912, 8290387169164139913131170926, 98021089474277074253102673060, 1158948987790395127011466558572]: \operatorname{Fin}\left(26\right) \to \operatorname{Int})\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.initial_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

Initial pair-label counts.

**Theorem 1.10 (The shifted relation for L plus six).**

$$\forall (n: \operatorname{Nat}), (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (27)\right): \operatorname{Int})) + (6) = ((((((((((((((((((((((((7) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (26)\right): \operatorname{Int})) + (6))) + ((103) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (25)\right): \operatorname{Int})) + (6)))) - ((365) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (24)\right): \operatorname{Int})) + (6)))) - ((2896) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (23)\right): \operatorname{Int})) + (6)))) + ((7168) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (22)\right): \operatorname{Int})) + (6)))) + ((32291) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (21)\right): \operatorname{Int})) + (6)))) - ((75471) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (20)\right): \operatorname{Int})) + (6)))) - ((161805) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (19)\right): \operatorname{Int})) + (6)))) + ((426135) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (18)\right): \operatorname{Int})) + (6)))) + ((333692) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (17)\right): \operatorname{Int})) + (6)))) - ((1225001) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (16)\right): \operatorname{Int})) + (6)))) - ((155206) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (15)\right): \operatorname{Int})) + (6)))) + ((1850161) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (14)\right): \operatorname{Int})) + (6)))) - ((363389) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (13)\right): \operatorname{Int})) + (6)))) - ((1524689) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (12)\right): \operatorname{Int})) + (6)))) + ((557502) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (11)\right): \operatorname{Int})) + (6)))) + ((690388) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (10)\right): \operatorname{Int})) + (6)))) - ((312941) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (9)\right): \operatorname{Int})) + (6)))) - ((166928) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (8)\right): \operatorname{Int})) + (6)))) + ((81406) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (7)\right): \operatorname{Int})) + (6)))) + ((19997) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (6)\right): \operatorname{Int})) + (6)))) - ((9672) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (5)\right): \operatorname{Int})) + (6)))) - ((906) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (4)\right): \operatorname{Int})) + (6)))) + ((420) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left((n) + (3)\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

The shifted relation for L plus six.

Finite column enumeration supplies every transition and initial weight. TransferMatrix.cardMatrix gives the count at arbitrary width. Twenty-six continuation vectors verify an order-24 vector relation after one transition. TransferMatrix.scalarRelationShift propagates that relation. Its coefficients sum to one, so adding the constant six preserves it. The scalar relation starts at width 27; width 26 is supplied separately by the initial values.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.Col`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.L`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.class_rep`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.column`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.initial_values`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.orbit`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.recurrence`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.representatives`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
