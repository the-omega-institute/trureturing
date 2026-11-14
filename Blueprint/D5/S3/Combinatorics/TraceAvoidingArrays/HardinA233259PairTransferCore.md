# One-sided pair transfer core

## Abstract

The four-row one-sided pair transfer definitions.

The core supplies the literal four-row proper-pattern predicate, its fourteen-class transfer matrix and the public grid transport used by the counting certificate.

**Definition 1.1 (One-sided column compatibility).**

$$\forall a \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col},\; \forall b \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{compatible}\left(a, b\right) = \left(\forall r \in \operatorname{Fin}\left(4\right),\; \forall s \in \operatorname{Fin}\left(4\right),\; ((r = s) \lor ((\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1) = \operatorname{Fin}.\operatorname{val}\left(s\right))) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(a, s\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(b, r\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

One-sided column compatibility.

**Definition 1.2 (Deciding column compatibility).**

$$\forall a \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col},\; \forall b \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col},\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{instDecidableCompatible}\left(a, b\right): \operatorname{Decidable}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{compatible}\left(a, b\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.instDecidableCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Deciding column compatibility.

**Definition 1.3 (Proper pair-label patterns).**

$$\forall n \in \operatorname{Nat},\; \forall P \in (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Proper}\left(P\right) = \left(\forall j \in \operatorname{Fin}\left(n\right),\; \forall h \in (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n,\; \forall r \in \operatorname{Fin}\left(4\right),\; \forall s \in \operatorname{Fin}\left(4\right),\; ((r = s) \lor ((\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1) = \operatorname{Fin}.\operatorname{val}\left(s\right))) \Rightarrow (P\left((s, j)\right) \ne P\left((r, \operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right))\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Proper pair-label patterns.

**Definition 1.4 (Literal pair-pattern count).**

$$\forall n \in \operatorname{Nat},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{L}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Proper}\left(P\right)), \operatorname{Finset}.\operatorname{univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Literal pair-pattern count.

**Definition 1.5 (Fourteen-class transfer matrix).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Q} = ![![2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0], ![1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1]]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Fourteen-class transfer matrix.

**Definition 1.6 (Class weights).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{weights} = (![48, 48, 24, 48, 24, 24, 12, 12, 24, 48, 24, 12, 12, 24]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Class weights.

**Theorem 1.7 (Relabelling preserves compatibility).**

$$\forall e \in \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right),\; \forall a \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col},\; \forall b \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col},\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{compatible}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e, a\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e, b\right)\right)) \Leftrightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{compatible}\left(a, b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.compatible_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Relabelling preserves compatibility.

**Theorem 1.8 (Grid locality characterization).**

$$\forall n \in \operatorname{Nat},\; \forall P \in (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Proper}\left(P\right)) \Leftrightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{TransferMatrix}.\operatorname{good}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{compatible}, \operatorname{Function}.\operatorname{const}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}, \operatorname{Function}.\operatorname{const}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}, \operatorname{Function}.\operatorname{const}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}, \operatorname{True}\right)\right)\right), \operatorname{List}.\operatorname{ofFn}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{gridEquiv}\left(n\right)\left(P\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.grid_good` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Grid locality characterization.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.L`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.Q`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.compatible_relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.grid_good`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.instDecidableCompatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.weights`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
