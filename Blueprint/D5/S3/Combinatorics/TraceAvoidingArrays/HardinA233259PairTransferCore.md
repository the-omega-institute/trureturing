# One-sided pair transfer core

## Abstract

The four-row one-sided pair transfer definitions.

The core supplies the literal four-row proper-pattern predicate, its fourteen-class transfer matrix and the public grid transport used by the counting certificate.

**Definition 1.1 (Four-label columns).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col} = (\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.Col` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Four-label columns.

**Definition 1.2 (Column coordinates).**

$$\forall c \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{column}\left(c\right) = (![\operatorname{Prod}.\operatorname{fst}\left(c\right), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)]: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.column` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Column coordinates.

**Definition 1.3 (The fourteen equality classes).**

$$\forall c \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{cls}\left(c\right) = ((let a: \operatorname{Fin}\left(3\right) = \operatorname{Prod}.\operatorname{fst}\left(c\right); (let b: \operatorname{Fin}\left(3\right) = \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right); (let d: \operatorname{Fin}\left(3\right) = \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right); (let e: \operatorname{Fin}\left(3\right) = \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right); (if a = b then (if a = d then (if a = e then 0 else 1) else (if a = e then 2 else (if d = e then 3 else 4))) else (if a = d then (if a = e then 5 else (if b = e then 6 else 7)) else (if b = d then (if a = e then 8 else (if b = e then 9 else 10)) else (if a = e then 11 else (if b = e then 12 else 13))))))))): \operatorname{Fin}\left(14\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.cls` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

The fourteen equality classes.

**Definition 1.4 (First-appearance representatives).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{representatives} = (![((0, 0, 0, 0): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 0, 0, 1): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 0, 1, 0): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 0, 1, 1): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 0, 1, 2): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 1, 0, 0): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 1, 0, 1): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 1, 0, 2): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 1, 1, 0): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 1, 1, 1): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 1, 1, 2): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 1, 2, 0): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 1, 2, 1): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col}), ((0, 1, 2, 2): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col})]: \operatorname{Fin}\left(14\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

First-appearance representatives.

**Definition 1.5 (Coordinatewise label permutations).**

$$\forall e \in \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{relabel}\left(e\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Coordinatewise label permutations.

**Definition 1.6 (Grids as sequences of columns).**

$$\forall n \in \operatorname{Nat},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{gridEquiv}\left(n\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{gridEquiv}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.gridEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Grids as sequences of columns.

**Theorem 1.7 (Recovering a grid entry).**

$$\forall n \in \operatorname{Nat},\; \forall P \in (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \forall r \in \operatorname{Fin}\left(4\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{column}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{gridEquiv}\left(n\right)\left(P, j\right), r\right) = P\left((r, j)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.column_grid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Recovering a grid entry.

**Definition 1.8 (One-sided column compatibility).**

$$\forall a \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col},\; \forall b \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{compatible}\left(a, b\right) = \left(\forall r \in \operatorname{Fin}\left(4\right),\; \forall s \in \operatorname{Fin}\left(4\right),\; ((r = s) \lor ((\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1) = \operatorname{Fin}.\operatorname{val}\left(s\right))) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{column}\left(a, s\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{column}\left(b, r\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

One-sided column compatibility.

**Definition 1.9 (Proper pair-label patterns).**

$$\forall n \in \operatorname{Nat},\; \forall P \in (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Proper}\left(P\right) = \left(\forall j \in \operatorname{Fin}\left(n\right),\; \forall h \in (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n,\; \forall r \in \operatorname{Fin}\left(4\right),\; \forall s \in \operatorname{Fin}\left(4\right),\; ((r = s) \lor ((\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1) = \operatorname{Fin}.\operatorname{val}\left(s\right))) \Rightarrow (P\left((s, j)\right) \ne P\left((r, \operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right))\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Proper pair-label patterns.

**Definition 1.10 (Literal pair-pattern count).**

$$\forall n \in \operatorname{Nat},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{L}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Proper}\left(P\right)), \operatorname{Finset}.\operatorname{univ}\left(\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Literal pair-pattern count.

**Definition 1.11 (Fourteen-class transfer matrix).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Q} = ![![2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0], ![1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1]]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Fourteen-class transfer matrix.

**Definition 1.12 (Class weights).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{weights} = (![48, 48, 24, 48, 24, 24, 12, 12, 24, 48, 24, 12, 12, 24]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Class weights.

**Theorem 1.13 (Relabelling preserves compatibility).**

$$\forall e \in \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right),\; \forall a \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col},\; \forall b \in \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Col},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{compatible}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e, a\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e, b\right)\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{compatible}\left(a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.compatible_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Relabelling preserves compatibility.

**Theorem 1.14 (Grid locality characterization).**

$$\forall n \in \operatorname{Nat},\; \forall P \in (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Proper}\left(P\right)) \Leftrightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{TransferMatrix}.\operatorname{good}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{compatible}, (\lambda (x: \operatorname{Fin}) \mapsto (\operatorname{True}) \land (x = x)), \operatorname{List}.\operatorname{ofFn}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{gridEquiv}\left(n\right)\left(P\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.grid_good` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Grid locality characterization.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.Col`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.L`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.Q`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.cls`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.column`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.column_grid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.compatible_relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.gridEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.grid_good`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.representatives`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.weights`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
