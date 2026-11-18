# Pair-label patterns and their column classes

## Abstract

A fourteen-class transfer for proper four-row pair-label patterns.

A column has four labels in Fin 3. Two consecutive columns are compatible when labels at row distance at most one differ. Relabelling the three labels preserves compatibility. The fourteen first-appearance representatives are 0000, 0001, 0010, 0011, 0012, 0100, 0101, 0102, 0110, 0111, 0112, 0120, 0121 and 0122. The constant column has three relabellings; each other representative has six. A finite check counts all compatible successors in every class for every one of the 81 columns. TransferMatrix.cardMatrix propagates these equalities to arbitrary width.

**Definition 1.1 (Proper pair-label patterns).**

$$\forall (n: \operatorname{Nat}), (\forall (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Proper}\left(P\right) = (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(4\right)), (\forall (s: \operatorname{Fin}\left(4\right)), (((\operatorname{Fin}.\operatorname{val}\left(r\right) \le (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)) \land (\operatorname{Fin}.\operatorname{val}\left(s\right) \le (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1))) \Rightarrow (P\left((r, j)\right) \ne P\left((s, \operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right))\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Proper pair-label patterns.

**Definition 1.2 (Literal pair-pattern count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Proper}\left(P\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Literal pair-pattern count.

**Definition 1.3 (Four-label columns).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col} = (\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times ((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.Col` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Four-label columns.

**Definition 1.4 (Column coordinates).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(c\right) = (![\operatorname{Prod}.\operatorname{fst}\left(c\right), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)]: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Column coordinates.

**Definition 1.5 (Compatibility of columns).**

$$\forall (a: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\forall (b: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{compatible}\left(a, b\right) = (\forall (r: \operatorname{Fin}\left(4\right)), (\forall (s: \operatorname{Fin}\left(4\right)), (((\operatorname{Fin}.\operatorname{val}\left(r\right) \le (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)) \land (\operatorname{Fin}.\operatorname{val}\left(s\right) \le (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1))) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(a, r\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(b, s\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Compatibility of columns.

**Definition 1.6 (Zero-defect transfer matrix).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Q} = (\begin{pmatrix}2&2&2&2&0&2&2&0&2&2&0&0&0&0\\1&0&0&1&0&1&0&0&0&1&0&0&0&0\\1&0&0&0&0&0&0&0&0&1&0&0&0&0\\1&1&0&0&0&0&0&0&0&1&1&0&0&0\\0&0&0&0&0&0&0&0&0&0&0&0&0&0\\1&1&0&0&0&0&0&0&0&0&0&0&0&0\\1&0&0&0&0&0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0&0&0&0&0&0\\1&0&0&0&0&0&0&0&0&0&0&0&0&0\\1&1&1&1&0&0&0&0&0&0&0&0&0&0\\0&0&0&1&0&0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0&0&0&0&0&0\end{pmatrix}: \operatorname{Matrix}\left(\operatorname{Fin}\left(14\right), \operatorname{Fin}\left(14\right), \operatorname{Int}\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Zero-defect transfer matrix.

**Theorem 1.7 (Compatible successor counts).**

$$\forall (b: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\forall (s: \operatorname{Fin}\left(14\right)), (\sum_{(c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})} ((if (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{compatible}\left(b, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left(c\right) = s) then (1: \operatorname{Int}) else (0: \operatorname{Int}))) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Q}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left(b\right), s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.quotient_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Compatible successor counts.

**Definition 1.8 (Zero-defect continuation vectors).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{W} = (\begin{pmatrix}1&1&1&1&1&1&1&1&1&1&1&1&1&1\\16&4&2&4&0&2&1&0&1&4&1&0&0&0\\68&26&20&25&0&20&16&0&16&26&4&0&0&0\\434&139&94&124&0&94&68&0&68&139&25&0&0&0\\2320&791&573&737&0&573&434&0&434&791&124&0&0&0\\13306&4421&3111&4026&0&3111&2320&0&2320&4421&737&0&0&0\\74072&24864&17727&22885&0&17727&13306&0&13306&24864&4026&0&0&0\\417502&139548&98936&127826&0&98936&74072&0&74072&139548&22885&0&0&0\end{pmatrix}: \operatorname{Fin}\left(8\right) \to \left(\operatorname{Fin}\left(14\right) \to \operatorname{Int}\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Zero-defect continuation vectors.

**Definition 1.9 (Sextic coefficients).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{coefficients} = (![4, 2, (-25), (-3), 16, 3]: \operatorname{Fin}\left(6\right) \to \operatorname{Int})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Sextic coefficients.

**Theorem 1.10 (Continuation powers).**

$$\forall (k: \operatorname{Fin}\left(8\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HPow}.\operatorname{hPow}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Q}, \operatorname{Fin}.\operatorname{val}\left(k\right)\right), (1: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{W}\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.powers_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Continuation powers.

**Theorem 1.11 (Sextic vector relation).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HPow}.\operatorname{hPow}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Q}, (1) + (6)\right), (1: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right) = \sum_{(j: \operatorname{Fin}\left(6\right))} (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{coefficients}\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HPow}.\operatorname{hPow}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Q}, (1) + (\operatorname{Fin}.\operatorname{val}\left(j\right))\right), (1: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.power_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Sextic vector relation.

**Definition 1.12 (The fourteen equality classes).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left(c\right) = ((let a: \operatorname{Fin}\left(3\right) := \operatorname{Prod}.\operatorname{fst}\left(c\right); (let b: \operatorname{Fin}\left(3\right) := \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right); (let d: \operatorname{Fin}\left(3\right) := \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right); (let e: \operatorname{Fin}\left(3\right) := \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right); (if a = b then (if a = d then (if a = e then 0 else 1) else (if a = e then 2 else (if d = e then 3 else 4))) else (if a = d then (if a = e then 5 else (if b = e then 6 else 7)) else (if b = d then (if a = e then 8 else (if b = e then 9 else 10)) else (if a = e then 11 else (if b = e then 12 else 13))))))))): \operatorname{Fin}\left(14\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.cls` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

The fourteen equality classes.

**Definition 1.13 (First-appearance representatives).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{representatives} = (![((0, (0, (0, 0))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (0, (0, 1))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (0, (1, 0))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (0, (1, 1))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (0, (1, 2))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (0, 0))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (0, 1))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (0, 2))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (1, 0))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (1, 1))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (1, 2))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (2, 0))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (2, 1))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (2, 2))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})]: \operatorname{Fin}\left(14\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

First-appearance representatives.

**Definition 1.14 (Coordinatewise label permutations).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e\right) = \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, e\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Coordinatewise label permutations.

**Theorem 1.15 (Relabelling column coordinates).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\forall (r: \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e\right): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col} \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})\left(c\right), r\right) = (e: \operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right))\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(c, r\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Relabelling column coordinates.

**Theorem 1.16 (Relabelling preserves equality classes).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e\right): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col} \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})\left(c\right)\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left(c\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.class_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Relabelling preserves equality classes.

**Theorem 1.17 (Every column has a representative).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\exists (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e\right): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col} \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})\left(c\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{representatives}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left(c\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.class_rep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Every column has a representative.

**Definition 1.18 (Grids as sequences of columns).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{gridEquiv}\left(n\right) = \operatorname{Equiv}.\operatorname{mk}\left((\lambda (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto (\lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (P\left((0, j)\right), (P\left((1, j)\right), (P\left((2, j)\right), P\left((3, j)\right)))))), (\lambda (f: \operatorname{Fin}\left(n\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}) \mapsto (\lambda (p: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right))) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(f\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right), \operatorname{Prod}.\operatorname{fst}\left(p\right)\right))), (\lambda (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto by funext p; rcases p with \langle r,j\rangle; \operatorname{fin_{cases}} r <;> rfl), (\lambda (f: \operatorname{Fin}\left(n\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}) \mapsto \operatorname{Eq}.\operatorname{refl}\left(f\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.gridEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Grids as sequences of columns.

**Theorem 1.19 (Recovering a grid entry).**

$$\forall (n: \operatorname{Nat}), (\forall (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (r: \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{gridEquiv}\left(n\right): \left((\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}\right))\left(P, j\right), r\right) = P\left((r, j)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column_grid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Recovering a grid entry.

**Theorem 1.20 (Eight initial pair-pattern counts).**

$$\forall (k: \operatorname{Fin}\left(8\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((\operatorname{Fin}.\operatorname{val}\left(k\right)) + (2)\right): \operatorname{Int}) = (![162, 1122, 5808, 33702, 186720, 1054446, 5907444, 33206862]: \operatorname{Fin}\left(8\right) \to \operatorname{Int})\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.initial_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Eight initial pair-pattern counts.

**Theorem 1.21 (The constant-adjusted pair-pattern recurrence).**

$$\forall (n: \operatorname{Nat}), (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (10)\right): \operatorname{Int})) + (6) = (((((((4) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (9)\right): \operatorname{Int})) + (6))) + ((13) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (8)\right): \operatorname{Int})) + (6)))) - ((19) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (7)\right): \operatorname{Int})) + (6)))) - ((22) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (6)\right): \operatorname{Int})) + (6)))) + ((27) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (5)\right): \operatorname{Int})) + (6)))) + ((2) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (4)\right): \operatorname{Int})) + (6)))) - ((4) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((n) + (3)\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

The constant-adjusted pair-pattern recurrence.

The continuation vectors satisfy the sextic x^6-3*x^5-16*x^4+3*x^3+25*x^2-2*x-4 after one transition. TransferMatrix.tabulatedPowers verifies the first eight vectors and TransferMatrix.scalarRelationShift propagates the finite relation. Subtracting consecutive sextic relations multiplies by x-1 and also annihilates the constant six.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.Col`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.L`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.Q`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.W`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.class_relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.class_rep`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.cls`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.coefficients`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column_grid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column_relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.gridEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.initial_values`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.power_polynomial`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.powers_table`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.quotient_rows`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.recurrence`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.representatives`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
