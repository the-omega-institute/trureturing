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

**Definition 1.5 (The fourteen equality classes).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left(c\right) = ((let a: \operatorname{Fin}\left(3\right) := \operatorname{Prod}.\operatorname{fst}\left(c\right); (let b: \operatorname{Fin}\left(3\right) := \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right); (let d: \operatorname{Fin}\left(3\right) := \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right); (let e: \operatorname{Fin}\left(3\right) := \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right); (if a = b then (if a = d then (if a = e then 0 else 1) else (if a = e then 2 else (if d = e then 3 else 4))) else (if a = d then (if a = e then 5 else (if b = e then 6 else 7)) else (if b = d then (if a = e then 8 else (if b = e then 9 else 10)) else (if a = e then 11 else (if b = e then 12 else 13))))))))): \operatorname{Fin}\left(14\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.cls` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

The fourteen equality classes.

**Definition 1.6 (First-appearance representatives).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{representatives} = (![((0, (0, (0, 0))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (0, (0, 1))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (0, (1, 0))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (0, (1, 1))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (0, (1, 2))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (0, 0))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (0, 1))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (0, 2))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (1, 0))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (1, 1))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (1, 2))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (2, 0))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (2, 1))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), ((0, (1, (2, 2))): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})]: \operatorname{Fin}\left(14\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

First-appearance representatives.

**Definition 1.7 (Coordinatewise label permutations).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e\right) = \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, e\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Coordinatewise label permutations.

**Theorem 1.8 (Relabelling column coordinates).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\forall (r: \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e\right): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col} \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})\left(c\right), r\right) = (e: \operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right))\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(c, r\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Relabelling column coordinates.

**Theorem 1.9 (Relabelling preserves equality classes).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e\right): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col} \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})\left(c\right)\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left(c\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.class_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Relabelling preserves equality classes.

**Theorem 1.10 (Every column has a representative).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\exists (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e\right): \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col} \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col})\left(c\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{representatives}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left(c\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.class_rep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Every column has a representative.

**Definition 1.11 (Grids as sequences of columns).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{gridEquiv}\left(n\right) = \operatorname{Equiv}.\operatorname{mk}\left((\lambda (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto (\lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (P\left((0, j)\right), (P\left((1, j)\right), (P\left((2, j)\right), P\left((3, j)\right)))))), (\lambda (f: \operatorname{Fin}\left(n\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}) \mapsto (\lambda (p: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right))) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(f\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right), \operatorname{Prod}.\operatorname{fst}\left(p\right)\right))), (\lambda (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto by funext p; rcases p with \langle r,j\rangle; \operatorname{fin_{cases}} r <;> rfl), (\lambda (f: \operatorname{Fin}\left(n\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}) \mapsto \operatorname{Eq}.\operatorname{refl}\left(f\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.gridEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Grids as sequences of columns.

**Theorem 1.12 (Recovering a grid entry).**

$$\forall (n: \operatorname{Nat}), (\forall (P: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (r: \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{column}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{gridEquiv}\left(n\right): \left((\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{Col}\right))\left(P, j\right), r\right) = P\left((r, j)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column_grid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Recovering a grid entry.

**Theorem 1.13 (Eight initial pair-pattern counts).**

$$\forall (k: \operatorname{Fin}\left(8\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left((\operatorname{Fin}.\operatorname{val}\left(k\right)) + (2)\right): \operatorname{Int}) = (![162, 1122, 5808, 33702, 186720, 1054446, 5907444, 33206862]: \operatorname{Fin}\left(8\right) \to \operatorname{Int})\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.initial_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Eight initial pair-pattern counts.

**Theorem 1.14 (The constant-adjusted pair-pattern recurrence).**

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
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.class_relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.class_rep`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.cls`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column_grid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.column_relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.gridEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.initial_values`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.recurrence`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.representatives`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
