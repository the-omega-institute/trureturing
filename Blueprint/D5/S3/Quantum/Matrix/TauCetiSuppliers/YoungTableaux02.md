# YoungTableaux02

## Abstract

Finite-group, partition and Young-tableau constructions from the Tau Ceti library. Symbols use the Lean names in the file namespace; tableau coordinate maps in later modules are YoungTableaux01.YoungTableau.rowIndex and colIndex. Proof arguments are suppressed when they do not affect the mathematical value.

**Theorem 1.1 (Col index lt row len of injective).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (u : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} \mu . \operatorname{card})) , (\operatorname{Function} . \operatorname{Injective} \operatorname{fun} x \mapsto (\operatorname{YoungTableau} . \operatorname{rowIndex} t x , \operatorname{YoungTableau} . \operatorname{colIndex} t (u x))) \to \forall (x : \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{colIndex} t (u x) < \mu . \operatorname{rowLen} (\operatorname{YoungTableau} . \operatorname{rowIndex} t x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.colIndex_lt_rowLen_of_injective` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives col Index lt row Len of injective.

**Definition 1.2 (Row filling).**

$$\forall (\mu : \operatorname{YoungDiagram}) (n : \mathbb{N}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (\operatorname{hn} : \mu . \operatorname{colLen} 0 \le n) (x : \operatorname{Fin} \mu . \operatorname{card}) , (\operatorname{YoungTableau} . \operatorname{rowFilling} t \operatorname{hn} x : \operatorname{Fin} n) = \langle \operatorname{YoungTableau} . \operatorname{rowIndex} t x \rangle$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.rowFilling` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The element of Fin n has value rowIndex t x. Its bound follows from rowIndex t x < μ.colLen 0 and hn. Proof fields of subtypes are omitted.

**Theorem 1.3 (Val row filling).**

$$\forall (\mu : \operatorname{YoungDiagram}) (n : \mathbb{N}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (\operatorname{hn} : \mu . \operatorname{colLen} 0 \le n) (x : \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{val} (\operatorname{YoungTableau} . \operatorname{rowFilling} t \operatorname{hn} x) = \operatorname{YoungTableau} . \operatorname{rowIndex} t x$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.val_rowFilling` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives val row Filling.

**Definition 1.4 (Relabel).**

$$\forall (\mu : \operatorname{YoungDiagram}) (\sigma : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} \mu . \operatorname{card})) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{relabel} \sigma t = t . \operatorname{trans} \sigma$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.relabel` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives relabel.

**Theorem 1.5 (Relabel apply).**

$$\forall (\mu : \operatorname{YoungDiagram}) (\sigma : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} \mu . \operatorname{card})) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (c : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \}) , (\operatorname{YoungTableau} . \operatorname{relabel} \sigma t) c = \sigma (t c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.relabel_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives relabel apply.

**Theorem 1.6 (Row index relabel).**

$$\forall (\mu : \operatorname{YoungDiagram}) (\sigma : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} \mu . \operatorname{card})) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (k : \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{rowIndex} (\operatorname{YoungTableau} . \operatorname{relabel} \sigma t) k = \operatorname{YoungTableau} . \operatorname{rowIndex} t (\sigma^{-1} k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.rowIndex_relabel` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Index relabel.

**Theorem 1.7 (Col index relabel).**

$$\forall (\mu : \operatorname{YoungDiagram}) (\sigma : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} \mu . \operatorname{card})) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (k : \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{colIndex} (\operatorname{YoungTableau} . \operatorname{relabel} \sigma t) k = \operatorname{YoungTableau} . \operatorname{colIndex} t (\sigma^{-1} k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.colIndex_relabel` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives col Index relabel.

**Definition 1.8 (Relabel perm).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t t ' : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{relabelPerm} t t ' = t . \operatorname{symm} . \operatorname{trans} t '$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.relabelPerm` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives relabel Perm.

**Theorem 1.9 (Relabel relabel perm).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t t ' : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{relabel} (\operatorname{YoungTableau} . \operatorname{relabelPerm} t t ') t = t '$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.relabel_relabelPerm` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives relabel relabel Perm.

**Theorem 1.10 (Exists relabel eq).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t t ' : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) , \exists (\sigma : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} \mu . \operatorname{card})) , \operatorname{YoungTableau} . \operatorname{relabel} \sigma t = t '$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.exists_relabel_eq` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives exists relabel eq.

**Theorem 1.11 (Nonempty).**

$$\forall (\mu : \operatorname{YoungDiagram}) , \operatorname{Nonempty} (\{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.nonempty` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives nonempty.

**Theorem 1.12 (Sum take row lens le of injective).**

$$\forall (lam m : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in lam . \operatorname{cells} \} \equiv \operatorname{Fin} lam . \operatorname{card}) (s : \{ c : \mathbb{N} \times \mathbb{N} // c \in m . \operatorname{cells} \} \equiv \operatorname{Fin} m . \operatorname{card}) (\sigma : \operatorname{Fin} m . \operatorname{card} \equiv \operatorname{Fin} lam . \operatorname{card}) , (\forall (x y : \operatorname{Fin} m . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{rowIndex} s x = \operatorname{YoungTableau} . \operatorname{rowIndex} s y \to \operatorname{YoungTableau} . \operatorname{colIndex} t (\sigma x) = \operatorname{YoungTableau} . \operatorname{colIndex} t (\sigma y) \to x = y) \to \forall (k : \mathbb{N}) , (\operatorname{List} . \operatorname{take} k m . \operatorname{rowLens}) . \operatorname{sum} \le (\operatorname{List} . \operatorname{take} k lam . \operatorname{rowLens}) . \operatorname{sum}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.sum_take_rowLens_le_of_injective` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives sum take row Lens le of injective.

**Definition 1.13 (Standard young tableau).**

$$\begin{aligned}\forall (\mu : \operatorname{YoungDiagram}) (T : \operatorname{StandardYoungTableau} \mu) , T . \operatorname{toTableau} : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}\\\forall (\mu : \operatorname{YoungDiagram}) (T : \operatorname{StandardYoungTableau} \mu) , (\forall (i \operatorname{j1} \operatorname{j2} : \mathbb{N}) , \operatorname{j1} < \operatorname{j2} \to (i , \operatorname{j2}) \in \mu \to T . \operatorname{toTableau} \langle (i , \operatorname{j1}) \rangle < T . \operatorname{toTableau} \langle (i , \operatorname{j2}) \rangle) \land (\forall (\operatorname{i1} \operatorname{i2} j : \mathbb{N}) , \operatorname{i1} < \operatorname{i2} \to (\operatorname{i2} , j) \in \mu \to T . \operatorname{toTableau} \langle (\operatorname{i1} , j) \rangle < T . \operatorname{toTableau} \langle (\operatorname{i2} , j) \rangle)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.StandardYoungTableau` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

A standard tableau is an equivalence from the diagram cells to Fin μ.card with strictly increasing entries along each row and column. In the displayed subtype constructors, membership proofs supplied by YoungDiagram.up_left_mem are omitted.

**Definition 1.14 (Row superstandard).**

$$\forall (\mu : \operatorname{YoungDiagram}) (c : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \}) , \operatorname{val} ((\operatorname{StandardYoungTableau} . \operatorname{rowSuperstandard} \mu) . \operatorname{toTableau} c) = (\sum_{(i : \mathbb{N}) \in \operatorname{Finset} . \operatorname{range} (\operatorname{val} c) . 1} \mu . \operatorname{rowLen} i) + (\operatorname{val} c) . 2$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.rowSuperstandard` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The entries enumerate cells in row order. The equivalence is Equiv.ofBijective applied to the displayed value; injectivity and equal finite cardinalities supply bijectivity. Both strictness fields follow from the same prefix-sum formula.

**Theorem 1.15 (Sum row lens eq card).**

$$\forall (mu : \operatorname{YoungDiagram}) , mu . \operatorname{rowLens} . \operatorname{sum} = mu . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.sum_rowLens_eq_card` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives sum row Lens eq card.

**Theorem 1.16 (Card transpose).**

$$\forall (mu : \operatorname{YoungDiagram}) , mu . \operatorname{transpose} . \operatorname{card} = mu . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.card_transpose` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives card transpose.

**Theorem 1.17 (Row lens of partition eq sort parts).**

$$\forall (n : \mathbb{N}) (p : \operatorname{Nat} . \operatorname{Partition} n) , ((\operatorname{D5} . \operatorname{S3} . \operatorname{Combinatorics} . \operatorname{TwoLayerSolidPartitions} . \operatorname{youngPartition} n) . \operatorname{symm} p) . 1 . \operatorname{rowLens} = p . \operatorname{parts} . \operatorname{sort} (\operatorname{fun} (a b : \mathbb{N}) \mapsto b \le a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.rowLens_ofPartition_eq_sort_parts` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Lens of Partition eq sort parts.

**Theorem 1.18 (Card of partition).**

$$\forall (n : \mathbb{N}) (p : \operatorname{Nat} . \operatorname{Partition} n) , ((\operatorname{D5} . \operatorname{S3} . \operatorname{Combinatorics} . \operatorname{TwoLayerSolidPartitions} . \operatorname{youngPartition} n) . \operatorname{symm} p) . 1 . \operatorname{card} = n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.card_ofPartition` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives card of Partition.

**Theorem 1.19 (Of partition to partition).**

$$\forall (n : \mathbb{N}) (\mu : \operatorname{YoungDiagram}) (h : \mu . \operatorname{card} = n) , ((\operatorname{D5} . \operatorname{S3} . \operatorname{Combinatorics} . \operatorname{TwoLayerSolidPartitions} . \operatorname{youngPartition} n) . \operatorname{symm} (\operatorname{D5} . \operatorname{S3} . \operatorname{Combinatorics} . \operatorname{TwoLayerSolidPartitions} . \operatorname{youngPartition} n \langle \mu , h \rangle)) . 1 = \mu$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.ofPartition_toPartition` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

Applying the diagram/partition equivalence and its inverse recovers the diagram.

**Theorem 1.20 (To partition of partition).**

$$\forall (n : \mathbb{N}) (p : \operatorname{Nat} . \operatorname{Partition} n) , \operatorname{D5} . \operatorname{S3} . \operatorname{Combinatorics} . \operatorname{TwoLayerSolidPartitions} . \operatorname{youngPartition} n ((\operatorname{D5} . \operatorname{S3} . \operatorname{Combinatorics} . \operatorname{TwoLayerSolidPartitions} . \operatorname{youngPartition} n) . \operatorname{symm} p) = p$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.toPartition_ofPartition` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

Applying the inverse equivalence and then its forward map recovers the partition.

**Definition 1.21 (Content).**

$$\forall (\mu : \operatorname{YoungDiagram}) (T : \operatorname{SemistandardYoungTableau} \mu) , \operatorname{SemistandardYoungTableau} . \operatorname{content} T = (\mu . \operatorname{cells} . \operatorname{val} . \operatorname{map} (\operatorname{fun} (c : \mathbb{N} \times \mathbb{N}) \mapsto T c . 1 c . 2)) . \operatorname{toFinsupp}$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.content` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives content.

**Theorem 1.22 (Content apply).**

$$\forall (\mu : \operatorname{YoungDiagram}) (T : \operatorname{SemistandardYoungTableau} \mu) (i : \mathbb{N}) , (\operatorname{SemistandardYoungTableau} . \operatorname{content} T) i = \{ c \in \mu . \operatorname{cells} | T c . 1 c . 2 = i \} . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.content_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives content apply.

**Theorem 1.23 (Support content).**

$$\forall (\mu : \operatorname{YoungDiagram}) (T : \operatorname{SemistandardYoungTableau} \mu) , (\operatorname{SemistandardYoungTableau} . \operatorname{content} T) . \operatorname{support} = \operatorname{Finset} . \operatorname{image} (\operatorname{fun} c \mapsto T c . 1 c . 2) \mu . \operatorname{cells}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.support_content` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives support content.

**Theorem 1.24 (Le entry).**

$$\forall (\mu : \operatorname{YoungDiagram}) (T : \operatorname{SemistandardYoungTableau} \mu) (i j : \mathbb{N}) , (i , j) \in \mu \to i \le T i j$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.le_entry` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives le entry.

**Theorem 1.25 (Sum content eq card).**

$$\forall (\mu : \operatorname{YoungDiagram}) (T : \operatorname{SemistandardYoungTableau} \mu) (N : \mathbb{N}) , (\forall (c : \mathbb{N} \times \mathbb{N}) , c \in \mu . \operatorname{cells} \to T c . 1 c . 2 < N) \to \sum_{i \in \operatorname{Finset} . \operatorname{range} N} (\operatorname{SemistandardYoungTableau} . \operatorname{content} T) i = \mu . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.sum_content_eq_card` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives sum content eq card.

**Definition 1.26 (Bounded ssyt).**

$$\forall (n : \mathbb{N}) (\mu : \operatorname{YoungDiagram}) , \operatorname{BoundedSSYT} n \mu = \{ T : \operatorname{SemistandardYoungTableau} \mu // \forall (i c : \mathbb{N}) , (i , c) \in \mu \to T i c < n \}$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.BoundedSSYT` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The subtype consists of semistandard tableaux whose entries in every cell are less than n.

**Theorem 1.27 (Entry lt).**

$$\forall (n : \mathbb{N}) (\mu : \operatorname{YoungDiagram}) (T : \operatorname{BoundedSSYT} n \mu) (i c : \mathbb{N}) , (i , c) \in \mu \to \operatorname{val} T i c < n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.entry_lt` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives entry lt.

**Theorem 1.28 (Is empty of lt col len).**

$$\forall (n : \mathbb{N}) (\mu : \operatorname{YoungDiagram}) , n < \mu . \operatorname{colLen} 0 \to \operatorname{IsEmpty} (\operatorname{BoundedSSYT} n \mu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.isEmpty_of_lt_colLen` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives is Empty of lt col Len.

**Definition 1.29 (Inst unique bot young diagram).**

$$\begin{aligned}\forall (n : \mathbb{N}) , \operatorname{val} ((\operatorname{BoundedSSYT} . \operatorname{instUniqueBotYoungDiagram} n) . \operatorname{default}) = \operatorname{SemistandardYoungTableau} . \operatorname{highestWeight} (\perp : \operatorname{YoungDiagram})\\\forall (n : \mathbb{N}) (T : \operatorname{BoundedSSYT} n (\perp : \operatorname{YoungDiagram})) , T = (\operatorname{BoundedSSYT} . \operatorname{instUniqueBotYoungDiagram} n) . \operatorname{default}\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.instUniqueBotYoungDiagram` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The default field is the subtype containing highestWeight on the empty diagram; its entry bound has no cells to check. The uniqueness field equates every tableau to this default because all entries outside the empty diagram are zero. Subtype proof fields are omitted.

**Definition 1.30 (Inst fintype bounded ssyt).**

$$\forall (n : \mathbb{N}) (\mu : \operatorname{YoungDiagram}) , \operatorname{instFintypeBoundedSSYT} n \mu = \operatorname{Fintype} . \operatorname{ofFinite} (\operatorname{BoundedSSYT} n \mu)$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.instFintypeBoundedSSYT` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The finite instance is Fintype.ofFinite. A tableau embeds into the functions from the finite cells to Fin n.

**Definition 1.31 (Diagram kostka number).**

$$\forall (\mu : \operatorname{YoungDiagram}) (w : \mathbb{N} \to \mathbb{N}) , \operatorname{diagramKostkaNumber} \mu w = \operatorname{Nat} . \operatorname{card} \{ T : \operatorname{SemistandardYoungTableau} \mu // (\operatorname{SemistandardYoungTableau} . \operatorname{content} T : \mathbb{N} \to \mathbb{N}) = w \}$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.diagramKostkaNumber` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The number is the natural cardinality of the tableaux with content w.

**Theorem 1.32 (Diagram kostka number def).**

$$\forall (\mu : \operatorname{YoungDiagram}) (w : \mathbb{N} \to \mathbb{N}) , \operatorname{diagramKostkaNumber} \mu w = \operatorname{Nat} . \operatorname{card} \{ T : \operatorname{SemistandardYoungTableau} \mu // (\operatorname{SemistandardYoungTableau} . \operatorname{content} T : \mathbb{N} \to \mathbb{N}) = w \}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.diagramKostkaNumber_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives diagram Kostka Number def.

**Theorem 1.33 (Diagram kostka number row len).**

$$\forall (\mu : \operatorname{YoungDiagram}) , \operatorname{diagramKostkaNumber} \mu \mu . \operatorname{rowLen} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.diagramKostkaNumber_rowLen` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives diagram Kostka Number row Len.

**Theorem 1.34 (Sum le sum take row lens of diagram kostka number ne zero).**

$$\forall (\mu : \operatorname{YoungDiagram}) (w : \mathbb{N} \to \mathbb{N}) , \operatorname{diagramKostkaNumber} \mu w \neq 0 \to \forall (k : \mathbb{N}) , \sum_{i \in \operatorname{Finset} . \operatorname{range} k} w i \le (\operatorname{List} . \operatorname{take} k \mu . \operatorname{rowLens}) . \operatorname{sum}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives sum le sum take row Lens of diagram Kostka Number ne zero.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.BoundedSSYT`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.StandardYoungTableau`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.card_ofPartition`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.card_transpose`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.colIndex_lt_rowLen_of_injective`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.colIndex_relabel`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.content`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.content_apply`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.diagramKostkaNumber`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.diagramKostkaNumber_def`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.diagramKostkaNumber_rowLen`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.entry_lt`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.exists_relabel_eq`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.instFintypeBoundedSSYT`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.instUniqueBotYoungDiagram`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.isEmpty_of_lt_colLen`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.le_entry`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.nonempty`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.ofPartition_toPartition`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.relabel`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.relabelPerm`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.relabel_apply`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.relabel_relabelPerm`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.rowFilling`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.rowIndex_relabel`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.rowLens_ofPartition_eq_sort_parts`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.rowSuperstandard`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.sum_content_eq_card`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.sum_rowLens_eq_card`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.sum_take_rowLens_le_of_injective`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.support_content`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.toPartition_ofPartition`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02.val_rowFilling`
- Dependency: [D5/S3/Combinatorics/TwoLayerSolidPartitions](../../../Combinatorics/TwoLayerSolidPartitions.md)
- Dependency: [D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01](YoungTableaux01.md)
