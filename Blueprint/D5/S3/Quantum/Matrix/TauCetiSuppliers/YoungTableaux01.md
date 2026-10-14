# YoungTableaux01

## Abstract

Finite-group, partition and Young-tableau constructions from the Tau Ceti library. Symbols use the Lean names in the file namespace; tableau coordinate maps in later modules are YoungTableaux01.YoungTableau.rowIndex and colIndex. Proof arguments are suppressed when they do not affect the mathematical value.

**Theorem 1.1 (Get d row lens).**

$$\forall (\mu : \operatorname{YoungDiagram}) (i : \mathbb{N}) , \mu . \operatorname{rowLens} . \operatorname{getD} i 0 = \mu . \operatorname{rowLen} i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.getD_rowLens` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives get D row Lens.

**Theorem 1.2 (Sort coe row lens).**

$$\forall (\mu : \operatorname{YoungDiagram}) , (((\mu . \operatorname{rowLens} : \operatorname{Multiset} \mathbb{N})) . \operatorname{sort} \operatorname{fun} \operatorname{x1} \operatorname{x2} \mapsto \operatorname{x1} \ge \operatorname{x2}) = \mu . \operatorname{rowLens}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.sort_coe_rowLens` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives sort coe row Lens.

**Theorem 1.3 (Sum range row len eq card filter fst).**

$$\forall (\mu : \operatorname{YoungDiagram}) (k : \mathbb{N}) , \sum_{i \in \operatorname{Finset} . \operatorname{range} k} \mu . \operatorname{rowLen} i = \{ c \in \mu . \operatorname{cells} | c . 1 < k \} . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.sum_range_rowLen_eq_card_filter_fst` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives sum range row Len eq card filter fst.

**Theorem 1.4 (Card eq sum range row len).**

$$\forall (\mu : \operatorname{YoungDiagram}) (N : \mathbb{N}) , \mu . \operatorname{colLen} 0 \le N \to \mu . \operatorname{card} = \sum_{i \in \operatorname{Finset} . \operatorname{range} N} \mu . \operatorname{rowLen} i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_eq_sum_range_rowLen` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives card eq sum range row Len.

**Theorem 1.5 (Card filter cells).**

$$\forall (\mu : \operatorname{YoungDiagram}) (p : \mathbb{N} \times \mathbb{N} \to \operatorname{Prop}) [ \operatorname{DecidablePred} p ] (N : \mathbb{N}) , \mu . \operatorname{colLen} 0 \le N \to (\operatorname{Finset} . \operatorname{filter} p \mu . \operatorname{cells}) . \operatorname{card} = \sum_{i \in \operatorname{Finset} . \operatorname{range} N} \{ j \in \operatorname{Finset} . \operatorname{range} (\mu . \operatorname{rowLen} i) | p (i , j) \} . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_filter_cells` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives card filter cells.

**Theorem 1.6 (Sum take row lens eq card filter fst).**

$$\forall (\mu : \operatorname{YoungDiagram}) (k : \mathbb{N}) , (\operatorname{List} . \operatorname{take} k \mu . \operatorname{rowLens}) . \operatorname{sum} = \{ c \in \mu . \operatorname{cells} | c . 1 < k \} . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.sum_take_rowLens_eq_card_filter_fst` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives sum take row Lens eq card filter fst.

**Theorem 1.7 (Card filter le sum take row lens).**

$$\forall (\alpha : \operatorname{Type}) [ \operatorname{Fintype} \alpha ] (lam : \operatorname{YoungDiagram}) (r : \alpha \to \mathbb{N}) (f : \alpha \to \mathbb{N} \times \mathbb{N}) , (\forall (a : \alpha) , f a \in lam . \operatorname{cells}) \to \operatorname{Function} . \operatorname{Injective} f \to (\forall (a b : \alpha) , r a = r b \to (f a) . 2 = (f b) . 2 \to a = b) \to \forall (k : \mathbb{N}) , ((\operatorname{Finset} . \operatorname{univ} : \operatorname{Finset} (\alpha)) . \operatorname{filter} (\operatorname{fun} (a : \alpha) \mapsto r a < k)) . \operatorname{card} \le (\operatorname{List} . \operatorname{take} k lam . \operatorname{rowLens}) . \operatorname{sum}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_filter_le_sum_take_rowLens` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives card filter le sum take row Lens.

**Theorem 1.8 (Row len le of le).**

$$\forall (\mu \nu : \operatorname{YoungDiagram}) , \nu \le \mu \to \forall (i : \mathbb{N}) , \nu . \operatorname{rowLen} i \le \mu . \operatorname{rowLen} i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowLen_le_of_le` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Len le of le.

**Theorem 1.9 (Le of forall row len le).**

$$\forall (\mu \nu : \operatorname{YoungDiagram}) , (\forall (i : \mathbb{N}) , \nu . \operatorname{rowLen} i \le \mu . \operatorname{rowLen} i) \to \nu \le \mu$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.le_of_forall_rowLen_le` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives le of forall row Len le.

**Theorem 1.10 (Le row len of forall mem).**

$$\forall (\nu : \operatorname{YoungDiagram}) (i k : \mathbb{N}) , (\forall (j : \mathbb{N}) , j < k \to (i , j) \in \nu) \to k \le \nu . \operatorname{rowLen} i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.le_rowLen_of_forall_mem` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives le row Len of forall mem.

**Theorem 1.11 (Finite iic).**

$$\forall (\mu : \operatorname{YoungDiagram}) , (\operatorname{Set} . \operatorname{Iic} \mu) . \operatorname{Finite}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.finite_Iic` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives finite Iic.

**Theorem 1.12 (Mem iff of col len le one).**

$$\forall (\mu : \operatorname{YoungDiagram}) , \mu . \operatorname{colLen} 0 \le 1 \to \forall (i j : \mathbb{N}) , (i , j) \in \mu \iff i = 0 \land j < \mu . \operatorname{rowLen} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.mem_iff_of_colLen_le_one` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives mem iff of col Len le one.

**Theorem 1.13 (Card eq row len of col len le one).**

$$\forall (\mu : \operatorname{YoungDiagram}) , \mu . \operatorname{colLen} 0 \le 1 \to \mu . \operatorname{card} = \mu . \operatorname{rowLen} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_eq_rowLen_of_colLen_le_one` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives card eq row Len of col Len le one.

**Definition 1.14 (Of row lens fin).**

$$\forall (n : \mathbb{N}) (f : \operatorname{Fin} n \to \mathbb{N}) (\operatorname{hf} : \operatorname{Antitone} f) , \operatorname{YoungDiagram} . \operatorname{ofRowLensFin} f \operatorname{hf} = \operatorname{YoungDiagram} . \operatorname{ofRowLens} (\operatorname{List} . \operatorname{ofFn} f)$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.ofRowLensFin` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The diagram is obtained from List.ofFn f by YoungDiagram.ofRowLens; antitonicity supplies the sortedness proof.

**Theorem 1.15 (Row len of row lens fin).**

$$\forall (n : \mathbb{N}) (f : \operatorname{Fin} n \to \mathbb{N}) (\operatorname{hf} : \operatorname{Antitone} f) (i : \operatorname{Fin} n) , (\operatorname{YoungDiagram} . \operatorname{ofRowLensFin} f \operatorname{hf}) . \operatorname{rowLen} (\operatorname{val} i) = f i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowLen_ofRowLensFin` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Len of Row Lens Fin.

**Theorem 1.16 (Row len of row lens fin eq zero of le).**

$$\forall (n : \mathbb{N}) (f : \operatorname{Fin} n \to \mathbb{N}) (\operatorname{hf} : \operatorname{Antitone} f) (i : \mathbb{N}) , n \le i \to (\operatorname{YoungDiagram} . \operatorname{ofRowLensFin} f \operatorname{hf}) . \operatorname{rowLen} i = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowLen_ofRowLensFin_eq_zero_of_le` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Len of Row Lens Fin eq zero of le.

**Theorem 1.17 (Col len zero of row lens fin le).**

$$\forall (n : \mathbb{N}) (f : \operatorname{Fin} n \to \mathbb{N}) (\operatorname{hf} : \operatorname{Antitone} f) , (\operatorname{YoungDiagram} . \operatorname{ofRowLensFin} f \operatorname{hf}) . \operatorname{colLen} 0 \le n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.colLen_zero_ofRowLensFin_le` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives col Len zero of Row Lens Fin le.

**Theorem 1.18 (Of row lens fin row len).**

$$\forall (n : \mathbb{N}) (\mu : \operatorname{YoungDiagram}) , \mu . \operatorname{colLen} 0 \le n \to \operatorname{YoungDiagram} . \operatorname{ofRowLensFin} (\operatorname{fun} (i : \operatorname{Fin} n) \mapsto \mu . \operatorname{rowLen} (\operatorname{val} i)) = \mu$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.ofRowLensFin_rowLen` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives of Row Lens Fin row Len.

**Theorem 1.19 (Entry le of le).**

$$\forall (\mu : \operatorname{YoungDiagram}) (T : \operatorname{SemistandardYoungTableau} \mu) (\operatorname{i1} \operatorname{i2} \operatorname{j1} \operatorname{j2} : \mathbb{N}) , \operatorname{i1} \le \operatorname{i2} \to \operatorname{j1} \le \operatorname{j2} \to (\operatorname{i2} , \operatorname{j2}) \in \mu \to T \operatorname{i1} \operatorname{j1} \le T \operatorname{i2} \operatorname{j2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.entry_le_of_le` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives entry le of le.

**Definition 1.20 (Row index).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (k : \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{rowIndex} t k = (\operatorname{val} (t . \operatorname{symm} k) : \mathbb{N} \times \mathbb{N}) . 1$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowIndex` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Index.

**Definition 1.21 (Col index).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (k : \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{colIndex} t k = (\operatorname{val} (t . \operatorname{symm} k) : \mathbb{N} \times \mathbb{N}) . 2$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.colIndex` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives col Index.

**Theorem 1.22 (Row index def).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (k : \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{rowIndex} t k = (\operatorname{val} (t . \operatorname{symm} k)) . 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowIndex_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Index def.

**Theorem 1.23 (Col index def).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (k : \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{colIndex} t k = (\operatorname{val} (t . \operatorname{symm} k)) . 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.colIndex_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives col Index def.

**Theorem 1.24 (Row index apply).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (c : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \}) , \operatorname{YoungTableau} . \operatorname{rowIndex} t (t c) = (\operatorname{val} c) . 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowIndex_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Index apply.

**Theorem 1.25 (Col index apply).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (c : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \}) , \operatorname{YoungTableau} . \operatorname{colIndex} t (t c) = (\operatorname{val} c) . 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.colIndex_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives col Index apply.

**Theorem 1.26 (Row index col index injective).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{Function} . \operatorname{Injective} \operatorname{fun} k \mapsto (\operatorname{YoungTableau} . \operatorname{rowIndex} t k , \operatorname{YoungTableau} . \operatorname{colIndex} t k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowIndex_colIndex_injective` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Index col Index injective.

**Theorem 1.27 (Row index lt col len zero).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (x : \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{rowIndex} t x < \mu . \operatorname{colLen} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowIndex_lt_colLen_zero` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Index lt col Len zero.

**Theorem 1.28 (Card filter row index eq).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (i : \mathbb{N}) , ((\operatorname{Finset} . \operatorname{univ} : \operatorname{Finset} (\operatorname{Fin} \mu . \operatorname{card})) . \operatorname{filter} (\operatorname{fun} (y : \operatorname{Fin} \mu . \operatorname{card}) \mapsto \operatorname{YoungTableau} . \operatorname{rowIndex} t y = i)) . \operatorname{card} = \mu . \operatorname{rowLen} i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_filter_rowIndex_eq` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives card filter row Index eq.

**Theorem 1.29 (Exists ne and apply eq of lt col len).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (\alpha : \operatorname{Type}) [ \operatorname{Fintype} \alpha ] (j : \mathbb{N}) , \operatorname{Fintype} . \operatorname{card} \alpha < \mu . \operatorname{colLen} j \to \forall (p : \operatorname{Fin} \mu . \operatorname{card} \to \alpha) , \exists (a b : \operatorname{Fin} \mu . \operatorname{card}) , \operatorname{YoungTableau} . \operatorname{colIndex} t a = j \land \operatorname{YoungTableau} . \operatorname{colIndex} t b = j \land a \neq b \land p a = p b$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.exists_ne_and_apply_eq_of_lt_colLen` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives exists ne and apply eq of lt col Len.

**Theorem 1.30 (Card filter row index lt).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (k : \mathbb{N}) , ((\operatorname{Finset} . \operatorname{univ} : \operatorname{Finset} (\operatorname{Fin} \mu . \operatorname{card})) . \operatorname{filter} (\operatorname{fun} (x : \operatorname{Fin} \mu . \operatorname{card}) \mapsto \operatorname{YoungTableau} . \operatorname{rowIndex} t x < k)) . \operatorname{card} = (\operatorname{List} . \operatorname{take} k \mu . \operatorname{rowLens}) . \operatorname{sum}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_filter_rowIndex_lt` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives card filter row Index lt.

**Theorem 1.31 (Card filter col index comp lt and row index eq le).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (u : \operatorname{Fin} \mu . \operatorname{card} \to \operatorname{Fin} \mu . \operatorname{card}) , (\operatorname{Function} . \operatorname{Injective} \operatorname{fun} x \mapsto (\operatorname{YoungTableau} . \operatorname{rowIndex} t x , \operatorname{YoungTableau} . \operatorname{colIndex} t (u x))) \to \forall (i k : \mathbb{N}) , ((\operatorname{Finset} . \operatorname{univ} : \operatorname{Finset} (\operatorname{Fin} \mu . \operatorname{card})) . \operatorname{filter} (\operatorname{fun} (y : \operatorname{Fin} \mu . \operatorname{card}) \mapsto \operatorname{YoungTableau} . \operatorname{colIndex} t (u y) < k \land \operatorname{YoungTableau} . \operatorname{rowIndex} t y = i)) . \operatorname{card} \le \operatorname{min} (\mu . \operatorname{rowLen} i) k$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_filter_colIndex_comp_lt_and_rowIndex_eq_le` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives card filter col Index comp lt and row Index eq le.

**Theorem 1.32 (Sum card filter col index comp lt and row index eq).**

$$\forall (\mu : \operatorname{YoungDiagram}) (t : \{ c : \mathbb{N} \times \mathbb{N} // c \in \mu . \operatorname{cells} \} \equiv \operatorname{Fin} \mu . \operatorname{card}) (u : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} \mu . \operatorname{card})) (k : \mathbb{N}) , \sum_{i \in \operatorname{Finset} . \operatorname{image} (\operatorname{YoungTableau} . \operatorname{rowIndex} t) \operatorname{Finset} . \operatorname{univ}} ((\operatorname{Finset} . \operatorname{univ} : \operatorname{Finset} (\operatorname{Fin} \mu . \operatorname{card})) . \operatorname{filter} (\operatorname{fun} (y : \operatorname{Fin} \mu . \operatorname{card}) \mapsto \operatorname{YoungTableau} . \operatorname{colIndex} t (u y) < k \land \operatorname{YoungTableau} . \operatorname{rowIndex} t y = i)) . \operatorname{card} = \sum_{i \in \operatorname{Finset} . \operatorname{image} (\operatorname{YoungTableau} . \operatorname{rowIndex} t) \operatorname{Finset} . \operatorname{univ}} \operatorname{min} (\mu . \operatorname{rowLen} i) k$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.sum_card_filter_colIndex_comp_lt_and_rowIndex_eq` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives sum card filter col Index comp lt and row Index eq.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_eq_rowLen_of_colLen_le_one`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_eq_sum_range_rowLen`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_filter_cells`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_filter_colIndex_comp_lt_and_rowIndex_eq_le`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_filter_le_sum_take_rowLens`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_filter_rowIndex_eq`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.card_filter_rowIndex_lt`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.colIndex`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.colIndex_apply`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.colIndex_def`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.colLen_zero_ofRowLensFin_le`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.entry_le_of_le`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.exists_ne_and_apply_eq_of_lt_colLen`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.finite_Iic`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.getD_rowLens`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.le_of_forall_rowLen_le`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.le_rowLen_of_forall_mem`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.mem_iff_of_colLen_le_one`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.ofRowLensFin`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.ofRowLensFin_rowLen`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowIndex`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowIndex_apply`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowIndex_colIndex_injective`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowIndex_def`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowIndex_lt_colLen_zero`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowLen_le_of_le`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowLen_ofRowLensFin`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.rowLen_ofRowLensFin_eq_zero_of_le`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.sort_coe_rowLens`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.sum_card_filter_colIndex_comp_lt_and_rowIndex_eq`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.sum_range_rowLen_eq_card_filter_fst`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01.sum_take_rowLens_eq_card_filter_fst`
- Dependency: [D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01](AlgebraGroups01.md)
