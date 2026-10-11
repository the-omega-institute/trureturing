# SquareFirstColumnDecomposition

## Abstract

SquareFirstColumnDecomposition for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Definition 1.1 (AvoidASM).**

$$\begin{aligned}\forall (n : \mathbb{N}) , \operatorname{AvoidASM} n : \operatorname{Type}\\\forall (n : \mathbb{N}) , \operatorname{AvoidASM} n = (\left\{M : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \operatorname{SignType} | \operatorname{IsASM} M \land \neg \operatorname{Contains312} M\right\})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.AvoidASM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.2 (FirstNonempty).**

$$\begin{aligned}\forall (r k d : \mathbb{N}) , \forall (\operatorname{hr} : 0 < r) , \operatorname{FirstNonempty} r k d \operatorname{hr} : \operatorname{Type}\\\forall (r k d : \mathbb{N}) , \forall (\operatorname{hr} : 0 < r) , \operatorname{FirstNonempty} r k d \operatorname{hr} = (\left\{B : \operatorname{Counted} r k d | \exists c , B . \operatorname{val} \langle 0\rangle c \neq 0\right\})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.FirstNonempty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.3 (ColumnFibre).**

$$\begin{aligned}\forall (r k d p : \mathbb{N}) , \forall (\operatorname{hr} : p < r) , \forall (\operatorname{hk} : p < k) , \operatorname{ColumnFibre} r k d p \operatorname{hr} \operatorname{hk} : \operatorname{Type}\\\forall (r k d p : \mathbb{N}) , \forall (\operatorname{hr} : p < r) , \forall (\operatorname{hk} : p < k) , \operatorname{ColumnFibre} r k d p \operatorname{hr} \operatorname{hk} = (\left\{R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType} | \operatorname{IsASR} R \land \operatorname{ExtAvoids312} R \land \operatorname{nonemptyRows} R = d \land R \langle p\rangle \langle 0\rangle = 1 \land (\forall v : \operatorname{Fin} r , v . \operatorname{val} < p \to \exists c , R v c \neq 0)\right\})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.ColumnFibre` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.4 (mergeColumnFibre).**

$$\begin{aligned}\forall (r k d p : \mathbb{N}) , \forall (\operatorname{hr} : p < r) , \forall (\operatorname{hk} : p < k) , \forall (\operatorname{hp} : 0 < p) , \forall (\operatorname{hd} : p \le d) , \forall (x : \operatorname{AvoidASM} p \times \operatorname{FirstNonempty} (r - p) (k - p) (d - p) \mathord{\cdot}) , \operatorname{mergeColumnFibre} (r := r) (k := k) (d := d) (p := p) \operatorname{hr} \operatorname{hk} \operatorname{hp} \operatorname{hd} x : \operatorname{ColumnFibre} r k d p \operatorname{hr} \operatorname{hk}\\\forall (r k d p : \mathbb{N}) , \forall (\operatorname{hr} : p < r) , \forall (\operatorname{hk} : p < k) , \forall (\operatorname{hp} : 0 < p) , \forall (\operatorname{hd} : p \le d) , \forall (x : \operatorname{AvoidASM} p \times \operatorname{FirstNonempty} (r - p) (k - p) (d - p) \mathord{\cdot}) , \forall (i : \operatorname{Fin} r) (j : \operatorname{Fin} k) , (\operatorname{mergeColumnFibre} \operatorname{hr} \operatorname{hk} \operatorname{hp} \operatorname{hd} x) . \operatorname{val} i j = \operatorname{mergeRect} x . 1 . \operatorname{val} x . 2 . \operatorname{val} . \operatorname{val} \langle i . \operatorname{val}\rangle \langle j . \operatorname{val}\rangle\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.mergeColumnFibre` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed entries specify the certified merge, with Fin value-preserving dimension casts and subtype proof fields suppressed.

**Lemma 1.5 (firstColumnFactor_card).**

$$\forall (r k d p : \mathbb{N}) , \forall (\operatorname{hr} : p < r) , \forall (\operatorname{hk} : p < k) , (0 < p) \to (p \le d) \to \operatorname{Nat} . \operatorname{card} (\operatorname{ColumnFibre} r k d p \operatorname{hr} \operatorname{hk}) = \operatorname{Nat} . \operatorname{card} (\operatorname{AvoidASM} p) \cdot \operatorname{Nat} . \operatorname{card} (\operatorname{FirstNonempty} (r - p) (k - p) (d - p) \mathord{\cdot})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.firstColumnFactor_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.6 (squareCount_card).**

$$\forall (n : \mathbb{N}) , S n n n = \operatorname{Nat} . \operatorname{card} (\operatorname{AvoidASM} n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.squareCount_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.7 (AvoidASM_zero_card).**

$$\operatorname{Nat} . \operatorname{card} (\operatorname{AvoidASM} 0) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.AvoidASM_zero_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.8 (asm_extAvoids).**

$$\forall (n : \mathbb{N}) , \forall (M : \operatorname{AvoidASM} n) , \operatorname{ExtAvoids312} M . \operatorname{val}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.asm_extAvoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.9 (asm_first_column_one).**

$$\forall (n : \mathbb{N}) , (0 < n) \to \forall (M : \operatorname{AvoidASM} n) , \exists u , M . \operatorname{val} u \langle 0\rangle = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.asm_first_column_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.10 (ASMFibre).**

$$\begin{aligned}\forall (n : \mathbb{N}) , \forall (\operatorname{hn} : 0 < n) , \forall (p : \operatorname{Fin} n) , \operatorname{ASMFibre} n \operatorname{hn} p : \operatorname{Type}\\\forall (n : \mathbb{N}) , \forall (\operatorname{hn} : 0 < n) , \forall (p : \operatorname{Fin} n) , \operatorname{ASMFibre} n \operatorname{hn} p = (\left\{M : \operatorname{AvoidASM} n | M . \operatorname{val} p \langle 0\rangle = 1\right\})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.ASMFibre` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.11 (fullFirstNonemptyEquiv).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (\operatorname{hr} : 0 < r) , \operatorname{fullFirstNonemptyEquiv} r k \operatorname{hr} : \operatorname{Equiv} (\operatorname{FirstNonempty} r k r \operatorname{hr}) (\operatorname{Counted} r k r)\\\forall (r k : \mathbb{N}) , \forall (\operatorname{hr} : 0 < r) , ((\operatorname{fullFirstNonemptyEquiv} r k \operatorname{hr}) . \operatorname{toFun} = (\operatorname{fun} B \mapsto B . \operatorname{val})) \land ((\operatorname{fullFirstNonemptyEquiv} r k \operatorname{hr}) . \operatorname{invFun} = (\operatorname{fun} B \mapsto \langle B\rangle))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.fullFirstNonemptyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted. The two equalities give the toFun and invFun fields; subtype proof fields are suppressed.

**Lemma 1.12 (asmNonzeroFibre_card).**

$$\forall (n : \mathbb{N}) , \forall (\operatorname{hn} : 0 < n) , \forall (p : \operatorname{Fin} n) , (0 < p . \operatorname{val}) \to \operatorname{Nat} . \operatorname{card} (\operatorname{ASMFibre} n \operatorname{hn} p) = \operatorname{Nat} . \operatorname{card} (\operatorname{AvoidASM} p . \operatorname{val}) \cdot \operatorname{Nat} . \operatorname{card} (\operatorname{AvoidASM} (n - p . \operatorname{val}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.asmNonzeroFibre_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.ASMFibre`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.AvoidASM`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.AvoidASM_zero_card`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.ColumnFibre`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.FirstNonempty`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.asmNonzeroFibre_card`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.asm_extAvoids`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.asm_first_column_one`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.firstColumnFactor_card`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.fullFirstNonemptyEquiv`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.mergeColumnFibre`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.squareCount_card`
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction](SquareMergeConstruction.md)
