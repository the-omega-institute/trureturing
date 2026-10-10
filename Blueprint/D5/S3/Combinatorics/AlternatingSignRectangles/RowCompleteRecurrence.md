# RowCompleteRecurrence

## Abstract

RowCompleteRecurrence for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Definition 1.1 (zeroColumn).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{zeroColumn} (r := r) (k := k) B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} (k + 1)) \operatorname{SignType}\\\forall (r k : \mathbb{N}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{zeroColumn} (r := r) (k := k) B = (\operatorname{fun} u \mapsto \operatorname{Fin} . \operatorname{cons} 0 (B u))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.zeroColumn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.2 (zeroColumn_zero).**

$$\forall (r k : \mathbb{N}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (u : \operatorname{Fin} r) , \operatorname{zeroColumn} B u 0 = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.zeroColumn_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.3 (zeroColumn_succ).**

$$\forall (r k : \mathbb{N}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (u : \operatorname{Fin} r) , \forall (c : \operatorname{Fin} k) , \operatorname{zeroColumn} B u c . \operatorname{succ} = B u c$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.zeroColumn_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.4 (zeroColumn_reconstruct).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} (k + 1)) \operatorname{SignType}) , (\forall u , R u 0 = 0) \to \operatorname{zeroColumn} ((\operatorname{fun} u c \mapsto R u c . \operatorname{succ})) = R$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.zeroColumn_reconstruct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.5 (ZeroColumnFibre).**

$$\begin{aligned}\forall (r k d : \mathbb{N}) , \operatorname{ZeroColumnFibre} r k d : \operatorname{Type}\\\forall (r k d : \mathbb{N}) , \operatorname{ZeroColumnFibre} r k d = (\left\{R : \operatorname{Counted} r (k + 1) d | \forall u , R . \operatorname{val} u 0 = 0\right\})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.ZeroColumnFibre` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.6 (extractZeroColumn).**

$$\begin{aligned}\forall (r k d : \mathbb{N}) , \forall (R : \operatorname{ZeroColumnFibre} r k d) , \operatorname{extractZeroColumn} (r := r) (k := k) (d := d) R : \operatorname{Counted} r k d\\\forall (r k d : \mathbb{N}) , \forall (R : \operatorname{ZeroColumnFibre} r k d) , \forall (i : \operatorname{Fin} r) (j : \operatorname{Fin} k) , (\operatorname{extractZeroColumn} R) . \operatorname{val} i j = R . \operatorname{val} . \operatorname{val} i j . \operatorname{succ}\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.extractZeroColumn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed entries specify removal of the zero first column; subtype proof fields are suppressed.

**Definition 1.7 (zeroColumnFibreEquiv).**

$$\begin{aligned}\forall (r k d : \mathbb{N}) , \operatorname{zeroColumnFibreEquiv} r k d : \operatorname{Equiv} (\operatorname{ZeroColumnFibre} r k d) (\operatorname{Counted} r k d)\\\forall (r k d : \mathbb{N}) , ((\operatorname{zeroColumnFibreEquiv} r k d) . \operatorname{toFun} = \operatorname{extractZeroColumn}) \land ((\operatorname{zeroColumnFibreEquiv} r k d) . \operatorname{invFun} = (\operatorname{fun} B \mapsto \langle \langle \operatorname{zeroColumn} B . \operatorname{val}\rangle\rangle))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.zeroColumnFibreEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted. The two equalities give the toFun and invFun fields; subtype proof fields are suppressed.

**Lemma 1.8 (pivot_before_nonempty_of_deficit).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to \forall (\operatorname{hk} : 0 < k) , \forall (i : \operatorname{Fin} r) , (R i \langle 0 , \operatorname{hk}\rangle = 1) \to (\operatorname{nonemptyRows} R < k) \to \forall v : \operatorname{Fin} r , v . \operatorname{val} < i . \operatorname{val} \to \exists c , R v c \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.pivot_before_nonempty_of_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.9 (positiveFirst_card).**

$$\forall (r k d : \mathbb{N}) , (d \le r) \to (d \le k) \to (d < k \lor d = r) \to \operatorname{Nat} . \operatorname{card} (\left\{R : \operatorname{Counted} (r + 1) (k + 1) (d + 1) | \exists i , R . \operatorname{val} i \langle 0\rangle = 1\right\}) = S r k d + \sum_{p : \operatorname{Fin} d} \operatorname{Nat} . \operatorname{card} (\operatorname{AvoidASM} (p . \operatorname{val} + 1)) \cdot \operatorname{Nat} . \operatorname{card} (\operatorname{FirstNonempty} (r - p . \operatorname{val}) (k - p . \operatorname{val}) (d - p . \operatorname{val}) \mathord{\cdot})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.positiveFirst_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.10 (rectangle_merge_nat).**

$$\forall (r k d : \mathbb{N}) , (d \le r) \to (d \le k) \to (d < k \lor d = r) \to S (r + 1) (k + 1) (d + 1) = S (r + 1) k (d + 1) + S r k d + \sum_{p : \operatorname{Fin} d} \operatorname{Nat} . \operatorname{card} (\operatorname{AvoidASM} (p . \operatorname{val} + 1)) \cdot \operatorname{Nat} . \operatorname{card} (\operatorname{FirstNonempty} (r - p . \operatorname{val}) (k - p . \operatorname{val}) (d - p . \operatorname{val}) \mathord{\cdot})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.rectangle_merge_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.11 (sum_Icc_two).**

$$\forall (\alpha : \operatorname{Type}) , [\operatorname{AddCommMonoid} \alpha] \to \forall (r : \mathbb{N}) , (0 < r) \to \forall (f : \mathbb{N} \to \alpha) , (\sum_{i : \operatorname{CoeSort}.\operatorname{coe} (\operatorname{Icc} 2 r)} f i . \operatorname{val}) = \sum_{p : \operatorname{Fin} (r - 1)} f (p . \operatorname{val} + 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.sum_Icc_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.12 (S_row).**

$$\forall (r k : \mathbb{N}) , (0 < r) \to (r < k) \to (S r k r : \mathbb{Z}) = (S r (k - 1) r : \mathbb{Z}) + (S (r - 1) (k - 1) (r - 1) : \mathbb{Z}) + \sum_{i : \operatorname{CoeSort}.\operatorname{coe} (\operatorname{Icc} 2 r)} (\operatorname{Nat} . \operatorname{largeSchroder} (i . \operatorname{val} - 2) : \mathbb{Z}) \cdot (S (r + 1 - i . \operatorname{val}) (k + 1 - i . \operatorname{val}) (r + 1 - i . \operatorname{val}) : \mathbb{Z})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.S_row` (`✓ std3`). ∎

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

Proposition 4.2 (p. 6), from the first-column decomposition of a rectangle with every row nonempty.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.S_row`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.ZeroColumnFibre`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.extractZeroColumn`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.pivot_before_nonempty_of_deficit`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.positiveFirst_card`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.rectangle_merge_nat`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.sum_Icc_two`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.zeroColumn`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.zeroColumnFibreEquiv`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.zeroColumn_reconstruct`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.zeroColumn_succ`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence.zeroColumn_zero`
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition](SquareASMDecomposition.md)
