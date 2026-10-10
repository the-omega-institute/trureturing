# SquarePrefixGeometry

## Abstract

SquarePrefixGeometry for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Lemma 1.1 (line_restrict).**

$$\forall (n m : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \forall (b : \operatorname{Fin} m \to \operatorname{SignType}) , \forall (f : \operatorname{Fin} n \to \operatorname{Fin} m) , (\operatorname{StrictMono} f) \to (\forall u , b (f u) = a u) \to (\forall x , (\neg \exists u , f u = x) \to b x = 0) \to (\operatorname{Alternates} b) \to (\operatorname{StartsOne} b) \to \operatorname{Alternates} a \land \operatorname{StartsOne} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.line_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.2 (ends_restrict).**

$$\forall (n m : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , \forall (b : \operatorname{Fin} m \to \operatorname{SignType}) , \forall (f : \operatorname{Fin} n \to \operatorname{Fin} m) , (\operatorname{StrictMono} f) \to (\forall u , b (f u) = a u) \to (\forall x , (\neg \exists u , f u = x) \to b x = 0) \to (\operatorname{EndsOne} b) \to \operatorname{EndsOne} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.ends_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.3 (shiftCol).**

$$\begin{aligned}\forall (p k : \mathbb{N}) , \forall (\operatorname{hp} : p + 1 \le k) , \forall (x : \operatorname{Fin} p) , \operatorname{shiftCol} (p := p) (k := k) \operatorname{hp} x : \operatorname{Fin} k\\\forall (p k : \mathbb{N}) , \forall (\operatorname{hp} : p + 1 \le k) , \forall (x : \operatorname{Fin} p) , \operatorname{shiftCol} (p := p) (k := k) \operatorname{hp} x = (\langle x . \operatorname{val} + 1\rangle)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.shiftCol` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.4 (prefix_first_column_zero).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to \forall (\operatorname{hk} : 0 < k) , \forall (i u : \operatorname{Fin} r) , (u < i) \to (R i \langle 0 , \operatorname{hk}\rangle = 1) \to R u \langle 0\rangle = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefix_first_column_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.5 (prefix_outside_zero).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to \forall (\operatorname{hk} : 0 < k) , \forall (i u : \operatorname{Fin} r) , \forall (b : \operatorname{Fin} k) , (u < i) \to (R i \langle 0 , \operatorname{hk}\rangle = 1) \to (i . \operatorname{val} < b . \operatorname{val}) \to (\forall v : \operatorname{Fin} r , v . \operatorname{val} < i . \operatorname{val} \to \exists c , R v c \neq 0) \to R u b = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefix_outside_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.6 (prefix_width).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to \forall (\operatorname{hk} : 0 < k) , \forall (i : \operatorname{Fin} r) , (R i \langle 0 , \operatorname{hk}\rangle = 1) \to (\forall u : \operatorname{Fin} r , u . \operatorname{val} < i . \operatorname{val} \to \exists c , R u c \neq 0) \to i . \operatorname{val} + 1 \le k$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefix_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.7 (prefix_shift_column_sum).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to (0 < k) \to \forall (i : \operatorname{Fin} r) , (R i \langle 0\rangle = 1) \to (\forall u : \operatorname{Fin} r , u . \operatorname{val} < i . \operatorname{val} \to \exists c , R u c \neq 0) \to \forall (x : \operatorname{Fin} i . \operatorname{val}) , \operatorname{colSum} (\operatorname{topRows} (p := i . \operatorname{val}) R \mathord{\cdot}) (\operatorname{shiftCol} \mathord{\cdot} x) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefix_shift_column_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.8 (prefixSquare).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (i : \operatorname{Fin} r) , \forall (\operatorname{hp} : i . \operatorname{val} + 1 \le k) , \operatorname{prefixSquare} (r := r) (k := k) R i \operatorname{hp} : \operatorname{Matrix} (\operatorname{Fin} i . \operatorname{val}) (\operatorname{Fin} i . \operatorname{val}) \operatorname{SignType}\\\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (i : \operatorname{Fin} r) , \forall (\operatorname{hp} : i . \operatorname{val} + 1 \le k) , \operatorname{prefixSquare} (r := r) (k := k) R i \operatorname{hp} = (\operatorname{fun} u c \mapsto R (\operatorname{Fin} . \operatorname{castLE} \mathord{\cdot} u) (\operatorname{shiftCol} \mathord{\cdot} c))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefixSquare` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.9 (prefixSquare_isASM).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to (0 < k) \to \forall (i : \operatorname{Fin} r) , (R i \langle 0\rangle = 1) \to (\forall u : \operatorname{Fin} r , u . \operatorname{val} < i . \operatorname{val} \to \exists c , R u c \neq 0) \to \operatorname{IsASM} (\operatorname{prefixSquare} R i \mathord{\cdot})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefixSquare_isASM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.10 (prefixSquare_avoids).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{ExtAvoids312} R) \to \forall (i : \operatorname{Fin} r) , (i . \operatorname{val} + 1 \le k) \to \neg \operatorname{Contains312} (\operatorname{prefixSquare} R i \mathord{\cdot})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefixSquare_avoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.11 (below_prefix_interior_zero).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to \forall (\operatorname{hk} : 0 < k) , \forall (i v : \operatorname{Fin} r) , (R i \langle 0 , \operatorname{hk}\rangle = 1) \to (\forall u : \operatorname{Fin} r , u . \operatorname{val} < i . \operatorname{val} \to \exists c , R u c \neq 0) \to (i . \operatorname{val} \le v . \operatorname{val}) \to \forall (c : \operatorname{Fin} k) , (0 < c . \operatorname{val}) \to (c . \operatorname{val} < i . \operatorname{val}) \to R v c = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.below_prefix_interior_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.12 (pivot_not_one_at_prefix_end).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to \forall (\operatorname{hk} : 0 < k) , \forall (i : \operatorname{Fin} r) , (R i \langle 0 , \operatorname{hk}\rangle = 1) \to (\forall u : \operatorname{Fin} r , u . \operatorname{val} < i . \operatorname{val} \to \exists c , R u c \neq 0) \to (0 < i . \operatorname{val}) \to R i \langle i . \operatorname{val}\rangle \neq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.pivot_not_one_at_prefix_end` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.13 (pivot_no_minus_after_prefix).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to \forall (\operatorname{hk} : 0 < k) , \forall (i : \operatorname{Fin} r) , (R i \langle 0 , \operatorname{hk}\rangle = 1) \to (\forall u : \operatorname{Fin} r , u . \operatorname{val} < i . \operatorname{val} \to \exists c , R u c \neq 0) \to \forall (c : \operatorname{Fin} k) , (i . \operatorname{val} < c . \operatorname{val}) \to R i c \neq - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.pivot_no_minus_after_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.14 (first_column_zero_except_pivot).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to \forall (\operatorname{hk} : 0 < k) , \forall (i : \operatorname{Fin} r) , (R i \langle 0 , \operatorname{hk}\rangle = 1) \to \forall v , R v \langle 0\rangle = \operatorname{if} v = i \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.first_column_zero_except_pivot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.15 (below_pivot_end_not_minus).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to \forall (\operatorname{hk} : 0 < k) , \forall (i v : \operatorname{Fin} r) , (R i \langle 0 , \operatorname{hk}\rangle = 1) \to (\forall u : \operatorname{Fin} r , u . \operatorname{val} < i . \operatorname{val} \to \exists c , R u c \neq 0) \to (0 < i . \operatorname{val}) \to (i . \operatorname{val} < v . \operatorname{val}) \to R v \langle i . \operatorname{val}\rangle \neq - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.below_pivot_end_not_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.16 (pivot_row_singleton_if_no_minus).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to (0 < k) \to \forall (i : \operatorname{Fin} r) , (R i \langle 0\rangle = 1) \to (\forall u : \operatorname{Fin} r , u . \operatorname{val} < i . \operatorname{val} \to \exists c , R u c \neq 0) \to (R i \langle i . \operatorname{val} , \mathord{\cdot}\rangle \neq - 1) \to \forall c , R i c = \operatorname{if} c . \operatorname{val} = 0 \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.pivot_row_singleton_if_no_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.17 (pivot_row_right_singleton).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASR} R) \to (\operatorname{ExtAvoids312} R) \to (0 < k) \to \forall (i : \operatorname{Fin} r) , (R i \langle 0\rangle = 1) \to (\forall u : \operatorname{Fin} r , u . \operatorname{val} < i . \operatorname{val} \to \exists c , R u c \neq 0) \to (R i \langle i . \operatorname{val} , \mathord{\cdot}\rangle = - 1) \to \exists q : \operatorname{Fin} k , i . \operatorname{val} < q . \operatorname{val} \land (\forall c : \operatorname{Fin} k , i . \operatorname{val} < c . \operatorname{val} \to R i c = \operatorname{if} c = q \operatorname{then} 1 \operatorname{else} 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.pivot_row_right_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.below_pivot_end_not_minus`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.below_prefix_interior_zero`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.ends_restrict`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.first_column_zero_except_pivot`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.line_restrict`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.pivot_no_minus_after_prefix`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.pivot_not_one_at_prefix_end`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.pivot_row_right_singleton`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.pivot_row_singleton_if_no_minus`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefixSquare`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefixSquare_avoids`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefixSquare_isASM`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefix_first_column_zero`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefix_outside_zero`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefix_shift_column_sum`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.prefix_width`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry.shiftCol`
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction](EmptyRowFillingConstruction.md)
