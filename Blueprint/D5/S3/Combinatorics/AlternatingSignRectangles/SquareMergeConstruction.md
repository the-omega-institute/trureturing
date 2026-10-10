# SquareMergeConstruction

## Abstract

SquareMergeConstruction for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Definition 1.1 (lowerIndex).**

$$\begin{aligned}\forall (p n : \mathbb{N}) , \forall (x : \operatorname{Fin} (p + n)) , \forall (\operatorname{hx} : p \le x . \operatorname{val}) , \operatorname{lowerIndex} (p := p) (n := n) x \operatorname{hx} : \operatorname{Fin} n\\\forall (p n : \mathbb{N}) , \forall (x : \operatorname{Fin} (p + n)) , \forall (\operatorname{hx} : p \le x . \operatorname{val}) , \operatorname{lowerIndex} (p := p) (n := n) x \operatorname{hx} = (\langle x . \operatorname{val} - p\rangle)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.lowerIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The dependent conditional binds hc as the branch proof of p ≤ c.val. The placeholder in lowerIndex u suppresses its certified proof argument; lowerIndex c hc retains the branch proof.

**Definition 1.2 (decCorner).**

$$\begin{aligned}\forall (s : \operatorname{SignType}) , \operatorname{decCorner} s : \operatorname{SignType}\\\forall (s : \operatorname{SignType}) , \operatorname{decCorner} s = (\operatorname{if} s = 1 \operatorname{then} 0 \operatorname{else} - 1)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.decCorner` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Definition 1.3 (incCorner).**

$$\begin{aligned}\forall (s : \operatorname{SignType}) , \operatorname{incCorner} s : \operatorname{SignType}\\\forall (s : \operatorname{SignType}) , \operatorname{incCorner} s = (\operatorname{if} s = - 1 \operatorname{then} 0 \operatorname{else} 1)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.incCorner` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.4 (incCorner_dec).**

$$\forall (s : \operatorname{SignType}) , (s \neq - 1) \to \operatorname{incCorner} (\operatorname{decCorner} s) = s$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.incCorner_dec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.5 (decCorner_inc).**

$$\forall (s : \operatorname{SignType}) , (s \neq 1) \to \operatorname{decCorner} (\operatorname{incCorner} s) = s$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.decCorner_inc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.6 (incCorner_cast).**

$$\forall (s : \operatorname{SignType}) , (s \neq 1) \to (\operatorname{incCorner} s : \mathbb{Z}) = (s : \mathbb{Z}) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.incCorner_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.7 (mergeRect).**

$$\begin{aligned}\forall (p r k : \mathbb{N}) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} p) (\operatorname{Fin} p) \operatorname{SignType}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{mergeRect} (p := p) (r := r) (k := k) M B : \operatorname{Matrix} (\operatorname{Fin} (p + r)) (\operatorname{Fin} (p + k)) \operatorname{SignType}\\\forall (p r k : \mathbb{N}) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} p) (\operatorname{Fin} p) \operatorname{SignType}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{mergeRect} (p := p) (r := r) (k := k) M B = (\operatorname{fun} u c \mapsto \operatorname{if} u . \operatorname{val} < p \operatorname{then} \operatorname{if} 0 < c . \operatorname{val} \land c . \operatorname{val} \le p \operatorname{then} M \langle u . \operatorname{val}\rangle \langle c . \operatorname{val} - 1\rangle \operatorname{else} 0 \operatorname{else} \operatorname{if} c . \operatorname{val} = 0 \operatorname{then} \operatorname{if} u . \operatorname{val} = p \operatorname{then} 1 \operatorname{else} 0 \operatorname{else} \operatorname{if} \operatorname{hc} : p \le \operatorname{val} c \operatorname{then} \operatorname{if} u . \operatorname{val} = p \land c . \operatorname{val} = p \operatorname{then} \operatorname{decCorner} (B (\operatorname{lowerIndex} u \mathord{\cdot}) (\operatorname{lowerIndex} c \operatorname{hc})) \operatorname{else} B (\operatorname{lowerIndex} u \mathord{\cdot}) (\operatorname{lowerIndex} c \operatorname{hc}) \operatorname{else} 0)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.8 (mergeRect_top).**

$$\forall (p r k : \mathbb{N}) , \forall (\operatorname{hk} : 0 < k) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} p) (\operatorname{Fin} p) \operatorname{SignType}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (u c : \operatorname{Fin} p) , \operatorname{mergeRect} M B (u . \operatorname{castAdd} r) (\operatorname{shiftCol} \mathord{\cdot} c) = M u c$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The placeholder in shiftCol suppresses the certified width inequality p + 1 ≤ p + k.

**Lemma 1.9 (mergeRect_first_col).**

$$\forall (p r k : \mathbb{N}) , (0 < k) \to \forall (M : \operatorname{Matrix} (\operatorname{Fin} p) (\operatorname{Fin} p) \operatorname{SignType}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (u : \operatorname{Fin} (p + r)) , \operatorname{mergeRect} M B u \langle 0\rangle = \operatorname{if} u . \operatorname{val} = p \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_first_col` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.10 (mergeRect_lower).**

$$\forall (p r k : \mathbb{N}) , (0 < p) \to \forall (M : \operatorname{Matrix} (\operatorname{Fin} p) (\operatorname{Fin} p) \operatorname{SignType}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \forall (u : \operatorname{Fin} r) , \forall (c : \operatorname{Fin} k) , \operatorname{mergeRect} M B (\operatorname{Fin} . \operatorname{natAdd} p u) (\operatorname{Fin} . \operatorname{natAdd} p c) = \operatorname{if} u . \operatorname{val} = 0 \land c . \operatorname{val} = 0 \operatorname{then} \operatorname{decCorner} (B u c) \operatorname{else} B u c$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.11 (mergeRect_isASR).**

$$\forall (p r k : \mathbb{N}) , (0 < p) \to \forall (\operatorname{hr} : 0 < r) , (0 < k) \to \forall (M : \operatorname{Matrix} (\operatorname{Fin} p) (\operatorname{Fin} p) \operatorname{SignType}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASM} M) \to (\operatorname{IsASR} B) \to (\exists c , B \langle 0 , \operatorname{hr}\rangle c \neq 0) \to \operatorname{IsASR} (\operatorname{mergeRect} M B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_isASR` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.12 (mergeRect_extAvoids).**

$$\forall (p r k : \mathbb{N}) , (0 < p) \to \forall (\operatorname{hr} : 0 < r) , (0 < k) \to \forall (M : \operatorname{Matrix} (\operatorname{Fin} p) (\operatorname{Fin} p) \operatorname{SignType}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASM} M) \to (\neg \operatorname{Contains312} M) \to (\operatorname{IsASR} B) \to (\operatorname{ExtAvoids312} B) \to (\exists c , B \langle 0 , \operatorname{hr}\rangle c \neq 0) \to \operatorname{ExtAvoids312} (\operatorname{mergeRect} M B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_extAvoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.13 (mergeRect_nonemptyRows).**

$$\forall (p r k : \mathbb{N}) , (0 < p) \to \forall (\operatorname{hr} : 0 < r) , (0 < k) \to \forall (M : \operatorname{Matrix} (\operatorname{Fin} p) (\operatorname{Fin} p) \operatorname{SignType}) , \forall (B : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , (\operatorname{IsASM} M) \to (\operatorname{IsASR} B) \to (\exists c , B \langle 0 , \operatorname{hr}\rangle c \neq 0) \to \operatorname{nonemptyRows} (\operatorname{mergeRect} M B) = p + \operatorname{nonemptyRows} B$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_nonemptyRows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.14 (all_rows_nonempty_iff).**

$$\forall (r k : \mathbb{N}) , \forall (R : \operatorname{Matrix} (\operatorname{Fin} r) (\operatorname{Fin} k) \operatorname{SignType}) , \operatorname{nonemptyRows} R = r \Leftrightarrow \forall u , \exists c , R u c \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.all_rows_nonempty_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.15 (asm_nonemptyRows).**

$$\forall (n : \mathbb{N}) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \operatorname{SignType}) , (\operatorname{IsASM} M) \to \operatorname{nonemptyRows} M = n$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.asm_nonemptyRows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.16 (square_count_isASM).**

$$\forall (n : \mathbb{N}) , \forall (M : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \operatorname{SignType}) , (\operatorname{IsASR} M) \to (\operatorname{nonemptyRows} M = n) \to \operatorname{IsASM} M$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.square_count_isASM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.all_rows_nonempty_iff`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.asm_nonemptyRows`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.decCorner`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.decCorner_inc`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.incCorner`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.incCorner_cast`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.incCorner_dec`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.lowerIndex`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_extAvoids`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_first_col`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_isASR`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_lower`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_nonemptyRows`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_top`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.square_count_isASM`
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry](SquarePrefixGeometry.md)
