# SquareASMDecomposition

## Abstract

SquareASMDecomposition for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Lemma 1.1 (cons_zero_line).**

$$\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{Alternates} a) \to (\operatorname{StartsOne} a) \to \operatorname{Alternates} (\operatorname{Fin} . \operatorname{cons} 0 a) \land \operatorname{StartsOne} (\operatorname{Fin} . \operatorname{cons} 0 a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.cons_zero_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.2 (cons_zero_ends).**

$$\forall (n : \mathbb{N}) , \forall (a : \operatorname{Fin} n \to \operatorname{SignType}) , (\operatorname{EndsOne} a) \to \operatorname{EndsOne} (\operatorname{Fin} . \operatorname{cons} 0 a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.cons_zero_ends` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Definition 1.3 (TopLeftFibre).**

$$\begin{aligned}\forall (r k d : \mathbb{N}) , \operatorname{TopLeftFibre} r k d : \operatorname{Type}\\\forall (r k d : \mathbb{N}) , \operatorname{TopLeftFibre} r k d = (\left\{R : \operatorname{Counted} (r + 1) (k + 1) (d + 1) | R . \operatorname{val} 0 0 = 1\right\})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.TopLeftFibre` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.4 (topLeftFibre_card).**

$$\forall (r k d : \mathbb{N}) , \operatorname{Nat} . \operatorname{card} (\operatorname{TopLeftFibre} r k d) = S r k d$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.topLeftFibre_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.5 (avoidingASM_card_schroder).**

$$\forall n , \operatorname{Nat} . \operatorname{card} (\operatorname{AvoidASM} (n + 1)) = \operatorname{Nat} . \operatorname{largeSchroder} n$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.avoidingASM_card_schroder` (`✓ std3`). ∎

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.6 (S_diagonal).**

$$\forall (d : \mathbb{N}) , (0 < d) \to (S d d d : \mathbb{Z}) = (\operatorname{Nat} . \operatorname{largeSchroder} (d - 1) : \mathbb{Z})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.S_diagonal` (`✓ std3`). ∎

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The square count is the large-Schröder number of index d − 1 for d > 0.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.S_diagonal`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.TopLeftFibre`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.avoidingASM_card_schroder`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.cons_zero_ends`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.cons_zero_line`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.topLeftFibre_card`
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition](SquareFirstColumnDecomposition.md)
