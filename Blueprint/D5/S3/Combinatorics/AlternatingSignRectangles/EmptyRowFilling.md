# EmptyRowFilling

## Abstract

EmptyRowFilling for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Definition 1.1 (FirstEmptyFibre).**

$$\begin{aligned}\forall (r k : \mathbb{N}) , \forall (j : \operatorname{Fin} (k + 1)) , \forall (\operatorname{hkr} : k < r) , \operatorname{FirstEmptyFibre} r k j \operatorname{hkr} : \operatorname{Type}\\\forall (r k : \mathbb{N}) , \forall (j : \operatorname{Fin} (k + 1)) , \forall (\operatorname{hkr} : k < r) , \operatorname{FirstEmptyFibre} r k j \operatorname{hkr} = (\left\{R : \operatorname{Counted} r k k | (\forall c , R . \operatorname{val} \langle j . \operatorname{val}\rangle c = 0) \land (\forall i : \operatorname{Fin} r , i . \operatorname{val} < j . \operatorname{val} \to \exists c , R . \operatorname{val} i c \neq 0)\right\})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling.FirstEmptyFibre` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted.

**Lemma 1.2 (firstEmptyFibre_card).**

$$\forall (r k : \mathbb{N}) , \forall (j : \operatorname{Fin} (k + 1)) , \forall (\operatorname{hkr} : k < r) , \operatorname{Nat} . \operatorname{card} (\operatorname{FirstEmptyFibre} r k j \operatorname{hkr}) = S j . \operatorname{val} k j . \operatorname{val} \cdot \operatorname{Nat} . \operatorname{choose} (r - j . \operatorname{val} - 1) (k - j . \operatorname{val})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling.firstEmptyFibre_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The implication holds for every parameter and sign matrix in the stated domains.

**Lemma 1.3 (S_col).**

$$\forall (r k : \mathbb{N}) , (0 < k) \to (k < r) \to (S r k k : \mathbb{Z}) = \sum_{j : \operatorname{Fin} (k + 1)} (S j . \operatorname{val} k j . \operatorname{val} : \mathbb{Z}) \cdot (\operatorname{Nat} . \operatorname{choose} (r - j . \operatorname{val} - 1) (k - j . \operatorname{val}) : \mathbb{Z})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling.S_col` (`✓ std3`). ∎

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

Proposition 4.3 (p. 8), obtained by filling the first empty row and choosing the remaining nonempty rows.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling.FirstEmptyFibre`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling.S_col`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling.firstEmptyFibre_card`
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction](EmptyRowFillingConstruction.md)
