# InteriorRecurrence

## Abstract

InteriorRecurrence for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Lemma 1.1 (S_interior).**

$$\forall (r k d : \mathbb{N}) , (0 < d) \to (d < r) \to (d < k) \to (S r k d : \mathbb{Z}) = (S r (k - 1) d : \mathbb{Z}) + (S (r - 1) (k - 1) (d - 1) : \mathbb{Z}) + \sum_{i : \operatorname{CoeSort}.\operatorname{coe} (\operatorname{Icc} 2 d)} (\operatorname{Nat} . \operatorname{largeSchroder} (i . \operatorname{val} - 2) : \mathbb{Z}) \cdot ((S (r + 1 - i . \operatorname{val}) (k + 1 - i . \operatorname{val}) (d + 1 - i . \operatorname{val}) : \mathbb{Z}) - (\operatorname{Nat} . \operatorname{choose} (r - i . \operatorname{val}) (d + 1 - i . \operatorname{val}) : \mathbb{Z}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/InteriorRecurrence.S_interior` (`✓ std3`). ∎

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

Theorem 4.4 (pp. 8–9), combining the first-column and first-empty-row decompositions.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/InteriorRecurrence.S_interior`
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling](EmptyRowFilling.md)
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence](RowCompleteRecurrence.md)
