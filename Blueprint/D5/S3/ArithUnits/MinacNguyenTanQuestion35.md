# Exact sums of units with prescribed augmentation

## Abstract

The exact n-sum property with restricted augmentation transfers from a finite field to every finite group algebra.

**Definition 1.1 (Exactly n summands).**

$$\forall R \in Type,\; [\operatorname{AddCommMonoid}\left(R\right)], \forall S \in \operatorname{Set}\left(R\right),\; \forall n \in Nat,\; \operatorname{HasNSumProperty}\left(S, n\right) \Leftrightarrow \left(\forall r \in R,\; \exists a \in \operatorname{Function}\left(\operatorname{Fin}\left(n\right), R\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{a}\left(i\right) \in S\right) \land \operatorname{sum}\left(a\right) = r\right)$$

*Formalization.* `D5/S3/ArithUnits/MinacNguyenTanQuestion35.HasNSumProperty` (`✓ std3`).

*Citation.* Ján Mináč, Tung T. Nguyen, Nguyen Duy Tân (2026). *Sums of units in finite rings and applications to Cayley graphs*. URL: <https://arxiv.org/abs/2607.00404v1>.

*Commentary.*

For every element r there is a function a on Fin n, every value belongs to S, and the sum of all its values is r. Repetitions are allowed.

**Definition 1.2 (The standard coefficient-sum augmentation).**

$$\forall F \in Type,\; \forall G \in Type,\; [\operatorname{Field}\left(F\right)], [\operatorname{Group}\left(G\right)], \forall x \in \operatorname{MonoidAlgebra}\left(F, G\right),\; \operatorname{augmentation}\left(F, G, x\right) = \operatorname{supportSum}\left(\operatorname{coeff}\left(x\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/MinacNguyenTanQuestion35.augmentation` (`✓ std3`).

*Citation.* Ján Mináč, Tung T. Nguyen, Nguyen Duy Tân (2026). *Sums of units in finite rings and applications to Cayley graphs*. URL: <https://arxiv.org/abs/2607.00404v1>.

*Commentary.*

The algebra homomorphism is MonoidAlgebra.lift of the constant-one group homomorphism. Its value on a group-algebra element is the sum of its coefficients over the finite support; for a finite group this is also the sum over all group elements.

**Definition 1.3 (Units with augmentation in U).**

$$\forall F \in Type,\; \forall G \in Type,\; [\operatorname{Field}\left(F\right)], [\operatorname{Group}\left(G\right)], \forall U \in \operatorname{Subgroup}\left(\operatorname{Units}\left(F\right)\right),\; \forall v \in \operatorname{Units}\left(\operatorname{MonoidAlgebra}\left(F, G\right)\right),\; v \in \operatorname{augmentationUnitSubgroup}\left(F, G, U\right) \Leftrightarrow \operatorname{mapUnit}\left(\operatorname{augmentation}\left(F, G\right), v\right) \in U$$

*Formalization.* `D5/S3/ArithUnits/MinacNguyenTanQuestion35.augmentationUnitSubgroup` (`✓ std3`).

*Citation.* Ján Mináč, Tung T. Nguyen, Nguyen Duy Tân (2026). *Sums of units in finite rings and applications to Cayley graphs*. URL: <https://arxiv.org/abs/2607.00404v1>.

*Commentary.*

This is the preimage of U under Units.map of the standard augmentation. All summands are genuine units of the actual MonoidAlgebra.

**Theorem 1.4 (Question 3.5 has an affirmative answer).**

$$\forall F \in Type,\; \forall G \in Type,\; [\operatorname{Field}\left(F\right)], [\operatorname{Group}\left(G\right)], [\operatorname{Finite}\left(F\right)], [\operatorname{Finite}\left(G\right)], \forall U \in \operatorname{Subgroup}\left(\operatorname{Units}\left(F\right)\right),\; -1 \in U \Rightarrow \left(\forall n \in Nat,\; 2 < \operatorname{card}\left(F\right) \Rightarrow \left(2 \le n \Rightarrow \left(\operatorname{HasNSumProperty}\left(\operatorname{unitValues}\left(U\right), n\right) \Rightarrow \operatorname{HasNSumProperty}\left(\operatorname{unitValues}\left(\operatorname{augmentationUnitSubgroup}\left(F, G, U\right)\right), n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MinacNguyenTanQuestion35.result` (`✓ std3`). ∎

*Resolves.* `Problems/minac-nguyen-tan-question-3-5` (proved) by `D5/S3/ArithUnits/MinacNguyenTanQuestion35.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"minac-nguyen-tan-question-3-5","declaration_gid":"D5/S3/ArithUnits/MinacNguyenTanQuestion35.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ján Mináč, Tung T. Nguyen, Nguyen Duy Tân (2026). *Sums of units in finite rings and applications to Cayley graphs*. URL: <https://arxiv.org/abs/2607.00404v1>.

*Commentary.*

The finite field has more than two elements, U contains minus one, n is at least two, and the field has the exact n-sum property with respect to U. The conclusion uses the same n for every element of the actual finite group algebra. It includes modular characteristic, arbitrary noncommutative finite groups, characteristic two fields with more than two elements, and the trivial group. The Jacobson quotient is decomposed into finite matrix algebras. Orthogonal idempotents select the factor seen by augmentation; its injective map to F identifies its entries with scalars. The given field sums control that factor. Rank normal form and a scalar distinct from zero and one construct two units in every other factor; extra units give n summands. Quotient units lift through the nilpotent radical, and the sum error is added to one lift without changing any augmentation. Minus-one membership is retained as a source assumption; the proof does not need it.

## References

- Truth anchor: `D5/S3/ArithUnits/MinacNguyenTanQuestion35.HasNSumProperty`
- Truth anchor: `D5/S3/ArithUnits/MinacNguyenTanQuestion35.augmentation`
- Truth anchor: `D5/S3/ArithUnits/MinacNguyenTanQuestion35.augmentationUnitSubgroup`
- Truth anchor: `D5/S3/ArithUnits/MinacNguyenTanQuestion35.result`
