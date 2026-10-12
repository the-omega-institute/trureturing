# Part IIUnitary Whole Graph Projective Product

## Abstract

The whole-SU and actual center-quotient PSU endpoints retain positive q, divisors e(j)|q, q/e(j), single N(q),C(q) before fields/ranks>=6 above the field cutoff, arbitrary genuine D/Phi/raw graph tuples and one right-inner correction before every actual target. The raw graph action on SU is identified with the supplied field involution. PSU is literally SU modulo its center; proved quotient surjectivity transports every quotient target. No arbitrary bare automorphism lifting or classification premise is introduced.

**Definition 1.1 (graphAction).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.graphAction`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.graphAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The raw graph is the anti-diagonal inverse transpose R(g), with entry R(g)(i,j) = g⁻¹(j.rev,i.rev). The defining SU fixed-point relation steinberg(ι)(g) = g gives ι(R(g)(i,j)) = g(i,j); applying the involution gives R(g)(i,j) = ι(g(i,j)). Thus graphAction uses ι.trans phi when eps is true and phi when eps is false. Both whole-group endpoints consume this genuine SU action; the raw graph bit, carrier, correction convention and divisor powers are preserved.

**Theorem 1.2 (actual uniform intrinsic whole graph q over e product).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.actual_uniform_intrinsic_whole_graph_q_over_e_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.actual_uniform_intrinsic_whole_graph_q_over_e_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual raw graph is absorbed into the genuine field component. No prescribed graph bit, divisor power, whole-SU target or global correction is discarded; the same uniform constants work for all graph tuples.

**Theorem 1.3 (actual uniform projective whole graph q over e product).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.actual_uniform_projective_whole_graph_q_over_e_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.actual_uniform_projective_whole_graph_q_over_e_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual center-quotient target is covered. The quotient action is constructed from the genuine SU action, and the quotient's surjectivity is proved library mathematics, rather than a bare-automorphism lift premise.

The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.actual_uniform_intrinsic_whole_graph_q_over_e_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.actual_uniform_projective_whole_graph_q_over_e_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct.graphAction`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicPrescribedProduct](PartIIUnitaryIntrinsicPrescribedProduct.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryProjectivePrescribedProduct](PartIIUnitaryProjectivePrescribedProduct.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholePrescribedProduct](PartIIUnitaryWholePrescribedProduct.md)
