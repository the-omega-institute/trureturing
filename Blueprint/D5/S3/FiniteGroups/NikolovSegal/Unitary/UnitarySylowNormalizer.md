# Unitary Sylow Normalizer

## Abstract

Actual unitary sylow normalizer supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.

**Theorem 1.1 (normalizer preserves prefix).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer.normalizer_preserves_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer.normalizer_preserves_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prefix is preserved by a normalizer element, from the intrinsic unitary-root characterization rather than an assumed fixed flag.

**Theorem 1.2 (upper of normalizer).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer.upper_of_normalizer`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer.upper_of_normalizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The genuine SU normalizer has literal zero entries below the diagonal.

**Theorem 1.3 (mem normalizer iff upper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer.mem_normalizer_iff_upper`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer.mem_normalizer_iff_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact normalizer recognition for actual positive unitary U.

The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer.mem_normalizer_iff_upper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer.normalizer_preserves_prefix`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer.upper_of_normalizer`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowFlag](UnitarySylowFlag.md)
