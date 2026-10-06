# Retained literal variables and fibre counting

## Abstract

Retained literal variables and fibre counting.

**Theorem 1.1 (solve extracted word retaining).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/ExtractionCounting.solve_extracted_word_retaining`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/ExtractionCounting.solve_extracted_word_retaining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The twisted PRODUCT input solves the original extracted word while preserving every unextracted variable and the final residual value.

**Theorem 1.2 (solution fibre card lower bound).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/ExtractionCounting.solution_fibre_card_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/ExtractionCounting.solution_fibre_card_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite variable and scalar types, actual restriction to the unextracted variables is surjective. The real literal-word solution fibre has cardinality at least |S| raised to (|V| minus 2D).

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/ExtractionCounting.solution_fibre_card_lower_bound`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/ExtractionCounting.solve_extracted_word_retaining`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/ExtractionResidual](ExtractionResidual.md)
