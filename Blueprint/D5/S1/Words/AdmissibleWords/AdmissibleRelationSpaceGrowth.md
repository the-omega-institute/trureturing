# Relation-Space Growth for Admissible Words

## Abstract

Full linear relations between admissible words have squared Fibonacci dimension and golden-ratio-squared growth.

**Theorem 1.1 (The relation-space dimension is a Fibonacci square).**

$$\forall n\in\mathbb{N}, \operatorname{dim}_C \operatorname{End}(H_n) = F_{n+2}^2.$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/AdmissibleRelationSpaceGrowth.admissible_relation_space_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H_n be the complex function space on the length-n Zeckendorf-admissible binary words. The existing admissible-word count gives dim H_n = F_(n+2), and the standard finrank formula for linear maps therefore gives dim End(H_n) = F_(n+2)^2.

**Theorem 1.2 (Consecutive relation spaces grow by the golden ratio squared).**

$$\lim_{n\to\infty} \frac{{\operatorname{dim} \operatorname{End}(H_{n+1})}}{{\operatorname{dim} \operatorname{End}(H_n)}} = \varphi^2.$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/AdmissibleRelationSpaceGrowth.admissible_relation_space_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After substituting the exact dimension formula, the consecutive ratio is the square of F_(n+3)/F_(n+2). Mathlib's Fibonacci ratio limit then yields the square of the golden ratio.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/AdmissibleRelationSpaceGrowth.admissible_relation_space_finrank`
- Truth anchor: `D5/S1/Words/AdmissibleWords/AdmissibleRelationSpaceGrowth.admissible_relation_space_growth`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](AdmissibleCount.md)
