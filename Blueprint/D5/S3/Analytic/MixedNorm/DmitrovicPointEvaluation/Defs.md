# Defs

## Abstract

Mixed norms and power-family point evaluations.

**Definition 1.1 (Circle integral means).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.circleMean`

*Formalization.* `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.circleMean` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Dmitrović (2024). *Norm of composition operator on mixed norm spaces*. DOI: [10.7153/oam-2024-18-42](https://doi.org/10.7153/oam-2024-18-42). URL: <https://doi.org/10.7153/oam-2024-18-42>.

*Commentary.*

For finite positive p the angular p-th powers are averaged over one full period and the p-th root is taken. At infinity the mean is the angular supremum.

**Definition 1.2 (Weighted radial mixed norms).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.mixedNorm`

*Formalization.* `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.mixedNorm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Dmitrović (2024). *Norm of composition operator on mixed norm spaces*. DOI: [10.7153/oam-2024-18-42](https://doi.org/10.7153/oam-2024-18-42). URL: <https://doi.org/10.7153/oam-2024-18-42>.

*Commentary.*

For finite positive q the q-th power integral uses density 2 alpha q r (1-r squared) raised to alpha q minus one. At infinity the norm is the supremum of the weighted angular means on radii strictly between zero and one.

**Definition 1.3 (The constant-one point evaluation conjecture).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.claim`

*Formalization.* `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Dmitrović (2024). *Norm of composition operator on mixed norm spaces*. DOI: [10.7153/oam-2024-18-42](https://doi.org/10.7153/oam-2024-18-42). URL: <https://doi.org/10.7153/oam-2024-18-42>.

*Commentary.*

Dmitrovic, Norm of composition operator on mixed norm spaces, Operators and Matrices 18 (2024), pages 697-710, doi:10.7153/oam-2024-18-42, conjectures this estimate on page 705. The parameters p and q range over positive extended nonnegative reals and alpha is positive. The function is holomorphic on the open unit disc and has finite mixed norm. The evaluation inequality is multiplied by the positive boundary weight. At p=infinity the reciprocal of p.toReal is zero.

## References

- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.circleMean`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.claim`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.mixedNorm`
