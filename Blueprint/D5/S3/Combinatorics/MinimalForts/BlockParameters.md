# Feasible sequences in every residue

## Abstract

Feasible sequences in every residue

**Definition 1.1 (The growth base).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/BlockParameters.rate`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/BlockParameters.rate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The real growth base is exactly three halves.

**Definition 1.2 (Complete-block increment).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/BlockParameters.negativeIncrement`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/BlockParameters.negativeIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The actual increment is the natural logarithm of two thirds.

**Definition 1.3 (Octahedral increment).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/BlockParameters.positiveIncrement`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/BlockParameters.positiveIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The actual increment is the natural logarithm of four thirds.

**Definition 1.4 (Target slope).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/BlockParameters.slope`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/BlockParameters.slope` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The target slope equals six times log(3/2) minus log(9). The inequalities 9<(3/2)^6<12 place it strictly between zero and the positive increment.

**Definition 1.5 (Residue correction).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/BlockParameters.offset`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/BlockParameters.offset` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For r in Fin 6, including all six residues zero through five, the real correction is (r+3)log(3/2)-log(r+2).

**Theorem 1.6 (Feasible sequences in every residue).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/BlockParameters.residue_sequences`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/BlockParameters.residue_sequences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

There exist natural-valued x,y,z indexed by r in Fin 6 and every natural k, with x(r,k)+y(r,k)+z(r,k)=k at every index. For each residue the signed error x log(2/3)+z log(4/3)-k slope-offset(r) tends to zero along the entire natural sequence. No residue or finite prefix is discarded from the domain. This follows by applying the feasible-simplex approximation to the actual irrational logarithmic ratio and interior slope.

## References

- Truth anchor: `D5/S3/Combinatorics/MinimalForts/BlockParameters.negativeIncrement`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/BlockParameters.offset`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/BlockParameters.positiveIncrement`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/BlockParameters.rate`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/BlockParameters.residue_sequences`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/BlockParameters.slope`
- Dependency: [D5/S3/Combinatorics/MinimalForts/LogRotation](LogRotation.md)
- Dependency: [D5/S3/Combinatorics/MinimalForts/SimplexApproximation](SimplexApproximation.md)
