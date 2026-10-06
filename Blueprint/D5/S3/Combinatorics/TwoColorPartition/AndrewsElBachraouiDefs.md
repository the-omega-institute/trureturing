# Andrews and El Bachraoui Two-Color Partition Series

## Abstract

Finite truncations define the two-color partition series and their three sign statements.

**Definition 1.1 (Geometric coefficient series).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.geom`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.geom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For a natural number d, geom d is the integer power series whose coefficient at t is one when d divides t and zero otherwise.

**Definition 1.2 (Finite C-prime truncation).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.cTrunc`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.cTrunc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For natural numbers k, m and N, cTrunc k m N is the finite sum over j from zero through N of q raised to m times (2j+1), multiplied by the finite products with factors 1 minus q raised to the two prescribed even exponents and two geometric denominators.

**Definition 1.3 (Finite D-prime truncation).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.dTrunc`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.dTrunc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For natural numbers k, m and N, dTrunc k m N is the finite sum over j from zero through N of q raised to m times (2j+2), multiplied by the finite products with factors 1 minus q raised to the prescribed even exponents and two geometric denominators.

**Definition 1.4 (C-prime coefficients).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.cCoeff`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.cCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The coefficient cCoeff k m n is the coefficient of degree n in the truncation cTrunc k m n.

**Definition 1.5 (D-prime coefficients).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.dCoeff`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.dCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The coefficient dCoeff k m n is the coefficient of degree n in the truncation dTrunc k m n.

**Definition 1.6 (C-prime positivity statement).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.conjectureTwo`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.conjectureTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The statement conjectureTwo says that cCoeff 2 4 n is nonnegative for every natural number n.

**Definition 1.7 (D-prime positivity statement).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.conjectureThree`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.conjectureThree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The statement conjectureThree says that dCoeff 2 2 n is nonnegative for every natural number n.

**Definition 1.8 (D-prime exceptional signs).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.conjectureFour`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.conjectureFour` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The statement conjectureFour says that dCoeff 2 3 n is negative exactly when n is 10 or 22.

## References

- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.cCoeff`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.cTrunc`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.conjectureFour`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.conjectureThree`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.conjectureTwo`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.dCoeff`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.dTrunc`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.geom`
