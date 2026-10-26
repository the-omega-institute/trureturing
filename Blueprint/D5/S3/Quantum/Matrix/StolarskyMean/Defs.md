# Stolarsky means and class A

## Abstract

Stolarsky mean matrices and their positive eigenvalue count.

**Definition 1.1 (The Stolarsky mean).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Defs.stolarsky`

*Formalization.* `D5/S3/Quantum/Matrix/StolarskyMean/Defs.stolarsky` (`✓ std3`).

*Citation.* R. Bhatia and T. Jain (2016). *Mean matrices and conditional negativity*. DOI: [10.13001/1081-3810.3082](https://doi.org/10.13001/1081-3810.3082). URL: <https://journals.uwyo.edu/index.php/ela/article/view/1495>.

*Commentary.*

The mean has diagonal value a. At parameter zero it is the logarithmic mean, and at parameter one it is the identric mean. At other parameters it is the real power of the divided difference of the power function. Positivity assumptions are supplied by the theorems using this total real function.

**Definition 1.2 (A finite mean matrix).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Defs.stolarskyMatrix`

*Formalization.* `D5/S3/Quantum/Matrix/StolarskyMean/Defs.stolarskyMatrix` (`✓ std3`).

*Citation.* R. Bhatia and T. Jain (2016). *Mean matrices and conditional negativity*. DOI: [10.13001/1081-3810.3082](https://doi.org/10.13001/1081-3810.3082). URL: <https://journals.uwyo.edu/index.php/ela/article/view/1495>.

*Commentary.*

The matrix entry at i,j is the Stolarsky mean of the two members of the given real family.

**Definition 1.3 (The positive eigenvalue count).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Defs.numPosEig`

*Formalization.* `D5/S3/Quantum/Matrix/StolarskyMean/Defs.numPosEig` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real Hermitian matrix, count the strictly positive eigenvalues with multiplicities. The value for a non-Hermitian matrix is zero.

**Definition 1.4 (Class A).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Defs.InClassA`

*Formalization.* `D5/S3/Quantum/Matrix/StolarskyMean/Defs.InClassA` (`✓ std3`).

*Citation.* R. Bhatia and T. Jain (2016). *Mean matrices and conditional negativity*. DOI: [10.13001/1081-3810.3082](https://doi.org/10.13001/1081-3810.3082). URL: <https://journals.uwyo.edu/index.php/ela/article/view/1495>.

*Commentary.*

A matrix belongs to class A when all entries are strictly positive and exactly one eigenvalue is strictly positive.

**Definition 1.5 (The Stolarsky matrix assertion).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Defs.claim`

*Formalization.* `D5/S3/Quantum/Matrix/StolarskyMean/Defs.claim` (`✓ std3`).

*Citation.* R. Bhatia and T. Jain (2016). *Mean matrices and conditional negativity*. DOI: [10.13001/1081-3810.3082](https://doi.org/10.13001/1081-3810.3082). URL: <https://journals.uwyo.edu/index.php/ela/article/view/1495>.

*Commentary.*

Every positive family of nonzero size gives a class A matrix at every real parameter at least two. For every parameter from zero inclusive to two exclusive, some positive finite family gives a matrix outside class A.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Defs.InClassA`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Defs.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Defs.numPosEig`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Defs.stolarsky`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Defs.stolarskyMatrix`
