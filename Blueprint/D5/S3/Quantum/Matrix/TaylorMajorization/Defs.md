# Taylor coefficients and weak majorization

## Abstract

Ordered Taylor coefficients and spectral comparison.

**Definition 1.1 (Ordered Taylor coefficients).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorQ`

*Formalization.* `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorQ` (`✓ std3`).

*Citation.* T. Zhang (2026). *Weak majorization inequalities for the cubic and quartic coefficients of e^{(A+B)t} versus e^{At}e^{Bt}*. DOI: [10.48550/arXiv.2601.07286](https://doi.org/10.48550/arXiv.2601.07286). URL: <https://arxiv.org/abs/2601.07286>.

*Commentary.*

Q at order k is the sum of choose(k,p) times A to the p times B to the k-p, for p from zero to k.

**Definition 1.2 (Hermitian Taylor coefficients).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorR`

*Formalization.* `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorR` (`✓ std3`).

*Citation.* T. Zhang (2026). *Weak majorization inequalities for the cubic and quartic coefficients of e^{(A+B)t} versus e^{At}e^{Bt}*. DOI: [10.48550/arXiv.2601.07286](https://doi.org/10.48550/arXiv.2601.07286). URL: <https://arxiv.org/abs/2601.07286>.

*Commentary.*

R at order k is the Hermitian part (Q+Q*)/2 of the ordered coefficient.

**Definition 1.3 (Spectral weak majorization).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.weakMaj`

*Formalization.* `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.weakMaj` (`✓ std3`).

*Citation.* T. Zhang (2026). *Weak majorization inequalities for the cubic and quartic coefficients of e^{(A+B)t} versus e^{At}e^{Bt}*. DOI: [10.48550/arXiv.2601.07286](https://doi.org/10.48550/arXiv.2601.07286). URL: <https://arxiv.org/abs/2601.07286>.

*Commentary.*

Weak majorization compares all initial sums of the nonincreasing real eigenvalue lists. The empty sum at r=0 is an automatic equality; positive lengths up to the matrix dimension give the source comparison.

**Definition 1.4 (The unrestricted comparison).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.claim`

*Formalization.* `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.claim` (`✓ std3`).

*Citation.* T. Zhang (2026). *Weak majorization inequalities for the cubic and quartic coefficients of e^{(A+B)t} versus e^{At}e^{Bt}*. DOI: [10.48550/arXiv.2601.07286](https://doi.org/10.48550/arXiv.2601.07286). URL: <https://arxiv.org/abs/2601.07286>.

*Commentary.*

For every positive dimension, every Hermitian A and B and every natural order k at least five, the eigenvalues of (A+B) to the k are weakly majorized by those of R at order k. No positivity assumption is imposed.

**Definition 1.5 (The real trace defect).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.defect`

*Formalization.* `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.defect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* T. Zhang (2026). *Weak majorization inequalities for the cubic and quartic coefficients of e^{(A+B)t} versus e^{At}e^{Bt}*. DOI: [10.48550/arXiv.2601.07286](https://doi.org/10.48550/arXiv.2601.07286). URL: <https://arxiv.org/abs/2601.07286>.

*Commentary.*

The defect is the real trace of R minus the real trace of (A+B) to the k. A strictly negative defect contradicts the full spectral comparison.

**Theorem 1.6 (Hermitian Taylor coefficients).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorR_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorR_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Zhang (2026). *Weak majorization inequalities for the cubic and quartic coefficients of e^{(A+B)t} versus e^{At}e^{Bt}*. DOI: [10.48550/arXiv.2601.07286](https://doi.org/10.48550/arXiv.2601.07286). URL: <https://arxiv.org/abs/2601.07286>.

*Commentary.*

The Hermitian part R is Hermitian at every order, so its sorted real eigenvalues are defined.

**Theorem 1.7 (The full spectral sum is the trace).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.weakMaj_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.weakMaj_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Zhang (2026). *Weak majorization inequalities for the cubic and quartic coefficients of e^{(A+B)t} versus e^{At}e^{Bt}*. DOI: [10.48550/arXiv.2601.07286](https://doi.org/10.48550/arXiv.2601.07286). URL: <https://arxiv.org/abs/2601.07286>.

*Commentary.*

Weak majorization of the nonincreasing real eigenvalues of Hermitian X and Y implies that the real trace of X is at most that of Y. Take the initial sum of length n and directly apply the existing RHLinalg real-trace identity and eigenvalue-sum reindexing theorem.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.defect`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorQ`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorR`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorR_isHermitian`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.weakMaj`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.weakMaj_trace`
