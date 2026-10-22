# Taylor coefficients and weak majorization

## Abstract

Ordered Taylor coefficients and spectral comparison.

For complex Hermitian matrices A and B, Q at order k is the sum of choose(k,p) times A to the p times B to the k-p over p from zero to k. Its Hermitian part R is (Q+Q*)/2. The claim compares every initial sum of the nonincreasing eigenvalues of (A+B) to the k with the corresponding sum for R, for every positive dimension and every k at least five. The defect is the real trace of R minus the real trace of (A+B) to the k.

**Theorem 1.1 (Hermitian Taylor coefficients).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorR_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorR_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Hermitian part R is Hermitian at every order, so its sorted real eigenvalues are defined.

**Theorem 1.2 (The full spectral sum is the trace).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.weakMaj_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.weakMaj_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weak majorization of the nonincreasing real eigenvalues of Hermitian X and Y implies that the real trace of X is at most that of Y. Take the initial sum of length n and reindex the spectral trace identity along the equivalence used by the sorted eigenvalue API.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.taylorR_isHermitian`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Defs.weakMaj_trace`
