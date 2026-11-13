# A counterexample to the Banerjee–Chaudhury stability conjecture

## Abstract

A strictly positive stochastic matrix and a positive semidefinite projection violate the proposed simultaneous stability interval.

The assertion is Conjecture 1.1 of Banerjee and Chaudhury, arXiv:2509.06715v1, https://arxiv.org/abs/2509.06715v1, licensed CC BY 4.0. The nonsymmetry convention is inherited from the paragraph preceding the conjecture. All matrices W and B are real square matrices of a common positive dimension. Their spectra are taken after entrywise inclusion into the complex numbers.

**Definition 1.1 (The finite real spectral radius).**

Lean statement: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.rho`

*Formalization.* `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n and real matrix A indexed by Fin n, rho A is (radius A).toReal, where radius A is spectralRadius over the complex numbers of A.map (algebraMap from the reals to the complex numbers). For n greater than zero, the complex spectrum is nonempty and compact. A spectral value z attains the largest modulus, radius A equals ENNReal.ofReal of the modulus of z, and rho A equals that modulus. Every spectral value w satisfies |w| ≤ rho A. Thus this real conversion is the finite maximum in the source definition, and does not discard an infinite value. The maximum argument uses spectrum.nonempty_of_isAlgClosed_of_finiteDimensional and spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty.

**Definition 1.2 (The first operator).**

Lean statement: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.P`

*Formalization.* `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, real n by n matrices W and B, and real t, P W B t = W (I − t B). Here I is the identity matrix and multiplication is matrix multiplication, with t B denoting real scalar multiplication.

**Definition 1.3 (The second operator and its domain).**

Lean statement: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.R`

*Formalization.* `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same arguments, R W B t = I − W + (I + t B)⁻¹ (2 W − I). The inverse is the matrix inverse. The assertion explicitly includes that I + t B is a unit, so that the total inverse operation is used on its genuine invertibility domain.

**Definition 1.4 (The stochastic and semidefinite hypotheses).**

Lean statement: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.Admissible`

*Formalization.* `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Admissible W B pi is the conjunction of the following conditions. W is nonsymmetric and belongs to the submonoid of nonnegative row-stochastic matrices, equivalently W has nonnegative entries and W e = e. W is primitive: its entries are nonnegative and there is a natural exponent k greater than zero such that every entry of W raised to k is strictly positive. B is nonzero, symmetric and positive semidefinite. Every entry of pi is strictly positive, the sum of its entries is one, and pi transposed times W equals pi transposed. These are the positive normalized left Perron eigenvector conditions for a primitive stochastic W. With e the all-ones vector, each component of B e is at most rho B, and pi transposed times B e is strictly positive. No entrywise nonnegativity condition is imposed on B.

**Definition 1.5 (The full simultaneous stability assertion).**

Lean statement: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.claim`

*Formalization.* `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposition claim states: for every natural n greater than zero, every pair of real matrices W and B indexed by Fin n and every real vector pi indexed by Fin n, Admissible W B pi implies that, for every real t with 0 < t < 2/(rho B), I + t B is a unit and both inequalities rho (P W B t) < 1 and rho (R W B t) < 1 hold. The maximum-modulus interpretation of rho applies to all these finite matrices, including nonsymmetric operators with nonreal spectral values. The unit condition makes the inverse domain explicit and is automatic: for nonnegative t, t B is positive semidefinite, so I + t B is positive definite and hence a unit. Consequently claim is equivalent to the universal assertion consisting of the two stability inequalities alone. This implication uses Matrix.PosDef.one, PosSemidef.smul, PosDef.add_posSemidef and PosDef.isUnit.

**Theorem 1.6 (The assertion is false).**

Lean statement: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem states the negation of claim. Take n = 4 and t = 9/5. Let W be 1/40 times the matrix with rows (37,1,1,1), (1,1,1,37), (1,1,1,37), (37,1,1,1). Let B be 1/3 times the matrix with rows (1,1,1,0), (1,1,1,0), (1,1,1,0), (0,0,0,3). Let pi = (176,5,5,14)/200. Every entry of W is strictly positive and every row sums to one, so it is primitive with exponent one. Its entries in positions (1,4) and (4,1) differ, so it is nonsymmetric. All entries of pi are positive, their sum is one, and pi transposed times W equals pi transposed.

The symmetric matrix B satisfies B squared = B and B transposed times B = B. Its positive semidefiniteness follows from Matrix.posSemidef_conjTranspose_mul_self applied to B and the latter identity. It is nonzero and B e = e. Idempotence puts its complex spectrum in {0,1}, and its eigenvector e has eigenvalue one. Consequently rho B = 1. Thus B e = (rho B)e and pi transposed times B e = 1. All hypotheses hold and 0 < 9/5 < 2/(rho B).

The inverse also exists at this parameter. For H = I − (9/14)B, direct multiplication gives (I + (9/5)B)H = I and H(I + (9/5)B) = I. These two identities exhibit a unit, and Matrix.inv_eq_right_inv identifies its matrix inverse with H.

For the nonzero complex vector x = (28,−19,−19,28), direct multiplication gives P W B (9/5) x = (27/25)x. The generic theorem LaplacianGapMinDegree.eigenpair_mem_spectrum puts 27/25 in the complex spectrum. The maximum-modulus bound then gives rho (P W B (9/5)) ≥ 27/25 > 1. This contradicts the first stability conjunct of claim and negates the full assertion. The argument asserts no instability of R and gives no classification of the broader stability problem.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.Admissible`
- Truth anchor: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.P`
- Truth anchor: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.R`
- Truth anchor: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.rho`
- Dependency: [D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation](AsynchronousIterationSpectralRadiusRefutation.md)
