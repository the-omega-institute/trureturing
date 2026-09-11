# Motzkin Conjecture 3 refutation

## Abstract

The printed universal first equality chain of Conjecture 3 in arXiv:2502.21050v1 is false at r = 9, n = 1, and stays false under the charitable reading r >= 3.

Wang and Zhang, Hankel determinants for convolution powers of Motzkin numbers, arXiv:2502.21050v1, Conjecture 3, prints no lower bound on r. A context sentence on printed page 2 mentions r >= 3; the witness r = 9 satisfies that reading as well, so the refutation survives it. Theorem 9 reports that the conjectures hold for r <= 27; that report is not read as a hypothesis r > 27 on the conjecture. This module refutes the printed universal first chain and makes no claim that a narrower author-intended proposition is false.

**Theorem 1.1 (The printed universal first chain is false).**

Lean statement: `D5/S0/Certificates/MotzkinConjectureThreeRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/MotzkinConjectureThreeRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Motzkin sequence, its Cauchy convolution powers and the Hankel determinant are reused from the already frozen sibling module. At r = 9, n = 1 the printed chain would force H9 of the ninth convolution power to equal minus 256, while the kernel-checked value is plus 256. The determinant is obtained from an integer matrix product identity rather than a direct expansion of a nine by nine determinant. The second equality of the conjecture, the one carrying alpha, is not used as a premise. A bounded literature search on 2026-09-10 found no prior attestation of this sign counterexample; that reading is recorded in the Lean header and is not a priority claim.

## References

- Truth anchor: `D5/S0/Certificates/MotzkinConjectureThreeRefutation.result`
- Dependency: [D5/S0/Certificates/MotzkinConvolutionHankelRefutation](MotzkinConvolutionHankelRefutation.md)
