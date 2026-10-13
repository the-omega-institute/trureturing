# From doubled-space monotonicity to concavity

## Abstract

Operator order on a doubled Hilbert space implies continuous half-line concavity.

**Theorem 1.1 (Actual bounded operators and continuous functional calculus).**

Lean statement: `D5/S3/Quantum/Lieb/MonotoneBlockConcavity.monotone_double_space_concavity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/MonotoneBlockConcavity.monotone_double_space_concavity` (`✓ std3`). ∎

*Citation.* Frank Hansen (2013). *The fast track to Loewner's theorem*. DOI: [10.1016/j.laa.2013.01.022](https://doi.org/10.1016/j.laa.2013.01.022). URL: <https://arxiv.org/abs/1112.0098>.

*Commentary.*

Let H be any complete nontrivial complex Hilbert space. If f is continuous on the positive half-line and its actual continuous functional calculus preserves order on the two-fold Hilbert sum H + H, then (1-t) f(A) + t f(B) <= f((1-t) A + t B) for all strictly positive bounded operators A and B on H and every 0 <= t <= 1. This covers noncommuting operators, infinite dimensional H and infinite spectra. The premise asks for monotonicity only on the doubled space of the selected H; it does not require monotonicity on every Hilbert space.

A real unitary rotation exposes the desired mixture as the first corner of diag(A,B). For every epsilon > 0, a positive square factorization controls its off-diagonal block after adding epsilon I to that first corner and a sufficiently large scalar to the second. Actual operator monotonicity, functional-calculus naturality and positive corner compression give the perturbed concavity inequality. Continuity of functional calculus removes epsilon in operator norm.

This formalizes the block argument of Frank Hansen, The fast track to Loewner's theorem, arXiv:1112.0098v3, Theorem 2.1. Continuity remains an explicit hypothesis: Hansen's additional proof that matrix monotonicity itself excludes scalar jumps is not supplied here. No representing measure, analytic continuation or concavity is assumed. Automatic continuity, Bendat-Sherman and the unique Loewner measure remain separate unproved steps of the representation route. The result is classical; no mathematical literature novelty is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/MonotoneBlockConcavity.monotone_double_space_concavity`
- Dependency: [D5/S3/Quantum/Lieb/JensenOperatorInequalityIImpIV](JensenOperatorInequalityIImpIV.md)
