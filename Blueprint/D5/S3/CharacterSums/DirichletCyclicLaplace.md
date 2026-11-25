# The actual cyclic character Laplace transform

## Abstract

The actual cyclic character Laplace transform

The selected length r may be any natural number at most the order of chi; all selected positive powers are nonprincipal.

Let chi be a Dirichlet character modulo a positive integer, and let r be at most its order. The cyclic family uses the actual Mangoldt ramp, the zeta remainder U, and the real parts of the nontrivial powers of chi. All integrals below converge absolutely when the real part of s exceeds one.

**Theorem 1.1 (The twisted Mangoldt transform).**

Lean statement: `D5/S3/CharacterSums/DirichletCyclicLaplace.characterRamp_half_plane_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletCyclicLaplace.characterRamp_half_plane_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The twisted von Mangoldt Dirichlet series gives the negative logarithmic derivative of the actual Dirichlet L-function, divided by s times (s minus one). Absolute convergence permits the series and integral to be exchanged. This identity applies to every character, including the principal one, for every s with real part greater than one. The integral is over positive y with kernel exp(-s y) and ramp evaluated at exp y.

**Theorem 1.2 (The full cyclic transform).**

Lean statement: `D5/S3/CharacterSums/DirichletCyclicLaplace.gl1CyclicFamily_half_plane_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletCyclicLaplace.gl1CyclicFamily_half_plane_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zeta term is its corrected logarithmic derivative. Each character contribution is one half of its transform at s plus the conjugate of its transform at conjugate s. The weights are one divided by three r plus one. This formula has no hypotheses about zeros, residues, or asymptotic estimates. More precisely, for r at most the order of chi and real part of s greater than one, the cyclic integrand is integrable on the positive y-axis, and its integral equals cyclicTransform chi s.

## References

- Truth anchor: `D5/S3/CharacterSums/DirichletCyclicLaplace.characterRamp_half_plane_laplace`
- Truth anchor: `D5/S3/CharacterSums/DirichletCyclicLaplace.gl1CyclicFamily_half_plane_laplace`
- Dependency: [D5/S3/CharacterSums/DirichletRampLaplace](DirichletRampLaplace.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane](../Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane.md)
