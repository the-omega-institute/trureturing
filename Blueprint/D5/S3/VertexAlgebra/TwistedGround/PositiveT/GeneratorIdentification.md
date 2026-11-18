# Actual Positive Gaussian J/T Kernel Unit

## Abstract

Actual Positive Gaussian J/T Kernel Unit

Let r be real with 0<r<1, and let u,v be complex with norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1. The literal positive square-resolvent generator equals the analytic candidate, including both axes and the diagonal. The finite mode definitions and the original source amplitudes are unchanged.

The actual finite denominator coefficients obey norm(h(p,q,r)) <= (1+sqrt(r))^(p+q) and norm(h2(p,q,r)) <= (p+1)*(q+1)*(1+sqrt(r))^(p+q). Polynomial geometric majorants give absolute convergence before any rearrangement. Guarded successor reindexings turn the finite identities E*h=delta00 and E*h2=h into the sums 1/E and 1/E squared; the first identity also proves E is nonzero. A rectangular Cauchy product evaluates the actual finite source convolutions.

The summed expression retains both r*(1+(1-r)*u*v)/(2*E) and r squared*u*v/E squared, as well as the logarithmic derivative correction r*(1-r)*periodPrime/period. The consumed bind-only full unit-disk mode helper FiniteMode.OriginalGaussianFiniteCandidateModes.externalT_positive_finite_eq identifies every original positive mode at z=sqrt(r) with its finite coefficient. The equality then follows by equality of the actual sums. No extra summability, germ-equality or differentiability hypothesis is imposed. Together with the actual positive J kernel in FiniteMode.OriginalGaussianPositiveIdentification, this unit identifies both original positive generating kernels. Finite J mode extraction, other sign sectors, monodromy and operator completion remain outside this result; the broader VOA/CFT/string/AdS-CFT goal remains open.

**Theorem 1.1 (positiveT_hasSum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 0<r<1 and every complex u,v in the stated source bidisk, the family t(p,q,r)*u^p*v^q, indexed by all natural pairs, has sum OriginalGaussianExternalAnalyticCandidate.candidateT(u,v,r). Absolute convergence is derived from the actual finite h and h2 bounds and the original source generators.

**Theorem 1.2 (positiveT_eq_candidateT).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_eq_candidateT`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_eq_candidateT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 0<r<1 and complex u,v satisfying norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1, OriginalGaussianExternalGeneratedSource.kernelMode(true,true,true,u,v,sqrt(r)) equals OriginalGaussianExternalAnalyticCandidate.candidateT(u,v,r). The proof consumes positiveT_hasSum and the unconditional full unit-disk identity for the original positive modes. Zero coordinates and equal coordinates are included.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_eq_candidateT`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_hasSum`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianPositiveIdentification](../FiniteMode/OriginalGaussianPositiveIdentification.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate](../OriginalGaussianExternalAnalyticCandidate.md)
