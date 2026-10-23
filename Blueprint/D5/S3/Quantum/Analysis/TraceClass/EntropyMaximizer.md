# A global entropy center before compactness

## Abstract

Finite continuous entropy has a unique global maximum on a closed convex state family.

**Theorem 1.1 (Bounded entropy, attainment, uniqueness and the quadratic deficit).**

$$\forall H \in CompleteComplexHilbertSpace,\; \forall A \in \operatorname{Set}\left(\operatorname{TraceClass}\left(H\right)\right),\; \left(\operatorname{Nonempty}\left(A\right) \land \left(\operatorname{IsClosed}\left(A\right) \land \left(\operatorname{Convex}\left(Real, A\right) \land \left(\operatorname{AllPositiveTraceOne}\left(A\right) \land \left(\operatorname{AllFiniteSpectralEntropy}\left(A\right) \land \operatorname{ContinuousOn}\left(realEntropy, A\right)\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{BddAbove}\left(\operatorname{image}\left(realEntropy, A\right)\right) \land \left(\exists gamma \in \operatorname{TraceClass}\left(H\right),\; \operatorname{Mem}\left(gamma, A\right) \land \left(\operatorname{IsMaxOn}\left(realEntropy, A, gamma\right) \land \left(\left(\forall rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{Mem}\left(rho, A\right) \Rightarrow \operatorname{multiply}\left(\operatorname{divide}\left(1, 8\right), \operatorname{square}\left(\operatorname{norm}\left(\operatorname{subtract}\left(rho, gamma\right)\right)\right)\right) \le \operatorname{subtract}\left(\operatorname{realEntropy}\left(gamma\right), \operatorname{realEntropy}\left(rho\right)\right)\right) \land \left(\forall rho \in \operatorname{TraceClass}\left(H\right),\; \left(\operatorname{Mem}\left(rho, A\right) \land \operatorname{IsMaxOn}\left(realEntropy, A, rho\right)\right) \Rightarrow rho = gamma\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/EntropyMaximizer.exists_unique_entropy_maximizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be any complete complex Hilbert space and A a nonempty closed real-convex subset of its actual trace-class Banach space. Every rho in A is positive and has real trace one. Its existing singular spectralEntropy is finite, and the existing realEntropy is continuous relative to A in the trace norm. In the formula, AllPositiveTraceOne and AllFiniteSpectralEntropy express exactly these pointwise conditions. For a state rho, its Reference is formed from rho, its positivity and the contraction inequality derived from its actual trace. realEntropy is the real value of this finite spectralEntropy.

Positivity identifies the trace norm with the real trace, so every state has norm one and any pair has distance at most two. The actual realEntropy is nonnegative. Fix x in A. Relative continuity gives delta>0 such that any z in A within delta of x has entropy below realEntropy(x)+1. Set t=min(1/2,delta/4). For any y in A the state z=(1-t)x+ty lies in A and has distance at most 2t<delta from x. Weighted entropy concavity and nonnegativity yield t*realEntropy(y)<=realEntropy(z)<realEntropy(x)+1. Thus the single finite number (realEntropy(x)+1)/t bounds entropy on all of A. This argument uses relative continuity at one point and does not require an ambient interior.

The full weighted quantitative entropy inequality supplies StrongConcaveOn with modulus 1/2. The closed family is complete in the trace-class Banach norm, and relative continuity supplies upper semicontinuity. Applying StrongConcavityAttainment.exists_unique_maximizer with the newly derived bound gives an actual gamma in A, IsMaxOn realEntropy A gamma, the deficit norm(rho-gamma)^2/8<=realEntropy(gamma)-realEntropy(rho) for every rho in A, and equality of every other maximizer with gamma.

No separability, finite dimension, commutativity, faithfulness, compactness, energy bound or prior entropy bound is assumed. Kernel fibers are retained by the existing spectral entropy. The boundedness and attainment argument is a standard consequence of concavity, continuity and completeness. The original Shirokov common-reference and full all-temperature Hamiltonian conclusions require further constructions; this entropy center alone does not resolve those conjectures.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/EntropyMaximizer.exists_unique_entropy_maximizer`
- Dependency: [D5/S3/Analytic/Convexity/StrongConcavityAttainment](../../../Analytic/Convexity/StrongConcavityAttainment.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity](EntropyConcavity.md)
