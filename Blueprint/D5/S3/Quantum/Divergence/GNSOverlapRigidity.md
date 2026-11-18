# All-threshold overlap optimality and spectral moments

## Abstract

Original all-threshold normal-overlap optimality determines every complex continuous GNS moment.

**Definition 1.1 (The actual CFC overlap operator).**

Lean statement: `D5/S3/Quantum/Divergence/GNSOverlapRigidity.spectralOverlap`

*Formalization.* `D5/S3/Quantum/Divergence/GNSOverlapRigidity.spectralOverlap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a self-adjoint positive contraction C in the actual GNS commutant, spectralOverlap(C,t) is defined by the real continuous functional calculus of x |-> min(x,t(1-x)). It is the actual operator G_t used in the spectral theorem, not an assumed supplier or an abstract optimum.

**Theorem 1.2 (The actual spectral moment theorem).**

Lean statement: `D5/S3/Quantum/Divergence/GNSOverlapRigidity.spectral_moments_of_all_overlap_optima`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GNSOverlapRigidity.spectral_moments_of_all_overlap_optima` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be an arbitrary concrete von Neumann algebra on a possibly nonseparable Hilbert space. Let rho and sigma be positive continuous dual functionals with actual coefficient-series witnesses in the original concrete representation. Let F be an actual full NormalMomentFamily.Family for this fixed pair. The hypothesis is precisely that, for every t>0, the real mass overlap(F,t)(1) equals the existing normal-overlap supremum overlapValue(M,rho,sigma,t). The result includes zero, singular and unnormalized inputs.

Put psi=rho+sigma, let N be the actual commutant of its completed GNS representation, and let C be the constructed original coordinate. The continuous-moment correspondence produces an actual positive unital complex-linear map Z into N with Z(u)=C and K(Z(g))=J_F(g) for every complex continuous g. The actual vector functional phi(T)=<Omega,T Omega> is faithful on the positive cone of N.

Define m_t(x)=min(x,t(1-x)) and G_t=m_t(C) by the real continuous functional calculus inside N. Functional calculus gives 0<=G_t<=C and G_t<=t(I-C). Coefficient positivity and order preservation make K(G_t) a positive continuous dual functional below rho and t sigma. The public value_attained theorem bounds the mass of every such functional; it needs no additional coefficient-series premise for this bound. Consequently phi(G_t)<=overlapValue=phi(Z(m_t)).

For 0<s<1 put t=s/(1-s). The exact continuous-function identity m_t=u-(1+t)(u-s)_+ has its exact CFC counterpart G_t=C-(1+t)(C-sI)_+. Substituting both into the mass comparison and cancelling phi(C) gives phi(Z((u-s)_+))<=phi((C-sI)_+). The coefficient is negative before cancellation, so this is the upper hinge bound. These are the actual scalar CFC hinges of Z(u), derived from the original all-threshold hypothesis.

Apply PositiveMomentRigidity.exists_starAlgHom_of_scalar_hinges to the actual Z and the actual faithful phi on N. It yields a genuine complex StarAlgHom Phi on all complex continuous functions on [0,1], agreeing with Z on every function. Thus Phi(u)=C and K(Phi(g))=J_F(g) for every complex continuous g, with no square-equality premise. The real restriction of Phi and the real CFC homomorphism of C are continuous star homomorphisms agreeing on the interval coordinate, hence agree by uniqueness of continuous functional calculus. Therefore Phi(m_t)=G_t for every real t, and for t>0 the actual G_t attains the original overlap optimum.

The same original F is passed to GeneralConvexReverseTestAttainment.standard_posterior_realization. Its preparation Gamma is defined on the entire complex L1 space of the scalar Riesz measure of F. On every continuous input it equals K(Phi(g)); on every complex L1 input its output has an actual coefficient-series witness in the original Hilbert space and is order normal. It is positive on almost-everywhere nonnegative inputs, preserves the integral mass, has norm at most one, and prepares both original posterior moments rho and sigma. The coefficient-series assertion uses the existing concrete coefficient-space heredity and whole-L1 range theorems, not a presumed equivalence between order normality and coefficient series.

This theorem derives full spectral moments from genuine all-threshold optimum and retains the original complex-L1 preparation. It does not derive that optimum from a convex-cost equality, and does not establish the compressed-centralizer criterion or the full original classification. Normality of the GNS representation, complete positivity, Stinespring dilation, finite dimension, separability, faithful inputs and normalized states are absent from the assumptions.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/GNSOverlapRigidity.spectralOverlap`
- Truth anchor: `D5/S3/Quantum/Divergence/GNSOverlapRigidity.spectral_moments_of_all_overlap_optima`
- Dependency: [D5/S3/Quantum/Analysis/GNSMomentFamilies](../Analysis/GNSMomentFamilies.md)
- Dependency: [D5/S3/Quantum/Divergence/NormalOverlapCompatibility](NormalOverlapCompatibility.md)
