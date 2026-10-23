# Coefficient convolution as a beta mixture mean

## Abstract

Beta mixtures for coefficient convolutions with two first parameters.

**Definition 1.1 (Coefficient convolution).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution`

*Formalization.* `D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive real p, q and b, the nth convolution is the sum of c_k(p,b)c_(n-k)(q,b) for k from zero through n.

**Definition 1.2 (Uniform mixture density).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Mixture.mixtureDensity`

*Formalization.* `D5/S3/Analytic/IncompleteBetaShape/Mixture.mixtureDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The density is the uniform average, with weight 1/(n+1), of the beta densities with shapes p+k+1 and q+n-k+1. Their common total shape is p+q+n+2.

**Definition 1.3 (Common prefactor).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Mixture.mixtureFactor`

*Formalization.* `D5/S3/Analytic/IncompleteBetaShape/Mixture.mixtureFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prefactor K(c,n,b) is (n+1)Gamma(c+n+2b) divided by Gamma(b)^2 Gamma(c+n+2). Its first parameter is the sum c=p+q.

**Theorem 1.4 (Beta mixture representation).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution_eq_mixtureMean`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution_eq_mixtureMean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive p, q and b, the coefficient convolution equals K(p+q,n,b) times the integral of [y(1-y)]^(b-1) against the uniform beta mixture density on the unit interval. Each summand is evaluated by the beta integral with shapes p+b+k and q+b+n-k. Positivity of the parameters gives integrability even when the power weight is unbounded at the endpoints.

**Theorem 1.5 (Affine mixture identity).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Mixture.mixture_eq_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Mixture.mixture_eq_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive p and q, a measurable real test function integrable against the shifted beta mixture has the same mean under the affine variable s v + (1-s)u. Here v has beta shapes p,q, s has beta shapes p+q,n+2, and u is uniform on the unit interval. The joint density normalizer is Gamma(p)Gamma(q)Gamma(n+2)/Gamma(p+q+n+2).

The triangle coordinate integral identity, with x=s v and z=s(1-v) and Jacobian s, is restricted to the output rectangle. At fixed output y its domain becomes the rectangle 0<x<y and 0<z<1-y. Expanding (1-x-z)^n into the n+1 terms ((y-x)+(1-y-z))^n and evaluating each beta integral produces the uniform shifted beta density. Nonnegative integration establishes the measure identity, and integrability transfers it to real test functions.

**Theorem 1.6 (Beta mean of the averaged kernel).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution_eq_betaMean_H`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution_eq_betaMean_H` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient convolution at p,q equals K(p+q,n,b) times the beta mean of H(p+q,n,b), with mean shape (p+q)/2 and signed imbalance (p-q)/2. Boundedness of H controls the outer beta integral, and the nonnegative affine identity transfers this finiteness to the weighted mixture. Thus the identity includes the singular endpoint regime 0<b<1. The common prefactor and kernel depend on p,q only through their sum, allowing strict comparison by imbalance.

## References

- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution_eq_betaMean_H`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution_eq_mixtureMean`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Mixture.mixtureDensity`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Mixture.mixtureFactor`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Mixture.mixture_eq_affine`
- Dependency: [D5/S3/Analytic/IncompleteBeta/Comparison](../IncompleteBeta/Comparison.md)
- Dependency: [D5/S3/Analytic/IncompleteBetaShape/Defs](Defs.md)
- Dependency: [D5/S3/Analytic/IncompleteBetaShape/Kernel](Kernel.md)
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](../KummerRatio/BetaIntegral.md)
- Dependency: [D5/S3/Quantum/Measurement/QubitIncompatibilityProbability](../../Quantum/Measurement/QubitIncompatibilityProbability.md)
