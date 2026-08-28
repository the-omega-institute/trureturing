# Completion Signature Covariance

## Abstract

Completion points, their problem-isomorphism class, and Gaussian self-duality covary under coordinate change.

**Theorem 1.1 (Completion signatures covary under coordinate change).**

$$\begin{aligned}\alpha: A \equiv APrime,&\\\forall a, a \in \mathcal{N} \Leftrightarrow \alpha(a) \in \mathcal{NPrime},&\\\forall a, \Delta(a) = 0_{D} \Leftrightarrow \Delta'(\alpha(a)) = 0_{DPrime}&\\\longrightarrow \alpha_{K(C)}: K(C) \equiv K(CPrime)&\\\land \operatorname{IsoClass}(C) = \operatorname{IsoClass}(CPrime)&\\\land S \neq \operatorname{id}&\\\land \mathcal{F}_{std}(g_{std}) = g_{std}&\\\land \mathcal{F}_{ang}(g_{ang}) = g_{ang}&\\\land g_{std} \neq g_{ang}&\\\land \exists \phi: \operatorname{Fix}(\mathcal{F}_{std}) \equiv \operatorname{Fix}(\mathcal{F}_{ang}), \phi(g_{std}) = g_{ang}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CompletionConstants/CompletionSignatureCovariance.completion_signature_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C and CPrime be completion problems with the source seven-part carrier (A, X, D, F, Delta, N, G). A completion coordinate change consists of a parameter equivalence alpha together with exactly the two source conditions: alpha preserves membership in N if and only if, and it preserves zero structural defect if and only if. The completion-point type K(C) is the subtype of normalized parameters with zero defect.

The seven displayed conjuncts are the seven semantic assertions carried by the Lean theorem. First, alpha restricts to an equivalence between the two completion-point types. Second, C and CPrime determine the same class in the quotient by completion coordinate changes. This quotient is an isomorphism-class object, not a numerical cardinality.

Third, the Gaussian coordinate equivalence S is not the identity. Fourth and fifth, gStd and gAng are fixed respectively by the standard and angular Fourier operators. Sixth, the two coordinate formulas are different functions. Here gStd(x) is exp(-pi x^2), while gAng(x) is exp(-x^2/2); their inequality is witnessed concretely at x equal to one.

Seventh, there exists an equivalence Phi between the two Fourier fixed-point types which sends the standard Gaussian fixed point to the angular Gaussian fixed point. Thus the last clause records both the unchanged fixed-point structure and the identity of the transported Gaussian, rather than merely asserting that two unrelated types are equinumerous.

Pinned Mathlib supplies Equiv.subtypeEquiv for the completion-point restriction, Quotient.sound for the problem-isomorphism class, and fourier_gaussian_pi for standard Gaussian self-duality. The angular operator in Lean is exactly the conjugate of the standard operator by the explicit scale sqrt(2*pi). Its fixed-point covariance and the formula exp(-x^2/2) are transported through that coordinate equivalence; no independent explicit angular-kernel integral theorem is claimed.

## References

- Truth anchor: `D5/S3/Fourier/CompletionConstants/CompletionSignatureCovariance.completion_signature_covariance`
