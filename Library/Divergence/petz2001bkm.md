---
bibkey: petz2001bkm
authors: Denes Petz
year: 2001
title: Covariance and Fisher information in quantum mechanics
doi: null
url: https://arxiv.org/abs/quant-ph/0106125
claim: The BKM metric is the resolvent trace form and pairs a tangent with the logarithmic differential in affine coordinates.
strata_touched:
  - D5/S3/Quantum/Divergence/MatrixLogResolventDerivative
license: citation-only
triage: anchor
---

# Logarithmic differential and the BKM form

## Verified locator

https://arxiv.org/abs/quant-ph/0106125

The full source was retrieved at
https://arxiv.org/html/quant-ph/0106125 and
https://arxiv.org/pdf/quant-ph/0106125. Section 3, equations (24) and (25),
and section 5, equations (28) and (29), were checked in the source.
Equation (24) names the resolvent trace form after Kubo, Mori, and Bogoliubov.
Equation (25) displays the inverse logarithmic-mean operator as a
resolvent sandwich integral. Equations (28) and (29) identify the affine
metric with the pairing against the logarithmic differential.

## Mathematical correspondence

For a positive definite density matrix D and self-adjoint tangents A,B,
equations (24) and (25) give

$$
K_D(A,B)=\int_0^\infty\operatorname{Tr}
 [A(D+tI)^{-1}B(D+tI)^{-1}]\,dt,
\qquad
\mathbb J_D^{-1}(B)=\int_0^\infty(D+tI)^{-1}B(D+tI)^{-1}\,dt.
$$

Equation (28) pairs the tangent with the derivative of log D; equation
(29) gives the same resolvent form in affine coordinates. Section 6
relates this metric to the mixed derivative of relative entropy. The
source's density manifold has trace-one base points and trace-zero
tangents. The repository's theorem is on arbitrary positive definite
matrices and all Hermitian directions, with the real part of the trace.
Its unrestricted trace-entropy Hessian follows from its own product and
chain rules and trace identity, rather than from an assertion that the
paper's manifold has this larger domain.

The classical formula is literature-attested. The uniform positive
neighborhood, dominated differentiation of actual CFC.log, half-line
integrability, and actual fderiv Hessian interface are repository-derived
proofs. No singular-base differentiation or sharp binary contraction
coefficient is supplied by this reference.
