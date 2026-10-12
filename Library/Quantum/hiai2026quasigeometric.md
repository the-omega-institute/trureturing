---
bibkey: hiai2026quasigeometric
authors: Fumio Hiai
year: 2026
title: Log-majorizations between quasi-geometric type means for matrices
doi: null
url: https://arxiv.org/abs/2510.04691v3
claim: The tilde spectral trace uses a base-first weighted geometric mean; Problem 5.20 asks for its joint concavity parameter range.
strata_touched:
  - D5/S3/Quantum/Hiai
license: citation-only
triage: anchor
---

# Tilde spectral trace and its concavity question

Hiai's equations (2.1), (2.5), and (2.6), printed page 4, define

$$
X\#_\alpha Y=X^{1/2}(X^{-1/2}YX^{-1/2})^\alpha X^{1/2},
\qquad K=A^{-p}\#_\alpha B^p,
$$
$$
T_{\alpha,p}(A,B)=\operatorname{Re}\operatorname{Tr}
\left(K^{1/2}A^{2p(1-\alpha)}K^{1/2}\right)^{1/p}.
$$

All powers are spectral functional calculus. The first geometric-mean argument
is its base. For semidefinite inputs the source requires support(A) to contain
support(B); positive definite A satisfies this requirement even when B is a
rank-one projection. Proposition 5.19(1), printed page 33, gives p <= 1 as a
necessary condition for joint concavity. Problem 5.20 asks for sufficient
conditions away from the known midpoint alpha = 1/2.

The project result excludes every 0 < alpha < 1/2 and every p > 0 by a strict
first-variable Jensen violation with positive definite complex 2 by 2 inputs.
This is a partial parameter exclusion, including 0 < p <= 1; it does not
classify the upper-half weights or solve all of Problem 5.20.

For P = (1/2)[[1,1],[1,1]] and A = diag(x,1), x > 0, the boundary calculation is

$$
T_{\alpha,p}(A,P)=
\left[\left(\frac{1+x^p}{2}\right)^{\alpha-1}
\frac{1+x^{2p(1-\alpha)}}2\right]^{1/p}.
$$

Normalizing A to exponent p/2 times P times A to exponent p/2 gives a positive
semidefinite idempotent. Its positive powers justify this actual matrix
identity. A decreasing interval of the displayed function gives a strict
Jensen gap. Continuity of positive matrix powers on the semidefinite cone
preserves the same gap for P + epsilon I with one positive epsilon.

Jeong, Kim, and Tam, *New Weighted Spectral Geometric Mean and Quantum
Divergence*, https://arxiv.org/abs/2501.00287v1, Theorem 4.3, prove strict
concavity in the second variable for the p = 1 tilde operator. Their Remark 4.4
distinguishes the first variable. This does not supply the all-p first-variable
exclusion.

Vuong, Shudo, and Osaka, *Alternative-Mean Trace Divergences: Geometry, Data
Processing, and Barycenters*, https://arxiv.org/abs/2609.00034v1, classify a
different operator f(A inverse # B) A f(A inverse # B), based on an unweighted
transition. At f(x) = x to exponent t, its specialization is the untilde p = 1 family. Theorem 4.1 cannot
be substituted for the tilde functional without an additional identity.

The comparison is bounded to these inspected primary versions and the pinned
repository libraries. It is not a global novelty certification. The proof is
a project synthesis of rank-one functional calculus, elementary real
calculus, and continuity; Hiai supplies the object and open question, not this
exclusion theorem. The separate support and boundary-limit obligations for
Problem 5.18 remain outside this result.

## Verified locator

https://arxiv.org/abs/2510.04691v3

The cached v3 PDF has SHA256
517793e372e0d145619e517e7be0772e4852536ce65821cd5142e714e19e1a4b.
