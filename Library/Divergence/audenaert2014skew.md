---
bibkey: audenaert2014skew
authors: Koenraad M. R. Audenaert
year: 2014
title: Quantum Skew Divergence
doi: 10.1063/1.4901039
url: https://arxiv.org/abs/1304.5935v2
claim: "Theorem 14 bounds Holevo information by mixing entropy times the largest pairwise trace distance; the equiprobable binary case gives J₂(ρ,σ) ≤ ‖ρ−σ‖tr/2."
strata_touched:
  - D5/S3/Divergence/AudenaertBinaryHolevoBound
  - D5/S3/Quantum/Divergence/UmegakiBKMPath
  - D5/S3/Quantum/Divergence/UmegakiRareFlagBKM
  - D5/S3/Quantum/Divergence/UmegakiArithmeticBKM
  - D5/S3/Quantum/Divergence/UniversalCommonCenter
  - D5/S3/Quantum/Divergence/UniversalPositiveScalarizer
  - D5/S3/Quantum/Divergence/ScalarizerMatrixTransport
license: citation-only
triage: anchor
---

# Quantum Skew Divergence

## Verified locator

DOI: https://doi.org/10.1063/1.4901039

Source: https://arxiv.org/abs/1304.5935v2

Journal of Mathematical Physics 55, 112202. The arXiv metadata gives the journal
reference and DOI above. Theorem 14 states χ(E) ≤ H(p)t, where t is the largest
pairwise trace distance. Taking two equally weighted states and base-two
logarithms gives

J₂(ρ,σ) = S₂((ρ+σ)/2) − (S₂(ρ)+S₂(σ))/2 ≤ ‖ρ−σ‖tr/2.

The supporting Lean theorem proves this binary specialization in every finite
dimension, including singular states. Its analytic route uses the resolvent
representation of the matrix logarithm, the differential estimate underlying
Theorem 8, integration to the skew-divergence estimate of Theorem 9, and a
trace-preserving regularization with continuity of x log x at zero.

The repository also contains `D5/S3/Quantum/Divergence/UmegakiRareFlagBKM`,
which proves the rectangular finite-dimensional rare-flag asymptotic for the
actual Bochner logarithmic derivative. It is a support result for the
rare-reference route and does not prove the conditional Umegaki coefficient
bound, coefficient equality, or a literature-priority claim.

`UmegakiArithmeticBKM.arithmetic_inverse_pairing_eq_logDeriv` identifies
Re Tr(H adjoint logDeriv(Z,H)) with the integral over u in [0,1] of the native
Hilbert-Schmidt pairing of H with the inverse of
M_Z(u)=(1-u)L_Z+u R_Z. Its scope is every finite index type, including empty
types, positive definite complex Z, and arbitrary complex H. A coordinatewise
reciprocal candidate in Z's eigenbasis proves actual invertibility, including
both endpoints and repeated eigenvalues. The original rare-flag scalar kernel
evaluation and spectral trace expansion are reused; Bochner integrability and
finite-sum interchange connect the two representations. This formal assembly
is repository-derived support, not an originality claim attributed to the paper.

For arbitrary correlated finite quantum references, the faithful conditional
application assumes a uniform arithmetic-kernel bound
`q(TZ,TV,u) ≤ c q(Z,V,u)` for every complex direction with actual partial trace
zero, every `u ∈ [0,1]`, and positive definite `Z,TZ`, with unchanged `c ≥ 0`.
Here `T` is the canonical channel's actual reference action. For canonical
density-state endpoints `rho,sigma,T rho,T sigma` that are positive definite,
the application gives
`D_fin(T rho,T sigma)-D_fin(rho_R,sigma_R) ≤
c (D_fin(rho,sigma)-D_fin(rho_R,sigma_R))`, using the actual
`SupportAwareRelativeEntropy.finiteTraceLogRelativeEntropy` branch and native
partial-trace marginals. The amplified trace-preservation theorem proves the
input and output marginals coincide for both states.

The same-center residual has zero partial trace and identifies the difference
of joint and marginal inverse pairings. Canonical channel module covariance
comes from complex blockwise linearity. Native inverse continuity supplies
inner interval integrability; the ordinary `relativeEntropy_eq_integral_bkm`
is applied separately to the actual joint and marginal pairs, with the native
weighted BKM integrability and cancellation of trace corrections by
`trace_partialTraceRight`. Iterated integration keeps the weight `1-t` and
requires no Fubini exchange. The conditional block-family theorem does not
supply this correlated-reference application.

This application is a bind-only consequence of the existing analytic suppliers
and finite matrix normalization, not a new standalone mathematical declaration
or a result attributed to Audenaert. The uniform metric bound is an explicit
intermediate premise. Support removal, singular limits, rare-flag ratios and
the remaining coefficient comparisons are not established. Final coefficient
division still requires the original strictly positive finite denominator.
The all-finite Umegaki coefficient equality remains unproved; the open-problem
KPI remains zero.

The associated finite semidefinite supplier
`UniversalCommonCenter.exists_common_center_of_posDef_trace_inf_le` concerns
arbitrary complex A and Hermitian B on r times a, for finite r and nonempty
finite a. If every positive-definite weight Z bounds the scalar infimum of
Re Tr(Z (A-X tensor I)(A-X tensor I) adjoint) by Re Tr(Z B), then one general
complex center X makes B-(A-X tensor I)(A-X tensor I) adjoint positive
semidefinite. Empty reference carriers are included; B is not assumed positive.
The proof establishes the actual quadratic epigraph's convexity and closedness,
then uses Hermitian-matrix PSD self-duality and strict separation.

This common-center inference is derived from the supplied repository-first
assessment, not attributed to Audenaert's article. It is step 3 support for the
same Umegaki complete-versus-conditional contraction problem served by the BKM
path identity. The weighted quotient-duality bridge and final coefficient
comparison remain open. No originality or solution of
that original problem is asserted.

The actual selected-column inference is formalized in
`UniversalPositiveScalarizer.selected_column_joint_gram`. For finite nonempty
input and output carriers and an actual quantum channel, its universal
positive-definite trace-inf premise supplies one scalar family for the whole
matrix-unit basis. With the canonical Kraus isometry J, pi(A)=A tensor I_Env
and e=I-J J adjoint, vertically stack C_i=J adjoint pi(E_i)e and
D_i=Phi*(E_i)-x_i I. The conclusion is positivity of k C C adjoint-D D adjoint,
including k=0. The packed actual defect is proved equal to C C adjoint.
For a full matrix center X, the selected residual column is D, while the
other columns form R. The proof uses P P adjoint=D D adjoint+R R adjoint
and positivity of the latter remainder; it imposes no sparsity on X.

This inference is a repository construction using the finite common-center
supplier, not a result attributed to Audenaert's paper. The selected joint
Gram is consumed by `UniversalPositiveScalarizer.common_positive_state_scalarizer`,
which constructs one possibly singular positive trace-one `DensityState b`,
independent of the reference and joint input. For every finite reference,
including the empty carrier, and every complex joint matrix, its ordinary
unnormalized weighted partial-trace center is the same in both residual Gram
inequalities. The construction uses native rectangular Douglas factorization,
complex-linear trace duality, the singular polar factor, and the supported Gram
flip; no faithful-state, invertibility, unitary-polar, or dimension
normalization assumption is added.

`ScalarizerMatrixTransport` contains the finite Euclidean matrix transports
used by this construction, including the Hilbert direct-sum application of the
existing Douglas supplier. These transports are auxiliary to the common-state
theorem and carry no separate novelty claim.

This is an intermediate on the original route. The all-channel coefficient
theorem, its support and regularization steps, and the final ratio comparison
remain open; no literature-priority or open-problem resolution is asserted.
