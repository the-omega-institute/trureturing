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
  - D5/S3/Quantum/Divergence/PositiveKrausCompression
  - D5/S3/Quantum/Divergence/UmegakiConditionalBKM
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

For arbitrary correlated finite quantum references,
`UmegakiConditionalBKM.faithful_conditional_relativeEntropy_contraction`
derives contraction of the faithful conditional Umegaki divergence from the
uniform endpoint bound on the native inverse quadratic form at u = 0.
The endpoint hypothesis ranges over every finite reference, every positive
definite joint weight and every complex direction with zero partial trace.
The coefficient ranges over the closed unit interval. The channel image of
the input identity is assumed positive definite.

For c < 1 the endpoint estimate yields the universal positive trace-infimum
test at k = c/(1-c). Both common-state residual Gram estimates are used with
the same center. Two weighted Cauchy–Schwarz inequalities lift the estimate
to every arithmetic interpolation parameter. The zero-output form is
handled before division, and the ordinary contraction follows from the
uncentered estimate and the positive defect at c = 1.

The joint-minus-marginal inverse form equals the inverse form on a
zero-partial-trace residual. The amplified channel transports that residual
with the same marginal center, so separate integrations in the arithmetic
parameter and along the joint and marginal state paths give the inequality.
The four pairs lie in the finite support branch. Their individually
normalized traces cancel the trace corrections. The mathematical argument
uses the resolvent and path ingredients supported by this reference and
the repository's common positive state and matrix transport results.
Singular support removal, supported regularization and the full ratio
comparison remain open.

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
path identity. The final coefficient comparison remains open. No originality or solution of
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

`PositiveKrausCompression` contains the supported factor and its positive
trace-one replacement. Its rectangular Euclidean transport applies the existing
Hilbert-space Douglas theorem on a direct sum and extracts the appropriate
block. `UniversalPositiveScalarizer` amplifies the fixed replacement to give both
Gram bounds for every finite reference.

This is an intermediate on the original route. The all-channel coefficient
theorem, its support and regularization steps, and the final ratio comparison
remain open; no literature-priority or open-problem resolution is asserted.
