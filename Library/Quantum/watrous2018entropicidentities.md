---
bibkey: watrous2018entropicidentities
authors: John Watrous
year: 2018
title: The Theory of Quantum Information — spectral calculus, reductions and entropy
doi: null
url: https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf
claim: Spectral functional calculus, partial trace, isometric entropy invariance and the definition of mutual information give the coherent-copy marginals, Gibbs logarithm, uniform-reference entropy identity and unbiased-pinching account by explicit standard substitutions.
strata_touched:
  - D5/S3/Quantum/Information/CoherentCopyCorrelationTax
  - D5/S3/Quantum/Information/PartialTraceMutualInformation
  - D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity
  - D5/S3/Quantum/Divergence/GibbsVariationalIdentity
  - D5/S3/Quantum/Divergence/DualAccountFull
license: citation-only
triage: anchor
---

# Spectral calculus, reductions and entropy

## Verified locator

The exact upstream locator is:
https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf

The author-hosted pre-publication PDF (title page: copyright 2018 John
Watrous, “draft, pre-publication copy”) was retrieved and the following
interior passages read.
Page numbers below are printed pages, followed by one-based PDF pages.

- Section 1.1.2, p. 22 (PDF 30), equations (1.120)–(1.121):
  partial trace on a tensor product is Tr(X)Y or X Tr(Y).
- Section 1.1.3, p. 27 (PDF 35), equation (1.145):
  spectral functional calculus is f(A) = sum_k f(lambda_k) Pi_k.
- Section 2.1, p. 68 (PDF 76), equations (2.30)–(2.34):
  a subsystem state is the actual partial trace; (2.34) gives its entries.
- Definition 4.4, p. 203 (PDF 211), equations (4.7)–(4.8):
  pinching is Phi(A) = sum_j Pi_j A Pi_j, with sum_j Pi_j = I.
- Definition 5.17, pp. 265–266 (PDF 273–274), equations (5.82)–(5.84):
  entropy is the Shannon entropy of the eigenvalues, or -Tr(P log P),
  with the value of t log t at zero set to zero.
- Definition 5.18, p. 266 (PDF 274), equation (5.85):
  relative entropy is Tr(P log P) - Tr(P log Q) when im(P) is in im(Q).
- Section 5.2.1, p. 267 (PDF 275), equation (5.91):
  I(X:Y) = H(X) + H(Y) - H(X,Y).
- Proposition 5.19, p. 268 (PDF 276), equation (5.93):
  H(V P V*) = H(P) for an isometry, including singular positive P.
- Proposition 5.22, p. 269 (PDF 277): relative entropy of density
  operators is nonnegative (Klein's inequality).

The book uses base-two logarithms for entropy. Multiplication of its entropy
and relative entropy by ln(2) gives the repository's natural-log convention.
All entropy identities and inequalities below use nats. The exponential in
the Gibbs construction is the ordinary natural exponential.

## Coherent-copy entries, marginals and entropy

Set V|i> = |i,i>. Orthonormality gives V*V = I. Expansion in matrix units gives

    R = V rho V* = sum_{i,j} rho_ij |i><j| tensor |i><j|.

Consequently R_(i,i),(j,j) = rho_ij. This is the exact specialization behind
`coherentCopyState_correlated_entry`, not an assertion that Watrous names that
declaration. Applying (1.120)–(1.121), with Tr(|i><j|) = delta_ij, gives

    Tr_record R = sum_i rho_ii |i><i| = Delta(rho),
    Tr_system R = sum_i rho_ii |i><i| = Delta(rho).

These are `marginalRight_coherentCopyState` and
`marginalLeft_coherentCopyState`. The order of the retained subsystem is
explicit: marginalRight retains the first factor; marginalLeft the second.
Proposition 5.19 with this V gives `vonNeumannEntropy_coherentCopyState`.
Equivalently, V sends an eigenbasis of rho to orthonormal eigenvectors of R;
the orthogonal complement contributes only zero eigenvalues and zero entropy.

## Actual marginal mutual information and unitary invariance

`PartialTraceMutualInformation.quantumMutualInformation` is precisely (5.91),
with the subsystem states computed by (2.30) and (2.34). It is a definition
of a function of one joint state, not three independent entropy parameters.

`CorrelatedGibbsEnergyIdentity.von_neumann_entropy_unitary` is Proposition
5.19 specialized to a square unitary U. No full-rank assumption is needed.
The repository's proof obtains this equality by subtracting two previously
proved pinching identities; that implementation choice does not change the
standard mathematical statement or attribute that proof route to the book.

## Gibbs logarithm and the uniform reference

Let H = sum_k h_k Pi_k be Hermitian. By (1.145), exp(H) has eigenvalues
exp(h_k) > 0. Thus Z = Tr(exp H) > 0 and G = exp(H)/Z has eigenvalues
exp(h_k)/Z. Apply the scalar natural logarithm in the same spectral basis:

    log G = sum_k (h_k - ln Z) Pi_k = H - ln Z I.

This is `log_gibbs_state`, a direct spectral-calculus consequence, not a
separately located named Gibbs theorem. With Tr(rho) = 1, (5.83) and (5.85)
then give D(rho||G) = -S(rho) - Tr(rho H) + ln Z. No commutation between
rho and H is used. The reference G is full rank, so the support condition
in (5.85) always holds, even for singular rho.

For H = 0, exp(H) = I, Z = d and G = I/d. The same formula gives

    S(rho) + D(rho||I/d) = ln d.

This is `entropy_uniform_identity`. The existing citation attached to the
general `gibbs_variational_identity` is a separate entry and is not replaced.

## Unbiased pinching and the entropy/freedom segment

For rank-one projectors Z_j and X_k resolving I, write a Z-fixed density as
rho = sum_j p_j Z_j, p_j = Tr(Z_j rho), p_j >= 0 and sum_j p_j = 1.
The rank-one identity X_k A X_k = Tr(X_k A) X_k follows immediately by
writing X_k = |x_k><x_k|. Under the theorem's supplied overlap hypothesis
Tr(X_k Z_j) = 1/d, Definition 4.4 therefore gives

    Phi_X(rho) = sum_{j,k} p_j Tr(X_k Z_j) X_k
               = (sum_j p_j) (sum_k X_k)/d = I/d.

This calculation also covers d = 1. Put sigma = Phi_X(rho) and omega = I/d.
The uniform-reference identity gives

    sigma = omega,
    D(rho||sigma) = D(rho||omega) = ln d - S(rho),
    S(sigma) - S(rho) = D(rho||sigma),
    Phi_X(rho) = rho iff rho = omega.

These are exactly the conjuncts of `dual_account_full`. The last equivalence
is under the existing Z-fixed and unbiased hypotheses. No general assertion
that every measurement depolarizes a state is made.

For `entropy_freedom_segment`, eigenvalues p_i of a density obey
0 <= p_i <= 1 and sum_i p_i = 1, hence -sum_i p_i ln p_i >= 0.
Proposition 5.22 gives D(rho||omega) >= 0; the displayed uniform-reference
identity supplies S + D = ln d. This is a pointwise account for each state,
without a dynamical equation or a prescribed trajectory.

## What this note does and does not attest

Attested by this repository's own retrieval: the PDF and every interior
locator and formula listed above. The substitutions and finite-dimensional
algebra connecting them to the ten bound declarations are written out here
and checked against the current Lean statements. The PDF receipt is in the
stage-3 implementation report; no search-engine snippet is used as evidence.

Not attested here: a page-by-page comparison with the publisher's printed
edition, the book's historical source references, or earliest priority for
any consequence. Those historical attributions, if inferred, are
`ASSUMED-UNVERIFIED`. The book is cited for the stated definitions and
propositions; the copy construction and unbiased/Gibbs substitutions above
are explicit standard deductions, not quotations of same-named theorems.
