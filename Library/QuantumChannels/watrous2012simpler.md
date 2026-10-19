---
bibkey: watrous2012simpler
authors: John Watrous
year: 2012
title: Simpler semidefinite programs for completely bounded norms
doi: null
url: https://arxiv.org/abs/1207.5726v2
claim: Rectangular trace and spectral norms are dual, the Frobenius norm is self-dual, and root fidelity admits exact semidefinite and positive-definite variational formulations.
strata_touched: []
license: citation-only
triage: anchor
---

# Simpler semidefinite programs for completely bounded norms

Primary text: https://arxiv.org/pdf/1207.5726v2 .

Section 1, printed pp. 2–3, defines the rectangular trace, Frobenius and
spectral norms and states trace/spectral duality and Frobenius self-duality.
The fidelity convention is the unsquared quantity
$F(P,Q)=\|\sqrt P\sqrt Q\|_1$.

Section 2.1, printed pp. 5–6, gives the fidelity SDP, its strong duality,
the positive-definite infimum (6), and Alberti's product form in Theorem 3.
The discussion on p. 6 explicitly allows singular positive operands and
warns that an optimal dual need not be attained in that case. Lemma 2
gives the singular-compatible block contraction factorization.

The family-specific common-density and common-isometry reductions in
Sections 85–90 of
[recovery volume II](../../docs/develop/theory/AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES_II.md#85-the-three-environment-family-and-one-common-auxiliary-density)
apply these norm and fidelity interfaces. This source does not establish
their proposed geometry-specific constant $(1+1/\sqrt2)/2$.
