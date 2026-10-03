---
bibkey: connesconsanimoscovici2024semilocal
authors: Alain Connes, Caterina Consani, and Henri Moscovici
year: 2024
title: Zeta zeros and prolate wave operators — semilocal adelic operators
doi: null
url: https://arxiv.org/abs/2310.18423v2
claim: Dual semilocal maps preserve a mixed Hilbert pairing and identify Sonin spaces, while their entire-function norms and orthogonal grading depend on the place set. This transport does not supply an actual full Weil signed trace comparison.
strata_touched: []
license: citation-only
triage: anchor
---

# Dual semilocal transport and the signed trace interface

The inspected primary manuscript is [arXiv:2310.18423v2](https://arxiv.org/pdf/2310.18423v2), 4 May 2024, 30 pages, SHA-256 `8bc197642ee9ca4f2393b6cbfd3db292be6a315ce76ad61bfb845d9fedb47f2e`. The source results below are reused without reproving them, numerical reproduction, or new Lean declarations. Selected statement and proof inspection is not a complete proof audit.

## The two maps retain a joint relation

For a finite place set $S\ni\infty$, the source defines $H_\infty=L^2(\mathbb R)_{\rm ev}$ and $H_S=L^2(X_S)^{K_S}$ with its characters, Haar measures and unitary Mellin maps $U_\infty=\mathcal F_\mu w_\infty$ and $U_S=\mathcal F_\mu w_S$. The superscript denotes invariance under the source compact group, not a finite-dimensional approximation. Write $L_p(z)=(1-p^{-z})^{-1}$.

Proposition 4.1(i), equation (47), manuscript p.17, and Proposition 4.6(ii), equation (57), p.22, respectively give

$$
U_S\eta_S f(s)=
\prod_{p\in S\setminus\{\infty\}}L_p(1/2-is)\,U_\infty f(s),
$$

$$
U_S\theta_S f(s)=
\prod_{p\in S\setminus\{\infty\}}(1-p^{-1/2-is})\,U_\infty f(s).
$$

Proposition 4.7(iii), manuscript pp.22–23, states on the full even $L^2$ domain

$$
\langle\theta_S f,\eta_S g\rangle_{H_S}
=\langle f,g\rangle_{H_\infty}.
$$

This joint cancellation is stronger information than separate norm envelopes. Nonunitarity alone does not rule out a useful paired estimate. Conversely the displayed identity is a mixed pairing: it is not an assertion that either individual map preserves the norm or a positive quadratic form with an additional operator inserted.

## What is actually transported

Proposition 4.1(ii) and (iv) transports the support and Fourier-support cutoff **subspaces** under $\eta_S$. Proposition 4.7(i) intertwines $\theta_S$ with the physical Fourier transforms. Theorem 4.6, manuscript p.23, proves that

$$
\theta_S:\mathcal S_\lambda(\mathbb R,e_\infty)
\longrightarrow\mathcal S_\lambda(X_S,\alpha)
$$

is a bounded invertible Hilbertian isomorphism, where each Sonin space consists of physical functions vanishing, together with their Fourier transforms, on $\lvert x\rvert<\lambda$. These physical inputs are not arbitrary additive compact Weil tests. The theorem does not state that $\eta_S$ gives the same Sonin-space identification or that the isomorphism is unitary in the common unweighted norms.

Proposition 4.8 and §4.8, manuscript pp.23–24, identify the same entire-function vector space $B_\lambda$ under these maps. The paper explicitly records that $B_\lambda$ inherits **different inner products** from the embeddings for different $S$. An unchanged entire function therefore does not by itself retain its quadratic weight.

The grading obstruction is also explicit. Theorem 4.1(ii) transports the polynomial filtration, but Remark 4.2(i), manuscript p.19, states

$$
N_S\eta_S\ne\eta_SN_\infty\qquad(S\ne\{\infty\}).
$$

Its orthogonalization depends on $S$. Remark 4.2(iii), equation (50), also records

$$
\lvert\cdot\rvert_S^2\eta_S f
\ne\eta_S(\lvert\cdot\rvert^2 f).
$$

These are obstructions to those specified operator intertwinings. They do not refute RH or every possible joint transport estimate, and failure of the grading intertwining does not settle an alternative argument using only Sonin projections.

## The remaining comparison uses the same test and compression

The [archimedean source theorem](connesconsani2021archimedean.md) compares its Weil functional with a positive trace formed with an **orthogonal** Sonin projection. To transfer that proof one must account for the actual orthogonal projection in $H_S$, its $S$-dependent metric, and the resulting trace correction. An identification of subspaces or a dual bilinear identity is not the missing signed correction estimate. No claim that the projection cannot be transported is made here; its relevant comparison has not been obtained.

The target remains the project's [full common Weil form](frankliebseiringer2006hardy.md), including poles, prime powers and Gamma terms on one actual test. The maps above act on physical $L^2$ vectors; the multiplicative test used to integrate the scaling action is a different object. Applying $\theta_S$ to that test without a proved interface changes the problem.

A useful next supplier would preserve that same arithmetic form and bound the defect between it and the positive semilocal compressed trace, for a support family exhausting all admissible tests or for an already equivalent constrained criterion. The small prime-free archimedean bound, the source's operator candidate, and the [fixed-test trace remainder](connes1999trace.md) do not supply that defect bound. No actual full-Weil signed comparison or cofinal positivity has been established here; RH remains unproved.
