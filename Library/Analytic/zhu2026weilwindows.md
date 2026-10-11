---
bibkey: zhu2026weilwindows
authors: Xuefeng Zhu
year: 2026
title: "Weil positivity in compact windows: a finite reduction, certified two-sided bounds, and a Landau--Widom decay law"
doi: null
url: https://arxiv.org/abs/2608.24827v2
claim: The preprint certifies Weil-form positivity on a compact support window and maps the computational barrier for pointwise prime-comb envelopes; its fitted asymptotic law and conditional large-window statements do not prove RH.
strata_touched: []
license: citation-only
triage: anchor
---

# Weil positivity in compact windows

The inspected source is [arXiv:2608.24827v2](https://arxiv.org/abs/2608.24827v2),
revised 2 September 2026. This is a preprint report of certified interval
computations and analytic reductions; it is not a Lean verification or an
independent audit of the numerical certificate.

## Finite window result

For the normalized Weil quadratic form, let

$$
 \lambda_*(L)=
 \inf_{\operatorname{supp}f\subseteq[-L,L]}
 \frac{Q(f)}{\|f\|_2^2}.
$$

The source gives a one-stroke finite-matrix reduction and certifies

$$
 \lambda_*(0.8)\ge 8.9\times10^{-18}
$$

for arbitrary complex test functions (the corresponding autocorrelation
support is $1.6$). It also gives certified variational upper bounds and an
exploratory computation at a larger support. A negative value at any support
would disprove RH, while positivity at one fixed support is only a finite
fragment of the Weil criterion.

## The mapped barrier

Theorem 1.4 shows that the source's pointwise-envelope reduction requires a
frequency threshold

$$
 T_1(L)=2\pi e^{A_L},\qquad A_L=(4+o(1))e^L,
$$

and that the associated matrix and quadrature sizes grow doubly
exponentially with $L$. Lowering this threshold within the same certificate
class requires cancellation in the prime comb, rather than a sharper
pointwise envelope. The reported Landau--Widom profile is fitted to certified
upper-bound data; it is not used as an unconditional asymptotic theorem.

## Relation to the FIB boundary--bulk route

This source supplies a useful frontier diagnostic: finite positivity margins
can be certified, but the continuation to all windows is an arithmetic
cancellation problem. The FIB four-phase rotation and five-state recursion
have not been identified with the Weil test space or its prime comb. A
transport theorem would need to preserve the Hilbert-space quadratic form,
the support parameter, and the signed prime contribution. The finite window
certificate therefore cannot be reused as a global Robin or RH proof.
