---
bibkey: johansson2018ballintegration
authors: Fredrik Johansson
year: 2018
title: Numerical integration in arbitrary-precision ball arithmetic
doi: null
url: https://arxiv.org/abs/1802.07942v1
claim: Validated Petras integration combines adaptive subdivision and Gaussian quadrature with complex analytic magnitude bounds. Its bounded-path and holomorphic-callback contract supplies a reusable integration method, not a sign certificate for the mixed theta matrix.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Validated integration supplier and callback obligations

The inspected primary text is
[arXiv:1802.07942v1](https://arxiv.org/pdf/1802.07942v1), with SHA-256
`64abe78ce44e513bacf764e205f5f4eb728e6c6a0c79dc1a114b2cbfb44aae78`.
Printed pp.2–3 describe the Petras strategy and its callback contract;
pp.6–7 describe handling singularities by splitting, transformations and
separately bounded tails. The integration method is existing work and
is reused without an originality claim.

The accompanying API contract was inspected in
[FLINT v3.3.1, doc/source/acb_calc.rst](https://github.com/flintlib/flint/blob/v3.3.1/doc/source/acb_calc.rst),
with SHA-256
`c57859a8a3b05fd0dc95a4f8a3f2448f04d70e5655a83bf944faab1d6fcde171`.
This pins the inspected documentation; it does not identify the FLINT
version linked by any separately installed Python runtime.

## Finite directed enclosures

`acb_calc_integrate` encloses a straight-segment integral supplied by a
complex-ball callback. Finite endpoints and a bounded integrand on the
path are required for a finite result. Improper integrals therefore need
a regularizing substitution or a finite retained path together with an
independent tail bound.

An order-zero callback supplies a pointwise enclosure without a
regularity assumption. An order-one callback must also verify
holomorphicity on the requested complex enclosure, returning nonfinite
values when this fails. Meromorphic field expressions automatically
reject enclosed poles; branch-cut functions need explicit analytic
checks. A callback using a truncated theta series must enclose its
omitted summands uniformly on that same complex domain.

The documented Gauss rule on $[-1,1]$, for an integrand bounded by $M$
on a Bernstein ellipse of parameter $r>1$, has error at most

$$
M e_n(r),\qquad e_n(r)=\frac{64}{15(r-1)r^{2n-1}}.
$$

The algorithm combines this rule with direct interval enclosures and
adaptive bisection. Absolute and relative tolerances are targets; the
final enclosure must itself be inspected. Evaluation limits,
cancellation and accumulated subdivision errors can prevent the
requested final accuracy. An API success or a nominal working precision
does not independently certify a desired matrix sign.

## Use in the mixed theta form

The [actual theta matrix assembly](../Weil/jarohsweth2020local.md)
must regularize both same-cell diagonal cancellation and adjacent-cell
jump corners before invoking the bounded-path supplier. One-sided
rational branches preserve the jump terms. Complex callbacks use
polarized products of those real branches; complex absolute squares are
not holomorphic extensions.

For a bounded holomorphic integrand on a product of rescaled Bernstein
ellipses, successive application of the documented one-dimensional rule
gives a tensor rule on $[0,1]^2$ with error at most
$M[e_n(r)+e_m(s)]/2$. This is a standard application of the existing
quadrature bound. An adaptively evaluated inner integral does not by
itself satisfy the analytic contract of an outer callback; tensor rules,
parameter-uniform inner enclosures or interval-box integration are
needed instead.

Quadrature supplies entry enclosures. A simultaneous Loewner lower
matrix additionally needs correctly directed truncation, full-probability
centering and a coefficient-vector error bound. These separate
obligations are retained in the linked model note. No numerical theta
matrix, positive-semidefinite sign, computational feasibility, Lean
certification, RH or full Robin conclusion follows from this source
alone.
