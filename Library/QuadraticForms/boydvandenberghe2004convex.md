---
bibkey: boydvandenberghe2004convex
authors: Stephen Boyd and Lieven Vandenberghe
year: 2004
title: Convex Optimization
doi: null
url: https://web.stanford.edu/~boyd/cvxbook/
claim: The one-constraint S-procedure is exact for real quadratic implications under a strictly feasible constraint, and is equivalent to a nonnegative-multiplier matrix inequality.
strata_touched: []
license: citation-only
triage: anchor
---

# Convex Optimization

Author-hosted primary PDF:
https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf .

Appendix B.2, printed p. 655 (PDF p. 669), equations (B.6)–(B.7), states
the exact quadratic alternative and the equivalent S-procedure
implication. Its necessary hypothesis is a point at which the constraint
quadratic is strictly negative. It allows a nonnegative multiplier and
a positive-semidefinite, potentially singular, coefficient matrix.

[Recovery volume II, Proposition 87.3](../../docs/develop/theory/AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES_II.md#87-the-exact-common-block-quadratic-certificate-on-the-boundary)
uses the unit ball in the eight-dimensional real Frobenius space
$\mathcal L_2$. The origin is strictly feasible. In that application,
the constraint coefficients are $(I,0,-1)$ and the conclusion coefficients
are $(H,d/2,A-c)$; the difference after multiplication is the displayed
$9\times9$ PSD certificate. The S-procedure proves equivalence for each
fixed common triple. It supplies no universal feasible multiplier or
the numerical constant for the full family.
