---
slug: oeis-a262082-schulte-power-coefficient
bibkey: schulte2015a262082
doi: null
url: https://oeis.org/A262082
triage: open
motivation_gids:
  - D5/S1/Recurrence/Algebraic/SchulteImplicitQuadrinomialPowers
---

# Schulte's implicit-series power coefficients

For every positive n, the native equation is
P_n=1+X*P_n^n+X²*P_n^(2n)+X³*P_n^(3n).
The source formula is:

> B(m,n,k) = m/(n*k+m) * Sum_{j=0..k} (-2)^j*binomial(n*k+m,j)* binomial(3*n*k+3*m-2*j,k-j) for m > 0, n > 0, and k >= 0. (conjectured)

The complete target requires a unique integer formal power series solution
and this rational image of every coefficient of every positive power.
It includes k=0, both sum endpoints and unbounded k. The separate
lattice-path and logarithmic conjectures are outside this target.

## Derivation

Coefficient agreement below degree d is preserved by powers and products.
Multiplication by X increases agreement to degree d+1. The existing
normalized contraction theorem constructs the integer solution. Every
solution has constant coefficient one, giving unrestricted uniqueness.
Mapping integer coefficients into the rationals preserves the equation.

Put Q(t)=1+t+t²+t³ and U(y)=y*P_n(y^n). Then U=y*Q(U^n), and
[y^(nk+m)]U^m=[X^k]P_n^m. Apply the existing Lagrange theorem at
degree N=nk+m and power m, with factor Q(y^n). Expansion transports
its other coefficient from degree nk to degree k in Q(t)^N. The existing
A008287 expansion supplies the alternating sum. Its hypothesis k≤3N
follows from n≥1 and m≥1; N is nonzero. No positive lower bound on k
is used.

## Triage

This is an unfrozen source candidate, not a delivered external resolution.
Independent source fidelity and proof-shape evaluation, the public-result
escape audit, Scribe production and publication gates remain pending.
The intended proof shape is bind-only; every auxiliary theorem is consumed
by the final result. The proposed admission basis is the external named
problem exception under [#30449](https://github.com/the-omega-institute/trureturing/issues/30449).
No escape witness, new axiom or originality claim is asserted.

The same change of series applies to P=Q(X*P^n) when a polynomial
coefficient supplier is available. This is an untested successor candidate,
not another resolved problem.
