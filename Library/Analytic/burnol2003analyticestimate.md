---
bibkey: burnol2003analyticestimate
authors: Jean-François Burnol
year: 2003
title: On an analytic estimate in the theory of the Riemann Zeta function and a Theorem of Baez-Duarte
doi: null
url: https://arxiv.org/abs/math/0202166v1
claim: Lemma 4.3 unconditionally identifies a damped Mobius fractional-part source on Re(s)>1; critical-line ratio control assumes RH, and the small-shift Hardy projection identity of Theorem 4.3 is RH-equivalent.
strata_touched: []
license: citation-only
triage: anchor
---

# Damped Mellin sources and the separate Hardy condition

The inspected primary version is [arXiv:math/0202166v1](https://arxiv.org/pdf/math/0202166v1), a nine-page preprint dated 18 February 2002. Its arXiv metadata gives the journal reference *Acta Cientifica Venezolana* 54 (2003), 210–215, and no DOI. The journal text was not separately inspected. Statements below use the preprint's numbering. The inspected statements are reused directly; no full proof audit or Lean certification is claimed.

## Unconditional source identification

Section 4 uses $\{t\}=t-\lfloor t\rfloor$ and

$$
f_\varepsilon(u)=\sum_{n\ge1}\mu(n)n^{-\varepsilon}
\left\{\frac1{nu}\right\},\qquad\varepsilon>0.
$$

Lemma 4.3, printed p.6, gives for $\Re s>1$

$$
\int_0^1 f_\varepsilon(u)u^{s-1}du
=\frac1{\zeta(1+\varepsilon)(s-1)}
-\frac{\zeta(s)}{s\zeta(s+\varepsilon)}.
$$

This identity supplies a damped arithmetic source, a rational principal part and a one-sided Mellin support relation. It does not require RH. Theorem 4.1, printed pp.6–7, identifies the critical-line $L^2$ Mellin transform under the additional hypothesis $f_\varepsilon\in L^2((0,\infty),du)$; that hypothesis cannot be omitted. Theorem 4.2 says square integrability for a positive shift sequence tending to zero implies RH.

## Conditions on critical-line transport

The paper's uniform critical-line bound for $\zeta(s)/\zeta(s+A)$ explicitly assumes RH. Theorem 4.3, printed pp.7–8, states an RH equivalence for the left Hardy projection identity of

$$
\frac{\zeta(s-\varepsilon/2)}{\zeta(s+\varepsilon/2)}
\frac1{s-\varepsilon/2},\qquad\Re s=1/2,
$$

for small positive shifts; a sequence tending to zero suffices. Its projection is the explicitly stated rational term on $\Re z<1/2$. This is a substantive support condition, not a consequence of the boundary modulus. The source's causality discussion explicitly distinguishes equal modulus from equal phase.

## Actual derivative-source parameter map

In the [FIB boundary calculation](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), §§404, 408, 411–413 use

$$
\mathscr G_\varepsilon(z)
=\frac{\mathcal B(z+\varepsilon)}{\mathcal B(z)}
\frac{-\zeta'(z)}{z\zeta(z+\varepsilon)}.
$$

Set $R_\varepsilon(z)=\zeta(z)/[z\zeta(z+\varepsilon)]$. On a domain where these functions are defined, the direct algebraic map is

$$
\mathscr G_\varepsilon(z)
=-\frac{\mathcal B(z+\varepsilon)}{\mathcal B(z)}
\left(\partial_z-\partial_\varepsilon+\frac1z\right)
R_\varepsilon(z).
$$

Burnol's $s$ maps to $z$ and his shift is the same $\varepsilon$. The displayed differential operator acts on $R_\varepsilon$, not on the $\mathcal B$ multiplier. This parameter adaptation is repo-derived algebra, not a new derivative theorem or source estimate. Transporting the Mellin source through derivatives requires control of the introduced logarithmic weights; the displayed identity supplies no such uniform estimate.

The FIB rational correction $Q_\varepsilon$ has a pole at $z=2$ even though its full weighted pairing is zero. A right-half-plane Hardy argument must separate that known rational component. For each fixed nontrivial zero $\rho$, all sufficiently small positive $\varepsilon$ preserve the pole at $z=\rho-\varepsilon$ with the original multiplicity; no common threshold over all zeros is asserted. Neither a null pairing nor a change of FIB coordinates proves the required holomorphy or the signed critical estimate.

The complete centered absolute norm and zero-damping boundary interface in §§411–413 are applications to the actual source with separately supplied domination. They are not statements printed in this paper. This note supplies the relevant existing Mellin/Hardy structure and its conditions; it supplies no unconditional proof of RH or full Robin.
