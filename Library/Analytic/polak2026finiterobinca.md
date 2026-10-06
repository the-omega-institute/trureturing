---
bibkey: polak2026finiterobinca
authors: Robert Polak
year: 2026
title: A Finite Computer-Assisted Verification of Robin's Inequality via Colossally Abundant Profiles, with Exact Prime-Power Residual Dynamics
doi: 10.5281/zenodo.21808589
url: https://doi.org/10.5281/zenodo.21808589
claim: The preprint reports a finite Robin verification and an effective positive full-support core; the core applies at the selected critical source's own logarithmic clock, but does not bound its signed prime-error tail or prove RH.
strata_touched: []
license: citation-only
triage: anchor
---

# Finite CA-profile verification and the signed residual

The source is Robert Polak, Zenodo preprint, record
[21808589](https://doi.org/10.5281/zenodo.21808589), version 1.0.0, published
5 August 2026. The retrieved PDF has 37 pages and SHA-256
`9a118f1f0247872458fc9dfbc91dfe067df7bbeb162f46fc1ad11e64f7913b2d`.
The locators below use printed pages. The full-support identity,
Lemma 7, and Proposition 10 with its argument on pp.3–8 were inspected.
This is a primary-source applicability check, not a whole-paper proof audit,
independent rerun of its certificates, peer-review claim, or Lean verification.

## Finite theorem and residual interface

The preprint claims Robin's strict inequality for every

$$
5041\le n\le 10^{7.1\times10^{22}}.
$$

Its certificate exhausts 3,341,978 colossally abundant exponent profiles, uses an analytic prime-power reduction and a finite-height zero verification, and transfers certified CA endpoints to intervening integers by Robin's convexity proposition. The stated CA support computation reaches $1.64967\times10^{23}$.

After the finite theorem, the source derives exact prime-power cell and signed-triangular identities. Its exploratory event scan is explicitly separated from the finite proof: the universal eventwise target needed for an infinite Robin proof remains unproved.

## Directly reusable effective core

For a real $x\ge2$ and a full-support integer
$n=\prod_{p\le x}p^{a_p}$ with every $a_p\ge1$, write

$$
\begin{aligned}
\Delta(n)&=\gamma+\log\log\log n-\log\frac{\sigma(n)}n,\\
I_\psi(x)&=\int_x^\infty(\psi(t)-t)
              \frac{1+\log t}{t^2\log^2t}\,dt,\\
z(n,x)&=\frac{\log n-x}{x},\\
B_2(n,x)&=\log\left(1+\frac{\log(1+z(n,x))}{\log x}\right)
             -\frac{z(n,x)}{\log x},\\
R_{\rm core}(n,x)&=\frac{\log n-\vartheta(x)}{x\log x}
                   -\sum_{p\le x}\log(1-p^{-(a_p+1)}),\\
C_{\rm pp}(x)&=\frac{\psi(x)-\vartheta(x)}{x\log x}
             +\sum_{\substack{p\le x,\ m\ge2\\p^m>x}}\frac1{mp^m}.
\end{aligned}
$$

The logarithmic margin is defined when $n>e$; the critical-source
application below is entirely above 5040. Proposition 6, p.5, gives

$$
\Delta(n)=I_\psi(x)+B_2(n,x)+R_{\rm core}(n,x)-C_{\rm pp}(x).
$$

This is the same $I_\psi$ and positive kernel used in the
[Nicolas comparison](../ArithSums/nicolas2025comparison.md).
The paper denotes the margin by $\mathcal G(n)$; it is not the Gronwall
quotient $G(n)=\sigma(n)/(n\log\log n)$ used in the other source notes.

Define the paper's independent full-support minimum by

$$
\begin{aligned}
\Phi_{p,x}(a)&=(a-1)\frac{\log p}{x\log x}
                       -\log(1-p^{-(a+1)}),\\
D^*(x)&=\sum_{p\le x}\min_{a\in\mathbb Z_{\ge1}}\Phi_{p,x}(a)-C_{\rm pp}(x).
\end{aligned}
$$

Lemma 7 and Corollary 8, pp.6–7, give
$R_{\rm core}(n,x)-C_{\rm pp}(x)\ge D^*(x)>0$ without a CA,
GA1, GA2, or self-tangency premise. The minimization retains full support;
its activation rule is not the paper's CA-family activation rule.
Proposition 10, p.8, gives the effective, unbounded continuation

$$
\sqrt x\log x\,D^*(x)>\frac12
\qquad(x\ge56\,048\,351).
$$

That continuation uses the cited Dusart theta bound and the explicit
positive contributions from $\sqrt{2x}<p\le x$. It is separate from
the finite all-integer Robin theorem and needs no finite-height RH input
in the inspected argument. Its cited theta theorem is an external
premise; its original proof was not independently audited here.
The finite support sweep and the analytic continuation are reused,
not repeated computations or new reserve estimates.

## Boundary for FIB

This is a larger finite verification range, not a replacement for the FIB source bridge. The certificate is organized by CA exponent profiles and consecutive-CA interpolation, whereas the FIB family is specified by additive Zeckendorf windows or congruence classes. No result in the source maps those addresses to the certified CA profiles or supplies the same-integer signed residual estimate required by §250. The finite range can be cited as an external boundary check, but repeating its computation would be duplicate work and would not advance RH.
