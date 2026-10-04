---
bibkey: "teschl2009mathematical"
authors: "Gerald Teschl"
year: 2009
title: "Mathematical Methods in Quantum Mechanics: With Applications to Schrodinger Operators"
doi: null
url: "https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf"
claim: "The maximal L2 multiplication domain is the strong derivative domain of its unitary exponential. For a finite complex Borel measure, Wiener's mean-square limit is the sum of squared atomic masses."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Maximal multiplication domains and physical modulation

Teschl, Graduate Studies in Mathematics 99, equation (2.21), printed pages 59-60, gives the maximal multiplication domain. Theorem 5.1(ii), printed pages 123-124, identifies the strong derivative domain of the unitary exponential with the domain of its self-adjoint generator. For the real multiplier A(x) = -(b dot x)/hbar, the convention U(t) = exp(-itA) gives positive modulation and derivative (i/hbar)(b dot x)f. These are known results, with this parameter correspondence.

## Physical modulation

For every natural number d, let E = EuclideanSpace Real (Fin d), with Lebesgue measure volume, and H = Lp Complex 2 volume. For every positive hbar, b in E, and f,v in H, let

```math
M_b(t)f=[x\mapsto e^{it\langle b,x\rangle/\hbar}f(x)].
```

The complete derivative graph is

```math
\operatorname{HasDerivAt}(t\mapsto M_b(t)f,v,0)
\iff
\exists h:\operatorname{MemLp}(x\mapsto\langle b,x\rangle f(x),2,\mathrm{volume}),\quad
v=\frac{i}{\hbar}\,h.\operatorname{toLp}(x\mapsto\langle b,x\rangle f(x)).
```

All directions, including zero, and all finite dimensions, including zero, are included. There is no finite-volume, global L1, Schwartz, or product-integrability premise on the derivative side.

Set a(x) = (b dot x)/hbar, z(x) = (b dot x)f(x), c = i/hbar, and k = cz. The quotient representative q_t(x) = t^(-1)(exp(it a(x))-1)f(x) converges pointwise to k. The phase derivative has norm |a(x)|, so |q_t(x)| is at most |k(x)| and |q_t(x)-k(x)| is at most 2|k(x)|. If z is square integrable, dominated convergence for the squared error proves convergence in the actual L2 norm and hence the derivative formula.

Conversely, a strong derivative v makes the quotient classes at t_n = 1/(n+1) converge to v in L2. Convergence in measure gives a strictly increasing subsequence converging almost everywhere. The countably many representative equalities hold together outside one null set. The scalar derivative forces the same subsequence to converge to k, so v=k almost everywhere. Thus k is in L2; since c is nonzero, z is in L2. The condition and toLp value are invariant under changes on null sets.

## Locator

https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf

Equation (2.21), printed pages 59-60; Theorem 5.1(ii), printed pages 123-124. The author-hosted file identifies the 2009 first edition, Graduate Studies in Mathematics volume 99. The online-use permission appears on its title page; this note cites the source and paraphrases the argument.

## Finite-measure Fourier mean squares

In the same retained first-edition PDF, Theorem 5.4, Section 5.2,
printed pp.126–127, equations (5.8)–(5.9), states Wiener's theorem for
every finite complex Borel measure $\mu$ on $\mathbb R$:

$$
\widehat\mu(t)=\int e^{-it\lambda}d\mu(\lambda),\qquad
\lim_{T\to\infty}\frac1T\int_0^T|\widehat\mu(t)|^2dt
=\sum_{\lambda\in\mathbb R}|\mu(\{\lambda\})|^2.
$$

The source uses the unnormalized angular transform, and the atomic sum
is finite. The inspected PDF SHA-256 is
`8dc8de0b58aa0a3fedfe594a345f9b5875322e5526ea581cb640a98d55b82818`;
its author-hosted title page dates the online text to 12 February 2009.
The source theorem is reused, without a new proof or priority claim.

For the project's real even finite signed prime-minus-continuum head,
the atoms are exactly $\pm\log n$, with masses $\Lambda(n)/\sqrt n$.
The negative continuous component has no atomic mass. The
[fixed-head scalar-budget application](../../docs/reports/theta-mixed-matrix/signed-low-row.md#fixed-head-band-expansion-has-a-classical-obstruction)
uses this same theorem to diagnose a frequency-envelope loss. It does
not assert growth of the actual weighted operator norm, an obstruction
to a growing arithmetic cutoff, or an RH/Robin conclusion. No compiled
project application is claimed.
