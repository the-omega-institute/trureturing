---
bibkey: baezduarte2005mobiusconvolutions
authors: "Luis Báez-Duarte"
year: 2005
title: "Moebius-convolutions and the Riemann hypothesis"
doi: null
url: "https://arxiv.org/abs/math/0504402v1"
claim: "Section 2 records classical weighted Möbius growth and Littlewood's RH criterion; the Fibonacci harmonic weights use these existing tools without rederiving the criterion."
strata_touched: []
license: citation-only
triage: anchor
---

# Weighted Möbius sums and convolution

The primary version is [arXiv math/0504402v1](https://arxiv.org/abs/math/0504402v1),
published 2005-04-20. The manuscript identifies its text as 2004-11-22,
with comments added 2005-04-19. The arXiv record supplies no journal reference
or DOI. The original TeX abstract and Sections 1–2 were inspected; no claim
is made about the proofs or results in unread sections. No source text is
vendored.

In Section 2, write

\[
M(x)=\sum_{n\le x}\mu(n),\qquad
g_\mu(x)=\sum_{n\le x}\frac{\mu(n)}n.
\]

The source's equation labeled `growthMandg` states, for
\(\alpha\in[1/2,1)\),

\[
M(x)\ll x^\alpha\quad\Longleftrightarrow\quad
g_\mu(x)\ll x^{\alpha-1}.
\]

The same section records Littlewood's classical criterion
\(\mathrm{RH}\Longleftrightarrow
g_\mu(x)\ll_\varepsilon x^{-1/2+\varepsilon}\)
for every positive \(\varepsilon\). Its equation labeled `growthg` uses
the unconditional bound \(M(x)\ll x(\log x)^{-3}\) to obtain
\(g_\mu(x)\ll(\log x)^{-2}\). These are literature inputs, not new
Fibonacci results or a Lean formalization.

For the actual Fibonacci kernel \(e=\mu*\beta\), finite convolution gives

\[
g_e(D)=\sum_{m\le D}\frac{e_m}{m}
=\sum_{d\le D}\frac{\beta_d}{d}\,g_\mu(D/d).
\]

[The FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§394 uses this classical relation and the existing actual-input zero moment.
Its claim that every finite actual \(g_e(D)\) is nonzero depends separately
on the integer Fibonacci atoms, the unit correction, and the golden norm.
That actual-source conclusion and the cofactor prime-panel asymptotic are
repository derivations, not statements attributed to this paper. The
paper's symbol \(\phi\) for a convolution test function is not the FIB
volume's golden ratio \(\varphi\).
