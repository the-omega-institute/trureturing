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
or DOI. The inspected original TeX scope is the abstract, Sections 1–2 and
the hypotheses and conclusion of the `GL1` lemma in Section 3.1; the
complete analytic proofs and the other results are not independently
certified here. No source text is vendored. The source archive has SHA256
`3654ec2a72bdae5d567ab0968d7283a636894928c07464a7986b19bcc491aeef`.

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

## The existing Mellin convolution input

Section 2 defines

$$
N_a(f)=\int_0^\infty|f(t)|t^{-a-1}\,dt.
$$

Section 3.1, the lemma labeled `GL1`, assumes $N_0(\phi)<\infty$ and
uses the classical convolution algebra on the multiplicative group
$(0,\infty)$ with Haar measure $dt/t$. Its norm conclusion is

$$
N_0(G\phi)\le N_0(g)N_0(\phi),\qquad
g(x)=\sum_{n\le x}\frac{\mu(n)}n.
$$

This is an existing absolute-convolution tool. The project's finite
$N_\alpha(R)$ for $0<\alpha<1$ does not by itself supply $N_0(R)$;
the displayed $O(1+\log y)$ high-quotient envelope alone also does not
prove that latter integral finite. No substitution $\phi=R$ or
identification $G\phi=I_\psi$ is asserted from those bounds.

The actual discrete adjacent-dilation difference in FIB §397 instead
retains the jump intervals of $K$ and the low-quotient continuous part
of $R$. It verifies the countable integral-norm premise for that
same-source series before using
[the existing integral-sum theorem](mathlib2026absoluteintegralsum.md).
The classical norm theorem and its Mellin formulation are not new
FIB results; the manuscript application remains without a complete
Lean verification or an RH/Robin conclusion.

## The exact endpoint already has a simplicity consequence

The additional inspected original TeX scope is Theorem 4.1, labeled
rhs, and its stated hypotheses and conclusion. In the paper's
notation, RHS means RH together with simple nontrivial zeros.
The theorem assumes a Mellin-proper test $\phi$, an extension
$\phi^\wedge\in A_c[-1/2,1]$, and nonvanishing on the boundary line
$\Re s=-1/2$. It concludes

$$
G_\phi(y)=O(y^{-1/2})\quad(y\to\infty)
\quad\Longrightarrow\quad
\text{RH and simple nontrivial zeros}.
$$

The [Liflandsky v4 source note](liflandsky2026mobiuslaplace.md) records
its §8.2 specialization with
$h(u)=u^{-1}e^{-1/u}$ and $\phi(u)=u h'(u)$:
$G_\phi(y)=y^{-1}\Phi_\mu(1/y)$ and
$\phi^\wedge(s)=s\Gamma(s+1)$.
That source supplies the test's required Mellin hypotheses. The
original theorem's complete proof is not independently certified here.
The original proof writes $\phi(s)$ in its nonvanishing step, then
$x^{\sigma-3/2}$ and $1/(\sigma-1/2)$ in its final estimate while
taking $\sigma\downarrow-1/2$. These notation and sign issues do not
match that stated boundary limit. The theorem statement is cited as
written; no silent correction or certification of that argument is claimed.

This exact endpoint has a stronger conclusion than the
$y^{-1/2+\varepsilon}$ RH criterion with a loss for every
$\varepsilon>0$. Removing that loss is an additional mathematical
obligation; it is not achieved by renaming the existing FIB
convolution or dilation filter.
