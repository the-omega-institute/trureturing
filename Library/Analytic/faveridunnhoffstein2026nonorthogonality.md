---
bibkey: faveridunnhoffstein2026nonorthogonality
authors: Alexandre de Faveri; Alexander Dunn; Jeffrey Hoffstein
year: 2026
title: "Non-orthogonality of the cubic and quartic large sieves via Rankin--Selberg"
doi: null
url: https://arxiv.org/abs/2607.07911v2
claim: "Theorems 1.1 and 1.2 prove cubic and quartic large-sieve lower bounds; Conjecture 1.3 is the quartic upper bound (1.8), while the general fixed-order prediction is Section 1.2, equation (1.9). These operator-norm results do not give a lower bound for the prescribed original Mobius/plain coefficient."
strata_touched: []
license: citation-only
triage: anchor
---

# Gauss-sum bias as a non-orthogonality boundary

The source is [arXiv:2607.07911v2](https://arxiv.org/pdf/2607.07911v2),
updated 13 July 2026. This card records the operator-norm statements and
their relevance to the project's fixed-order character estimates. It is a
literature boundary, not an independent proof audit or Lean certification.

## Proven lower bounds

For the cubic character family, Theorem 1.1 states

$$
\Xi_3(A,B)\gg_\varepsilon (AB)^{-\varepsilon}
\left(A+B+(AB)^{2/3}\right).
$$

For the quartic family, Theorem 1.2 states

$$
\Xi_4(A,B)\gg_\varepsilon (AB)^{-\varepsilon}
\left(A+B+A^{3/4}B^{1/2}+A^{1/2}B^{3/4}\right).
$$

At the balanced scale $A\asymp B\asymp X$, these give respectively
$X^{4/3-\varepsilon}$ and $X^{5/4-\varepsilon}$. Thus the character
families are unconditionally not perfectly orthogonal. The paper attributes
the obstruction to a bias in the relevant Gauss sums and obtains the
quartic input through Rankin--Selberg regularization of metaplectic theta
coefficients.

## General-order prediction

Conjecture 1.3 is specifically the quartic upper bound, equation (1.8).
The general fixed-order prediction appears separately in §1.2, equation
(1.9): for $n\ge3$ over a field containing $\mathbb Q(\zeta_n)$,

$$
\Xi_n(A,B)=(AB)^{o(1)}
\left(A+B+A^{1-1/n}B^{2/n}+A^{2/n}B^{1-1/n}\right)
$$

as $\min(A,B)\to\infty$. For $n=6$ and $A\asymp B\asymp K$, this predicts
the $K^{7/6+o(1)}$ scale appearing in the project's balanced joint-contour
target. The source's $\Xi_3$ and $\Xi_4$ use squarefree rows and columns;
its prediction concerns the analogous family. The paper does not prove
the $n=6$ case or this prediction in general. The later de Faveri upper
bound, recorded in [the fixed-order card](faveri2026fixedorder.md), applies
to $n$-th-power-free supports and hence to their squarefree restriction.
This does not supply a matching all-range lower bound on the
squarefree-squarefree family: a lower bound on the larger support cannot
be restricted in that direction. The source's older statement that a
power-saving upper improvement for $n\ge4$ remains open must be read
with that later result.

## Exact non-overlap with the project's open estimate

The project already records de Faveri's later fixed-order upper bound in
`faveri2026fixedorder.md`. The present source supplies a complementary
lower-bound obstruction:

* it is an operator norm for a full cubic or quartic character family;
* it does not estimate the signed kernel $\mathscr F_{j,a}$ in the joint
  contour target;
* it does not handle the moving quadratic twist coupled to the cubic Gauss
  factor after the project's theta transform; and
* it does not address detector length coverage or the final signed Robin
  restoration.

Consequently the results rule out a diagonal-only or perfect-orthogonality
shortcut, but they are neither an upper bound for (J) nor a Robin or RH
argument. The structural similarity between the paper's Gauss bias and the
project's moving quadratic/cubic coupling is a search interface only; an
explicit reduction would still be a new theorem.



## Existing theta-corrected and cuspidal estimates

Dunn–Radziwiłł, [*Bias in cubic Gauss sums: Patterson's conjecture*,
arXiv:2109.07463v3, Propositions 9.1–9.2](https://arxiv.org/html/2109.07463v3#S9),
already estimate the cubic squared sum after subtracting an explicit theta
term. That correction and its proof are literature inputs to reuse.
The hypotheses include $0<\eta\le1/4$, $A,B,w\ge10$,
$w>(\log(AB))^{10}$ and $\boldsymbol\beta\in\mathcal C_\eta(B,w)$.
Definition 3.1 requires bounded coefficients, squarefree $w$-rough primary
support of norm $\asymp B$, and near-square-root cancellation under every
allowed angular/norm twist and divisibility restriction $u\mid b$, with
the stated nontriviality condition on the angular/cubic twist. Membership
of the original unrestricted sextic Möbius/plain convolution in this class
has not been established. Lemmas 6.1–6.2 verify membership for specific
prime-product sequences under Hecke GRH; that route would not discharge
an unconditional RH proof obligation.

The theta correction retains the row-dependent condition $(a,b)=1$.
It is not identified with the actual finite Gauss-row projection $P_L$
without an additional kernel and normalization comparison. Even if such
a comparison were available, at $A=B=K$ and the source's $\pi=1$,
Proposition 9.1 contains

$$
B^{29/12}A^{-1/12}=K^{7/3}.
$$

Thus direct specialization of that bound does not provide a sub-$K^2$
squared-sum estimate at those lengths. This is a limitation of the
specified direct application, not a lower bound on the actual sum.

Dunn, [*Metaplectic cusp forms and the large sieve*,
arXiv:2403.13151v4, Theorem 1.5](https://arxiv.org/html/2403.13151v4#S1),
provides a Type-II estimate for the Fourier coefficients of a fixed cubic
metaplectic cusp form, with constants depending on that form. Its stated
dense-coefficient saving range is $X^{2/3+\varepsilon}\ll B\ll X^{1-\varepsilon}$,
$X\asymp AB$, which excludes the equal-length specialization. The theorem
itself is stated for all $A,B\ge10$; the useful range is not a hypothesis
limiting its validity. Applying it to the original sextic complement
would require an exact spectral realization of that kernel and uniform
control of the occurring forms, levels, twists and profiles. Neither the
finite projection nor the phrase “remove theta” supplies that realization.

In particular an operator-norm lower bound selects some coefficient
vector and does not give a lower bound for the prescribed
$b(h)=\omega(h)\sum_{dn=h}\mu(d)V(q_d/D)W(q_n/N)$.
The formal diagonal in $\|Ab\|_2^2$ is not a lower bound either, since its
off-diagonal part has signs. The complete original-energy estimate in
[§459](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#459-缓冲零点分箱下的完整原卷积联合估计),
the small-label projection in
[§484](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II.md#484-全部小标记的反射主项与完整投影预算),
and the complement lacking the required sub-$K^2$ bound therefore retain
distinct scopes.
These applicability statements carry no independent Lean certification
or new large-sieve theorem.
