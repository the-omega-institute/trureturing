---
bibkey: alouges2022polynomial
authors: François Alouges, Sébastien Darses, Erwan Hillion
year: 2022
title: Polynomial approximations in a generalized Nyman-Beurling criterion
doi: 10.5802/jtnb.1227
url: https://arxiv.org/abs/2006.02953v2
claim: Lemma 1.2 supplies the fractional-part Mellin multiplier, and Theorem 3 requires both a quantitative approximation rate and control of the combined seed tail to exclude zeros in a strip; unconditional density alone supplies neither a Robin tail bound nor that joint control.
strata_touched: []
license: citation-only
triage: anchor
---

# Generalized Nyman-Beurling approximation and the missing tail control

The pinned primary is [arXiv:2006.02953v2](https://arxiv.org/abs/2006.02953v2),
version stamp 1 June 2022. The [14-page PDF](https://arxiv.org/pdf/2006.02953v2)
has SHA-256
`36b419c75ce4854cf54833fe289b69f83e79ff38dfe0e652e8f3cf212a596bf5`;
the [author-source archive](https://arxiv.org/src/2006.02953v2) has SHA-256
`3de578f71ea15d22ea652577f14aa809c7d85aea449452ae8f3d529a3866c01d`.
The selected formulas were checked against the author TeX, rather than
relying on the PDF's imperfect text extraction. The
[publisher record](https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.1227/)
identifies *Journal de théorie des nombres de Bordeaux* 34 (2022), no.3,
767--785, [DOI 10.5802/jtnb.1227](https://doi.org/10.5802/jtnb.1227).
The locators below refer to the pinned arXiv pagination and numbering.
This note quotes literature and gives a scoped paper application; it
adds no Lean declaration, kernel certification or claim of priority.
No source text or proof is vendored.

## Reuse the existing multiplier and both hypotheses

Write

$$
g^\times(t)=\int_0^\infty\{x/t\}g(x)\,\frac{dx}{x},
\qquad \widehat g(s)=\int_0^\infty g(x)x^{s-1}\,dx.
$$

Assumption (M), PDF p.3, is
$\int|g(x)|\,dx<\infty$ and $\int|g(x)|\,dx/x<\infty$.
Lemma 1.2(i), PDF p.4, gives $g^\times\in L^2(0,\infty)$ and

$$
\widehat{g^\times}(s)=-\frac{\zeta(s)}s\widehat g(s),
\qquad 0<\operatorname{Re}s<1.
\tag{A1}
$$

Part (ii) gives the analogous identity for
$\mathbb E\{Z/t\}$ when $Z\ge0$ is integrable; it does not require
$Z$ to have a density. Equation (1.11), PDF p.3, already supplies the
fractional-part multiplier underlying (A1). These are known inputs,
not new factorial-kernel or FIB estimates. The
[existing Nyman-Beurling source](baezduarte2002nyman.md) remains the
owner of the natural-dilation criterion.

Theorem 3, PDF p.5, fixes $1/2<\sigma_0<1$, seeds $g_k$ satisfying
(M), and one real target $\phi$ such that
$\int_0^\infty(1+t)|\phi(t)|^2\,dt<\infty$ and $\widehat\phi$ is
nonzero throughout $1/2<\operatorname{Re}s\le\sigma_0$.
For the same real coefficients $c_{k,n}$ and cutoffs $M_n\to\infty$,
put $G_n=\sum_{k=1}^n c_{k,n}g_k$. Both conditions are required:

$$
M_n^{2\sigma_0-1}\|\phi-G_n^\times\|_{L^2(0,\infty)}^2\longrightarrow0,
\tag{A2}
$$

$$
M_n^{\sigma_0-1}\int_{M_n}^\infty|G_n(x)|\,dx\longrightarrow0.
\tag{A3}
$$

The source labels these (2.12) and (2.13). Together they imply
zero-freedom in the stated strip. The absolute value in (A3) is outside
the combined seed sum; the theorem does not replace it by a claim
about each seed separately. Its proof on pp.5--7 uses both conditions
at the same hypothetical zero.

Theorem 4, PDF pp.7--8, supplies unconditional gNB approximation for
its specified inverse-Gamma construction. That is the unscaled
approximation property of Section 1.1, Definition 1.1 (PDF p.3), not a proof that (A2)
and (A3) hold jointly. Section 4.3.2, PDF p.13, observes that a common
compact seed support makes (A3) automatic for sufficiently large
$M_n$. It then discusses the loss of the stated polynomial-density
argument. This discussion is not a theorem excluding every compact
support construction or every factorial method.

## Application to the original Robin kernel

Keep the same actual ordinary integer $N$ from the
[joint source](../Arith/caveney2012sacaga.md), and put $A=\log N>1$.
The original kernel and its Mellin transform are already identified in
[(M1)--(M2) of the comparison analysis](../ArithSums/nicolas2025comparison.md):

$$
H_A(t)=\frac1{\max(A,t)\log\max(A,t)},
\qquad F_A(s)=\int_0^\infty H_A(t)t^{s-1}\,dt.
$$

The following is an application of the known multiplier, not an
additional result attributed to the paper. For each fixed $A>1$,
$H_A$ satisfies the weighted-square-integrability condition of
Theorem 3: its tail with weight $t$ is
$\int_A^\infty dt/(t\log^2t)<\infty$.
Writing $\ell=\log A$, the identity
$1/\log t=\int_0^\infty t^{-u}\,du$ gives

$$
sA^{1-s}F_A(s)=\int_0^\infty
 e^{-\ell u}\frac{1+u}{1+u-s}\,du,
\qquad 0<\operatorname{Re}s<1.
\tag{A4}
$$

Indeed, split the defining Mellin integral at $A$. The two pieces
are $A^{s-1}/(s\ell)$ and
$A^{s-1}\int_0^\infty e^{-\ell u}/(1+u-s)\,du$.
Fubini is justified by the corresponding finite integral with
$\operatorname{Re}s$ in place of $s$. The integrand on the right of
(A4) has strictly positive real part, so $F_A(s)\ne0$ in that strip.
Thus this fixed target meets the target hypotheses of Theorem 3;
(A2)--(A3), with this target and the same approximants, remain to be
proved. Applying a fixed-target theorem is not a uniform estimate
for a moving family $A\to\infty$.

The finite balanced factorial case is already covered by the same
multiplier. If
$\Phi(u)=\sum_i\lfloor a_i u\rfloor-\sum_j\lfloor b_j u\rfloor$
with positive parameters and $\sum_i a_i=\sum_j b_j$, put
$K_{\Phi,x}(t)=\Phi(x/t)$ for $x>0$. Cancel the linear terms and
apply the source's fractional-part identity to obtain

$$
\widehat K_{\Phi,x}(s)=x^s\frac{\zeta(s)}s
 \left(\sum_i a_i^s-\sum_j b_j^s\right).
\tag{A5}
$$

Consequently every finite signed combination $G_A$ of these kernels
has zero Mellin value at any actual nontrivial zero
$\rho=\beta+i\gamma$. With
$\|h\|_\beta=\int_0^\infty|h(t)|t^{\beta-1}\,dt$, Mellin evaluation
therefore gives the necessary error bound

$$
\|H_A-G_A\|_\beta\ge|F_A(\rho)|>0.
\tag{A6}
$$

The same conclusion holds for a signed kernel mixture when
$\int\|K_{\Phi,x}\|_\beta\,d|\nu|(\Phi,x)<\infty$; that absolute
condition is needed to interchange the mixture and Mellin integral.
There is no assertion about arbitrary conditionally convergent mixtures.

For a fixed zero, subtract $(1-s)^{-1}$ from the integrand factor
$(1+u)/(1+u-s)$ in (A4). Since the difference is
$-su/((1-s)(1+u-s))$, one obtains

$$
F_A(\rho)=\frac{A^{\rho-1}}{\rho(1-\rho)\log A}+R_A,
\qquad
|R_A|\le\frac{A^{\beta-1}}
 {|1-\rho|(1-\beta)\log^2 A}.
\tag{A7}
$$

In particular, if $\log A\ge2|\rho|/(1-\beta)$, (A6) is at least
$A^{\beta-1}/(2|\rho(1-\rho)|\log A)$.
A critical-line zero obstructs little-oh approximation at the root
scale in this weighted norm; it does not obstruct big-oh approximation.
Conditional on a right-hand zero, the corresponding $\beta$-weighted
norm cannot have a big-oh root-scale bound. Neither statement is a
lower bound for the signed Robin tail itself.

## The remaining arithmetic transfer is a separate obligation

A weighted Lebesgue $L^1$ kernel error alone does not control pairing
against the actual prime-power measure
$\mu=d\psi-dt$, where $\psi(t)=\sum_{p^k\le t}\log p$.
For example, fix one prime power $m=p^k$ and use continuous triangular
bumps $e_\varepsilon(t)=\max(1-|t-m|/\varepsilon,0)$ with
$0<\varepsilon<1/2$. Their $\beta$-weighted norms tend to zero,
whereas $\int e_\varepsilon\,d\mu=\log p-\varepsilon$ tends to
$\log p$. Thus no finite constant bounds this pairing by
$\|e\|_\beta$ for all compactly supported continuous errors $e$.
This standard atomic-measure obstruction does not exclude a bound
for a smaller, independently controlled family of errors.

The original target remains an eventual uniform lower bound for

$$
\sqrt A\log A\,I_\psi(A),\qquad
I_\psi(A)=\int_A^\infty(\psi(t)-t)
 \frac{1+\log t}{t^2\log^2t}\,dt,
$$

on the same actual ordinary source, with every prime power, exponent
and complete CA reserve retained. The paper supplies neither this
signed bound nor (A2)--(A3) for a proposed FIB family. The known
multiplier and density theorems are reused; a quantitative coefficient
tail or a justified transfer to this actual arithmetic pairing is the
remaining work. No new Robin estimate or RH proof is asserted.
