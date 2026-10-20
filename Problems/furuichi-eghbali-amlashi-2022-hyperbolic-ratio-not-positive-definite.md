---
slug: furuichi-eghbali-amlashi-2022-hyperbolic-ratio-not-positive-definite
bibkey: furuichi2022bounds
doi: 10.7153/mia-2024-27-27
url: https://arxiv.org/abs/2203.01134
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.claim
---

# Furuichi–Eghbali Amlashi: the hyperbolic ratio below one

## Problem

S. Furuichi and M. Eghbali Amlashi, *On bounds of logarithmic mean and
mean inequality chain*, arXiv:2203.01134v2, Remark 3.2(i), proposes the
positive definite function conjecture. The supplied source identifies
this with Remark 2(i) in Mathematical Inequalities & Applications 27(2)
(2024), 379–399.

The ratio is

$$
\frac{K_r(e^{2t},1)}{L(e^{2t},1)}
=\frac{t(\cosh t)^{1-r}}{\sinh t}=: \phi_r(t),\qquad \phi_r(0)=1,
$$

where $K_r=G^r A^{1-r}$ and $L$ is the logarithmic mean. The source states:

> Thus these numerical computations support the conjecture that the function ϕr (t) for r < 1, is not positive definite.

The exact target is: for every real $r<1$, the complex cast of $\phi_r$
is not positive definite. Positive definiteness means that for every
natural $m$ and every $x:\operatorname{Fin}(m)\to\mathbb R$, the matrix
with entries $f(x_j-x_i)$ is positive semidefinite. The existing
`FiniteInversePoissonCriterion.PositiveDefinite` supplies this definition.

## Motivation

Numerical counterexamples at individual parameters do not decide the
full real interval below one. A general imaginary-axis obstruction
makes the analytic zero boundary decisive for every positive exponent
$1-r$, including arbitrarily small ones.

## Gap

The implication from real positive definiteness to an imaginary-axis
lower bound requires more than the usual real-axis boundedness.
Binomial quadratic forms extract the signs of all even Taylor
coefficients. Real-valuedness ensures that odd powers contribute zero
real part on the imaginary axis. The argument requires a holomorphic
extension throughout the disk where the lower bound is applied.

## Route

For $u_j=(-1)^j\binom{k}{j}$, two forward differences give

$$
\sum_{i,j=0}^k u_i u_j(i-j)^m=
\begin{cases}
0 & m<2k,\\
(-1)^k(2k)! & m=2k.
\end{cases}
$$

The positive semidefinite quadratic form at samples $-jh$ is nonnegative.
Taylor expansion through degree $2k$ and an analytic remainder show
that $(-1)^k a_{2k}\ge0$. Restricting the complex power series to the
real axis shows that its coefficients are real. Consequently every
nonconstant real contribution to $F(iy)$ is nonnegative, and
$\operatorname{Re}F(iy)\ge f(0)$ for $0\le y<R$.

Put $a=1-r>0$ and

$$
F(z)=\frac{\exp(a\operatorname{Log}(\cosh z))}
{\operatorname{dslope}(\sinh,0,z)}.
$$

On $|z|<\pi/2$, the real part of $\cosh z$ is
$\cosh(\operatorname{Re}z)\cos(\operatorname{Im}z)>0$.
The logarithm is therefore holomorphic. The divided slope is holomorphic
and nonzero, including its value one at zero. On the real diameter,
$F=\phi_r$. For $0<y<\pi/2$,

$$
F(iy)=\frac{y(\cos y)^a}{\sin y}\longrightarrow0
\quad\text{as }y\uparrow\pi/2.
$$

The lower bound one contradicts this limit.

## Falsifier

A real parameter $r<1$ for which every finite matrix
$[\phi_r(x_j-x_i)]$ is positive semidefinite would refute the claim.
Failure of an individual matrix test would only refute that test as
a witness. An error in the analytic extension or coefficient-sign
argument would invalidate the route without establishing the opposite
positive definite assertion.

## Evidence

The exact definitions `phi` and `claim`, and theorem `result`, are in
[FuruichiAmlashiHyperbolicRatio.lean](../D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.lean).
The general imaginary-radius theorem `le_re_of_positiveDefinite` and
`finite_difference_moment` are in
[PositiveDefiniteImaginaryAxis.lean](../D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.lean).
The conclusion has the full real parameter quantifier and the existing
finite-matrix definition of positive definiteness. The analytic lower
bound has no additional hypothesis beyond its stated real-valuedness,
positive definiteness, differentiability on the disk, and real-diameter
agreement. Both modules are tagged I because the reused definition's
module is tagged I; the analytic statement itself is general.

## Triage

- PROVED: `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.result` establishes the conjecture for every real $r<1$.
- PROVED: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.finite_difference_moment` gives the first surviving binomial quadratic moment, including $k=0$.
- PROVED: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.le_re_of_positiveDefinite` supplies the general analytic imaginary-radius lower bound.

### What the settlement shows

- PROVED (paper proof, not formalized here): the conjecture also follows from Albania–Nagisa Proposition 2.7 and classical facts. Positive definite functions are closed under pointwise products; $(\cosh t)^{-s}$ is positive definite for $s\ge0$, and $\tanh(t/2)/(t/2)$ is positive definite (Hiai–Kosaki 1999, Example 3.5). Put $q=1-r>0$ and choose an integer $k$ with $kq\ge1$. If $\phi_r$ were positive definite, so would be the left side of

  $$
  \phi_r(t)^k(\cosh t)^{1-kq}
  \left(\frac{\tanh(t/2)}{t/2}\right)^k
  =\frac{\cosh t}{\cosh^{2k}(t/2)}
  =2^{2k-1}\frac{\sinh(2t)\sinh^{2k}(t/2)}{\sinh^{2k+1}(t)}.
  $$

  Proposition 2.7 excludes the right side: take $a=(2,1/2,\ldots,1/2)$ with $2k$ entries equal to $1/2$ and $b=(1,\ldots,1)$ of length $2k+1$. A positive scalar multiple cannot change positive definiteness. All removable values at zero are understood continuously. The [Albania–Nagisa Library note](../Library/Fourier/albania2017families.md) binds the proposition and its locators.
- PROVED (paper proof, not formalized here): the independent Lean route's analytic imaginary-axis bound also reproves Proposition 2.7. For positive $a_i,b_i$ with $a_1>\max_i b_i$, the product $\prod_i\sinh(a_i z)/\sinh(b_i z)$, with its removable value $\prod_i a_i/b_i>0$ at zero, is holomorphic on the disk of radius $\pi/\max_i b_i$. It vanishes at $i\pi/a_1$, strictly inside the disk, contrary to the analytic lower bound if the real restriction were positive definite. This application of the bound is proved on paper, not formalized here.
- PROVED (paper proof, not formalized here): the same lemma decides Remark 3.8(i), comparing $L$ with $B_p$ for $0<p<1/2$. Write $F_p(t)=\sinh t/(t(\cosh(pt))^{1/p})$, with value one at zero. Its extension is holomorphic on $|z|<\pi/(2p)$ and vanishes at $i\pi$, which lies strictly inside that disk. The lower bound one excludes positive definiteness. There is also a Proposition 2.7 reduction: choose an integer $m\ge1/p$. If $F_p$ were positive definite, closure under products and the classical positive definiteness of $pt/\sinh(pt)$ would make the left side of

  $$
  F_p(t)(\cosh(pt))^{-(m-1/p)}\frac{pt}{\sinh(pt)}
  =p\,2^m\frac{\sinh t\,(\sinh(pt))^{m-1}}{(\sinh(2pt))^m}
  $$

  positive definite. Proposition 2.7 excludes it with $a=(1,p,\ldots,p)$ and $b=(2p,\ldots,2p)$, each of length $m$, since $1>2p$.
- COMPUTED: at step $h=0.05$, scanning binomial orders $k=1,2,\ldots$ with `mpmath` at 60 decimal digits gives the first negative quadratic form at $k=2$ for $r=2/3$, $k=3$ for $r=0.9$, $k=5$ for $r=0.99$, and $k=7$ for $r=0.999$. The respective values are approximately $-3.32014459577087277\cdot10^{-6}$, $-2.13592501542096782\cdot10^{-8}$, $-5.87653709085978443\cdot10^{-12}$, and $-9.61362164735655401\cdot10^{-15}$. The calculation evaluates `mp.fsum((-1)**(i+j)*mp.binomial(k,i)*mp.binomial(k,j)*phi(mp.mpf('0.05')*(i-j)) for i in range(k+1) for j in range(k+1))`, with `phi(0)=1` and the displayed hyperbolic formula otherwise.
- PROVED (paper proof, not formalized here) for the infinitesimal binomial method: each fixed signed even Taylor coefficient is strictly positive at $r=1$ and continuous in $r$. The former follows from the nonzero alternating even coefficients of $t/\sinh t$. Thus the first coefficient-sign obstruction has order tending to infinity as $r\uparrow1$. No fixed matrix size suffices for this particular infinitesimal binomial method. OPEN: exclusion of a uniform matrix size over arbitrary configurations and vectors; that stronger assertion does not follow from the four computations or the coefficient argument.
- PROVED (paper proof, not formalized here), conditional on the Hiai–Kosaki positive definite ratio criterion and the source mean definitions: $K_r\not\preccurlyeq L$ for $0\le r<1$.
- PROVED in the source, not formalized here: the range $r\ge1$ is positive definite. This is the source's positive result, rather than a new consequence of the negative-range argument.
- OPEN: an effective optimal finite matrix witness size for each real parameter below one.

## ASSUMED-UNVERIFIED

The original source quotation, version correspondence, and positive
parameter-range attribution are supplied information. No online source
or citation-index verification was possible under the offline constraint.
The supplied literature search found no source stating the
Albania–Nagisa deduction or a resolution of the conjecture. Its searched
scope comprises Hiai–Kosaki, Lecture Notes in Mathematics 1820, chapter 7;
Hiai–Kosaki 1999, pp. 923–924; Kosaki, Journal of Functional Analysis
2014; and follow-up papers from 2022–2026. Kosaki, Memoirs of the AMS
2011, was not read in full text. This is the supplied search status,
not an exhaustive citation-index or priority certification. The
[Library note](../Library/Fourier/furuichi2022bounds.md) binds the DOI and
arXiv locators of the conjecture, and the
[Albania–Nagisa Library note](../Library/Fourier/albania2017families.md)
binds the DOI and arXiv locators of Proposition 2.7. The classical-factor
reductions, the application reproving Proposition 2.7, the neighbouring
mean-ordering statements, and the asymptotic binomial-order discussion
are mathematical analyses on paper, not additional Lean settlements.
