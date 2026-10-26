---
bibkey: bober2009factorialratios
authors: Jonathan W. Bober
year: 2009
title: Factorial ratios, hypergeometric series, and a family of step functions
doi: 10.1112/jlms/jdn078
url: https://arxiv.org/abs/0709.1977v1
claim: Theorem 1.2 classifies balanced integral factorial ratios of height one; Section 1.1 relates the associated step functions to the existing Nyman-Beurling criterion, without an unconditional Robin tail estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Factorial-ratio step functions and the existing RH criterion

The primary is [arXiv:0709.1977v1](https://arxiv.org/pdf/0709.1977v1),
with arXiv version stamp 13 September 2007. The 23-page PDF has SHA-256
`5f3cb3b1e7f74b791608669ce22a6d07ab51faac68436d806c9b329c9abf3201`.
The publication is *Journal of the London Mathematical Society* 79 (2009),
422--444, [DOI 10.1112/jlms/jdn078](https://doi.org/10.1112/jlms/jdn078).
The source locators below identify inspected statements and their scope;
the complete classification proof has not been independently audited or
Lean compiled. No source text or proof is vendored.

## Integrality and the classified family

For positive integer tuples $a=(a_1,\ldots,a_K)$ and
$b=(b_1,\ldots,b_L)$, write

$$
u_n(a,b)=\frac{\prod_{i=1}^K(a_i n)!}{\prod_{j=1}^L(b_j n)!},
\qquad
\Phi_{a,b}(u)=\sum_i\lfloor a_i u\rfloor-\sum_j\lfloor b_j u\rfloor.
$$

Landau's criterion, stated in Theorem 3.1 and specialized in Lemma 3.2,
PDF p.7, equates integrality of every $u_n$ with nonnegativity of
$\Phi_{a,b}$ on $[0,1]$. Under the balance condition
$\sum_i a_i=\sum_j b_j$, this step function is periodic. Lemma 3.4,
PDF p.8, relates its reflected values and its height $L-K$.
These are literature suppliers, not new project results.

Theorem 1.2, PDF p.3, classifies the case $L=K+1$, after canceling
common numerator and denominator parameters and imposing
$\gcd(a_1,\ldots,a_K,b_1,\ldots,b_L)=1$. There are three displayed
families, (7)--(9), and 52 sporadic parameter sets in Table 2.
This is a height-one classification, not a classification of all
nonnegative factorial-ratio kernels or their signed linear combinations.

The paragraph surrounding (10), PDF p.3, records that the best
Chebyshev constants obtained by the indicated argument from this family
are approximately $0.92$ and $1.11$. Its example is the classical ratio

$$
\frac{(30n)!n!}{(15n)!(10n)!(6n)!}.
$$

That ratio already has the repository divisibility developments
[BalaChebyshevThreeDivisibility](../../D5/S3/Arith/FactorialRatio/BalaChebyshevThreeDivisibility.lean)
and
[BalaChebyshevFiveDivisibility](../../D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.lean).
Their presence is a reuse locator; no current build or classification
formalization is asserted here.

## The RH connection is already Nyman-Beurling approximation

Theorem 1.1 and Lemma 3.5 relate the height-one ratios to step functions

$$
f(x)=\sum_k c_k\lfloor x/m_k\rfloor,
\qquad m_k\in\mathbb N_{>0},\quad c_k\in\mathbb Z,\quad
\sum_k\frac{c_k}{m_k}=0,
$$

with values in $\{0,1\}$. Section 1.1, PDF pp.4--5, places these
functions in the existing Nyman-Beurling problem. After $x=1/u$,
the finite balanced combinations correspond to fractional-part probes.
The criterion requires approximation of the constant function in
$L^2((1,\infty),dx/x^2)$; equivalently, one can use the corresponding
unit-interval formulation. The complete natural-dilation criterion is
already sourced in
[Baez-Duarte's strengthening](../Weil/baezduarte2002nyman.md).
A factorial-ratio integrality statement does not supply that norm
convergence. Bober's Theorems 1.3 and 1.5, PDF p.4, use a linear span with arbitrary
real coefficients (or its equivalent complexification), unlike the
integer coefficients in the classified blocks above. Coefficients can
change with the approximation stage. This criterion does not assert that
height-one functions alone suffice. Stagewise combinations of bounded
blocks need not themselves be uniformly bounded.

The specific natural-prefix nonconvergence result and its limitations
concerning subsequences are already recorded in
[Baez-Duarte 2000](../Weil/baezduarte2000natural.md).
Bober's separate divergence citation on PDF p.5 is reference [2],
*A divergent Vasyunin correction*, identified on p.22 as
[arXiv:math/0506318v1](https://arxiv.org/abs/math/0506318v1); it is not
Proposition 4.4 of the 2000 paper. The latter obstruction must not be widened to exclude every factorial-ratio construction,
every subsequence, or freely chosen coefficients. Pointwise convergence
alone does not supply the needed norm estimate without suitable global
control; a uniformly bounded sequence on this finite-measure space is a
different situation, where dominated convergence does apply.

## Remaining obligation for the ordinary Robin source

The [joint ordinary source](../Arith/caveney2012sacaga.md) fixes the same
actual integer $N$ and $A=\log N$, with
$\psi(t)=\sum_{p^k\le t}\log p$. The target remains an eventual
uniform lower bound for

$$
\sqrt A\log A\int_A^\infty(\psi(t)-t)
       \frac{1+\log t}{t^2\log^2t}\,dt.
$$

All ordinary prime powers, the actual exponent vector and the complete
CA reserve must be retained together. Neither the height-one
classification, the quoted Chebyshev constants, nor the criterion
supplies this signed estimate on that source. A factorial-kernel route
would still need a quantitative transfer with its whole residual paid
at this scale. The [existing comparison analysis](../ArithSums/nicolas2025comparison.md)
and [actual FIB target support analysis](../Weil/baezduarte2000natural.md)
remain the relevant interfaces; a positive branch classification is not
an estimate for their signed residual. No general impossibility theorem
for factorial methods or new analytic bound is asserted.
