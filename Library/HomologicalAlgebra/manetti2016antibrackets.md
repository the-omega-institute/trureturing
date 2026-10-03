---
bibkey: manetti2016antibrackets
authors: Marco Manetti; Giulia Ricciardi
year: 2016
title: "Universal Lie Formulas for Higher Antibrackets"
doi: 10.3842/SIGMA.2016.053
url: https://arxiv.org/abs/1509.09032v3
claim: "In the algebra of linear endomorphisms of Q[x] vanishing at 1, with Phi^{n,i}(x^i) = x^{n-i}/(n-i)!, Phi^n = sum_i (-1)^{n-i} Phi^{n,i} and rho_k(Psi) = (x^k/k! - x^{k+1} d/(k+1)!) o Psi - Psi o x d^{k+1}/(k+1)!, there is for every n > 0 a unique sequence of rationals c_1^n, ..., c_n^n with Phi^{n+1} = (c_1^n rho_1^n + c_2^n rho_1^{n-2} rho_2 + ... + c_n^n rho_n) Phi^1 (Theorem 6.4); these are the coefficients of Theorem 2.3 for higher Koszul brackets. Conjecture 2.4 gives a closed formula for c_i^n, verified by the authors for n <= 12, and asserts (-1)^n c_i^n > 0."
strata_touched:
  - D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients
license: citation-only
triage: anchor
---

# Universal Lie Formulas for Higher Antibrackets

Marco Manetti, Giulia Ricciardi, SIGMA 12 (2016), 053, 20 pages;
arXiv:1509.09032 (math.QA, cross-listed hep-th and math-ph). Quotations
are from the arXiv v3 source.

Theorem 2.3:

> In the notation above, for every integer $n>0$, there exists an unique sequence
> $c_1^n,\ldots,c_n^n$ of rational numbers
> such that, for every linear operator $f\colon A\to A$, we have

followed by the display
$\Phi^{n+1}_f=\big(c_1^n\rho_1^n+c^n_2\rho_1^{n-2}\rho_2+c^n_3\rho_1^{n-3}\rho_3+\cdots+c^n_n\rho_n\big)f$.

Conjecture 2.4:

> For every $n\ge 2$ the coefficients $c^n_i$ of Theorem~{\rm \ref{thm.standardform}} are given by the formula

followed by the display
$c_i^n=\frac{\displaystyle (-1)^{n} \prod_{j=2}^{i}\dfrac{n(n-1)-(j-1)(j-2)}{2}}{\displaystyle \sum_{h=2}^n h\left(\prod_{j=2}^{h}\dfrac{n(n-1)-(j-1)(j-2)}{2}\right)\left(\prod_{j=h}^{n-1}\dfrac{(1-j)(j+2)}{2}\right)}$,
and

> where every empty product is intended to be equal to $1$. Moreover $(-1)^{n}c^n_i>0$ for every $n\ge i\ge 1$.

The operators (Section 6):

> For every $n\ge i>0$, denote by $\Phi^{n,i}\in \mathfrak{a}$ the operator

with $\Phi^{n,i}(x^{i})=\frac{x^{n-i}}{(n-i)!}$ and $\Phi^{n,i}(x^s)=0$ for
$s\ne i$; $\Phi^n=\sum_{i=1}^n(-1)^{n-i}\Phi^{n,i}$; and Lemma 6.2 defines
$\rho(l_n)(\Psi)=\left(\dfrac{x^n}{n!}-\dfrac{x^{n+1}\partial}{(n+1)!}\right)\circ \Psi-\Psi\circ \dfrac{x\partial^{n+1}}{(n+1)!}$.
Theorem 6.4 states the unique solvability of
$\Phi^{n+1}=\big(c^n_1\rho_1^n+c^n_2\rho_1^{n-2}\rho_2+\cdots+c^n_n\rho_n\big)\Phi^1$
in $\mathfrak{a}$, and Lemma 6.3 transports it to Theorem 2.3.

## Verified locator

- DOI: https://doi.org/10.3842/SIGMA.2016.053 (SIGMA 12 (2016), 053).
- URL: https://arxiv.org/abs/1509.09032v3 (v1 2015-09-30, v2 2015-11-12,
  v3 2016-06-06; source `sigma16-053.tex`, md5
  `69e1f0c5a2a7c94f98ac2352869f2b60`): Theorem 2.3 (l. 176–181), the
  sentence before the conjecture (l. 184), Conjecture 2.4 (l. 186–192),
  the algebra $\mathfrak{a}$ (l. 662), $\Phi^{n,i}$ (l. 681–682), $\Phi^n$
  (l. 686–688), Lemma 6.2 (l. 700–703), Lemma 6.3 (l. 735–749) and
  Theorem 6.4 (l. 751–754).
