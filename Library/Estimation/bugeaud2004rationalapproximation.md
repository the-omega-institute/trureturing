---
bibkey: bugeaud2004rationalapproximation
authors: Yann Bugeaud
year: 2004
title: Approximation by Algebraic Numbers
doi: 10.1017/CBO9780511542886
url: https://assets.cambridge.org/97805218/23296/excerpt/9780521823296_excerpt.pdf
claim: "Section 1.1 gives Dirichlet approximation, Liouville's algebraic irrationality lower bound and the definition and transcendence of Liouville numbers."
strata_touched: []
license: citation-only
triage: anchor
---

# Liouville approximation and the original decimal slope

## Verified locator

DOI: <https://doi.org/10.1017/CBO9780511542886> resolves with HTTP 200
to Cambridge's page for Bugeaud's 2004 book.
The [publisher excerpt](https://assets.cambridge.org/97805218/23296/excerpt/9780521823296_excerpt.pdf)
is HTTP 200 and identifies Bugeaud, the title and ISBN 0521823293.
Section 1.1, Theorems 1.1–1.2, Corollary 1.1 and Definition 1.1
on printed/PDF pp. 1–4 were inspected.

## Classical arithmetic bounds

Dirichlet's theorem supplies rational approximants with error
$<1/(qQ)$ for $1\le q\le Q$, and infinitely many approximants
with error $<q^{-2}$ for an irrational real number.
Liouville's theorem gives, for an algebraic irrational $\xi$ of
degree $d$, a constant $c(\xi)>0$ such that

$$
\left|\xi-\frac pq\right|\ge c(\xi)q^{-d}
\qquad(p\in\mathbb Z,\ q\ge1).
$$

A Liouville number admits nonzero rational approximation errors
smaller than every power of the denominator. The definition requires
a nonzero error; exact rational equality is not such an approximation.
The theorem and the rational separation bound show that these numbers
are transcendental. Corollary 1.1 treats the familiar decimal
$\sum_{j\ge1}10^{-j!}$.

## Correspondence with the fixed parity slope

Definition 39.1 of the
[posterior-field volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
uses $d_1=1$, $d_{n+1}=10^{5d_n}$, $Q_n=10^{d_n}$ and
$\alpha=\sum_{n\ge1}10^{-d_n}$. The finite decimal numerator is
$P_n=\sum_{j\le n}10^{d_n-d_j}$. Its positive tail satisfies

$$
0<\alpha-P_n/Q_n\le2\,10^{-Q_n^5}.
$$

The increasingly sparse decimal construction is an application of
the classical Liouville mechanism; the quantitative tail used at the
model's scale $\lambda=Q_n^3$ must retain this particular exponent.
The general Liouville definition alone supplies no uniform exponential
tail in a prescribed model scale.

Nor does transcendence of the ratio
$\alpha=\log(1+r)/[-\log(1-r)]$ by itself imply transcendence
of $r$. The original amplitude argument additionally uses the
[Baker–Wüstholz logarithmic-form lower bound](bakerwustholz1993logarithmicforms.md).
Exact rational independence of posterior centers also does not imply
a quantitative lower distance from integers or probabilistic
modulo-one anti-concentration.
