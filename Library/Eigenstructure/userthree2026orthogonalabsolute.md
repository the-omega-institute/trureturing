---
bibkey: userthree2026orthogonalabsolute
authors: User3 (MathOverflow user 600125)
year: 2026
title: A nontrivial lower bound for the orthogonally transformed absolute product
doi: null
url: https://mathoverflow.net/questions/515549
claim: 'The question asks for a strict uniform lower bound above one, or an intrinsic characterization of the infimum of rho(abs(PQ) abs(transpose(Q) inverse(P))) over real orthogonal Q for nonsingular real square P.'
strata_touched:
  - D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum
license: CC-BY-SA-4.0
triage: anchor
---

# Orthogonally transformed absolute products

## Verified locator

https://mathoverflow.net/questions/515549

User3, MathOverflow user 600125, revision 1,
GUID `CB719581-BCE3-4573-931E-15327002F861`, published
2026-09-25T19:17:56+00:00. Source text and version evidence are supplied
by the registered problem record, issue 24893. The revision identifies the
question and does not assert its present answer status.

## Source question

> Let $P\in\mathbb{R}^{K\times K}$ be nonsingular and define
> $$M(Q)=|PQ|\,|Q^\top P^{-1}|,\qquad Q\in O(K).$$
> $|M∣$ means the matrix obtained by taking the absolute value of each entry.
> Since
> $$|PQ(Q^\top P^{-1})|=I\le |PQ|\,|Q^\top P^{-1}|=M(Q),$$
> one obtains the trivial bound $\rho(M(Q))\ge 1$.
> $\rho(M(Q))$ is the spectral radius of the matrix $M$.
> The question is whether there exists a nontrivial quantity $\beta(P)$,
> depending only on $P$, such that
> $$\rho(M(Q))\ge\beta(P)>1\qquad\text{for all }Q\in O(K),$$
> for an appropriate class of nonsingular matrices $P$.
> Equivalently, can the optimization problem
> $$\inf_{Q\in O(K)}\rho\!\left(|PQ|\,|Q^\top P^{-1}|\right)$$
> be bounded below, or even characterized explicitly, in terms of intrinsic
> properties of $P$?

Quotation: rendered body with paragraph whitespace normalized; notation
retained. Attribution: User3, MathOverflow, identified revision, under
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).

## Formal correspondence

The formal theorem quantifies over every natural dimension $K>0$, every
real $K$-by-$K$ matrix $P$ with nonzero determinant, and every real matrix
$Q$ satisfying both orthogonality identities. Absolute value is entrywise,
the products are matrix products, and the radius is computed over the
complex numbers after entrywise inclusion of the real entries.

The universal lower bound is joined to existence of an orthogonal $Q$
with objective exactly one. This characterizes the attained minimum and
the infimum as one, and excludes any strict uniform lower bound above one
for any nonsingular $P$. It imposes no dimension bound or sign restriction
and makes no assertion classifying every minimizer.

The proof applies ordered Gram-Schmidt and the triangular inverse,
characteristic polynomial and spectral comparison results in the pinned
Lean libraries. This source is cited for its question, not for a proof of
the attained value. The supplied bounded prior-result screen did not
identify an exact published resolution; worldwide completeness and
historical priority remain unverified.
