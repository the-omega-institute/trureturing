---
slug: user3-2026-orthogonal-absolute-product-minimum
bibkey: userthree2026orthogonalabsolute
doi: null
url: https://mathoverflow.net/questions/515549
triage: theorem
motivation_gids:
  - D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.result
---

# The orthogonal absolute-product minimum is attained at one

## Problem

User3 (MathOverflow user 600125), *A nontrivial lower bound for the
orthogonally transformed absolute product*, question 515549, revision 1,
GUID `CB719581-BCE3-4573-931E-15327002F861`, asks:

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

The quotation is attributed to User3, MathOverflow, under
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
Its source identity and license are recorded in
[the Library note](../Library/Eigenstructure/userthree2026orthogonalabsolute.md).

The single resolution anchor is the exact optimization characterization:
for every natural $K>0$ and every $P\in\mathbb R^{K\times K}$ with
$\det P\ne0$,

$$
\left(\forall Q\in O(K),\quad
1\le\rho\!\left(|PQ|\,|Q^\top P^{-1}|\right)\right)
\quad\land\quad
\left(\exists Q\in O(K),\quad
\rho\!\left(|PQ|\,|Q^\top P^{-1}|\right)=1\right).
$$

Thus the minimum and infimum are both one, with actual attainment.
In particular, no $\beta(P)>1$ can bound the objective below for every
orthogonal $Q$, for any nonsingular $P$ in positive dimension. This answers
the characterization question and negates the proposed strict improvement.

## Motivation

The source distinguishes the entrywise absolute-product spectral radius
from a norm or a matrix absolute value. Determining its exact orthogonal
minimum decides whether intrinsic features of a nonsingular matrix can
force a strict improvement on the elementary bound one.

## Gap

The source gives the elementary bound but asks whether a stronger bound
or an explicit infimum characterization is available. This is a Tier 1
recent externally authored question, preregistered in
[issue #24893](https://github.com/the-omega-institute/trureturing/issues/24893).
The retained bounded literature and duplicate screen identified no exact
published resolution within its searched scope. That negative search
result does not establish exhaustive literature coverage or priority.

## Route

For every orthogonal $Q$, the matrices $A=PQ$ and $B=Q^\top P^{-1}$
satisfy $AB=I$. The finite-sum triangle inequality gives
$I\le |A||B|$ entrywise; the frozen spectral comparison
`D5/S1/Digit/Infinite/ResetCodebookOrder.radius_mono` supplies the bound one.

Apply ordered Gram-Schmidt to the rows of $P$ and use the resulting
orthonormal basis as the columns of $Q$. Then $T=PQ$ is lower triangular,
$Q$ satisfies both orthogonality identities, and
$T^{-1}=Q^\top P^{-1}$ is lower triangular. The product $|T||T^{-1}|$
is lower triangular with every diagonal entry equal to one.
Its complex characteristic polynomial is $(X-1)^K$, so its spectral radius
is one for $K>0$. This argument uses the pinned Mathlib Gram-Schmidt,
triangular-inverse and characteristic-polynomial results directly.

## Falsifier

Replacing entrywise absolute values by a norm or operator absolute value,
reversing or changing the matrix products, restricting the orthogonal
domain, bounding the dimension, assuming a sign pattern or diagonalizability,
or replacing attainment by an approximation would fail to match this
problem. The formal result requires $K>0$ and $\det P\ne0$ and explicitly
quantifies over every real orthogonal matrix, while separately constructing
an attaining one. No classification of all minimizers is asserted.

## Evidence

The result is
`D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.result` in
[the Lean source](../D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.lean).
Its complete mathematical exposition is the corresponding
[Blueprint](../Blueprint/D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.md).
Canonical frozen membership is recorded at
`Golden/Frozen/state/D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.lean.json`.
The axiom closure uses only `Classical.choice`, `Quot.sound` and `propext`;
there is no `sorryAx` or additional axiom.

The retained Reg source has accepted kernel, sorry and axiom evidence.
Its current binding remains incomplete under the linked-issue exception:
[issue #24912](https://github.com/the-omega-institute/trureturing/issues/24912).
An extracted `declared_validated` row is not evidence of completed binding.

## Triage

- **Proved:** for every positive natural dimension and every nonsingular
  real square matrix, all real orthogonal $Q$ have objective at least one
  and some real orthogonal $Q$ attains one. The resolution kind is `proved`
  for this optimization characterization.
- **Proved, consequence of the same two clauses:** the attained minimum
  and the infimum over the full orthogonal group equal one. A strict
  uniform bound $\beta(P)>1$ is impossible for any such $P$, and hence
  for every nonempty class of them.
- **Proved, mechanism of the displayed proof:** the chosen orthogonal
  coordinates make $PQ$ and its inverse lower triangular, and their
  entrywise absolute product has unit diagonal. The spectral argument
  does not require diagonalizability.
- **Unresolved:** a classification of every minimizing $Q$, quantitative
  stability near the minimum, and variants with a restricted set of
  orthogonal transformations are outside this theorem. They receive no
  new theorem or admission from this source resolution.
- **Unresolved:** exhaustive worldwide literature coverage and historical
  priority are not established by the bounded source screen.

## ASSUMED-UNVERIFIED

The source attribution and bounded literature conclusions use the retained
primary-source and preregistration evidence. They do not certify present
MathOverflow answer status, global novelty or priority. Current Reg binding
is explicitly unfinished under issue #24912; successful compilation and
CI do not replace the missing binding evidence. The result concerns the
stated positive-dimensional nonsingular domain and makes no assertion
about singular matrices, dimension zero, or every possible minimizer.
