---
slug: mathoverflow-513954-singular-diagonal-downdate-inertia
bibkey: lucid2026structureddowndate
doi: null
url: https://mathoverflow.net/revisions/513954/2
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/StructuredRankOneFamily.mo513954_revision2
---

# Inertia of a singular diagonal matrix after a structured rank-one downdate

## Problem

The source is Lucid (MathOverflow user 596445), revision 2 of [MathOverflow question 513954](https://mathoverflow.net/revisions/513954/2), revision GUID `1084D752-1BBD-405E-B335-28FBDD1F4D6D`. The [Library note](../Library/QuadraticForms/lucid2026structureddowndate.md) is the sole source acknowledgement and records the CC BY-SA 4.0 license.

The source asks:

> I ran into this while working through a rank-one perturbation problem and got stuck on the case where $D$ is singular.
> Let $D = \operatorname{diag}(d_1, \dots, d_n)$ be real diagonal, possibly singular, and let $x \in \mathbb{R}^n$ satisfy
> $$\Delta := x^\top D x \neq 0.$$
> Set $w = Dx$ and
> $$M = D - \frac{ww^\top}{\Delta}.$$
> Writing $\operatorname{inertia}(A) = (n_+(A), n_-(A), n_0(A))$, is the following formula always valid?
> $$\operatorname{inertia}(M) = \begin{cases} (n_+(D) - 1,\ n_-(D),\ n_0(D) + 1), & \Delta > 0, \\ (n_+(D),\ n_-(D) - 1,\ n_0(D) + 1), & \Delta < 0. \end{cases}$$
> I specifically want a proof that doesn't assume $D^{-1}$ exists.
> Note: this isn't the general rank-one update $D + \rho vv^\top$ for arbitrary $v$ (the classical secular-equation setting) , here $w = Dx$ is tied to $D$ itself, with coefficient exactly $1/\Delta$, chosen so $x$ becomes an exact null vector of $M$. I'm after the inertia count specifically, including the singular-$D$ case and the index-tracking behavior in the corollary below.
> Here's what I've tried. Define $H = \{z : w^\top z = 0\}$. Since $w^\top x = \Delta \neq 0$,
> $$\mathbb{R}^n = H \oplus \operatorname{span}\{x\}.$$
> If $Z$ contains a basis of $H$ and $P = [Z \ \ x]$, then
> $$P^\top D P = \begin{pmatrix} Z^\top D Z & 0 \\ 0 & \Delta \end{pmatrix}, \qquad P^\top M P = \begin{pmatrix} Z^\top D Z & 0 \\ 0 & 0 \end{pmatrix}.$$
> Does Sylvester's law of inertia immediately establish the displayed formula, including all additional null directions when $D$ is singular?
> A related corollary: suppose $D(y)$, $x(y)$, and hence $M(y)$, vary continuously on $X \setminus A$, where $X$ is homeomorphic to an open $(n-1)$-simplex, $n \geq 3$, and $A$ is finite. If $\Delta(y) \neq 0$ and $M(y) \succeq 0$, does path-connectedness imply that $\Delta$ has constant sign and, when negative, exactly one fixed diagonal index of $D(y)$ remains negative throughout?
> I've checked the inertia formula numerically for random $D$, $x$ up to $n = 9$, including singular $D$, and haven't found a counterexample.

This is one full unit: the complete two-sign inertia triple and the continuous-family sign/fixed-negative-index corollary. The matrix clause ranges over every finite dimension and retains singular diagonal matrices; the family clause keeps the open-simplex-minus-finite-points domain, continuous families, nonzero pivot and pointwise positive semidefiniteness. No invertibility, connected-family replacement, dimension cutoff, tolerance or spectral-gap premise is added.

## Motivation

The question asks whether the structured downdate removes exactly the pivot sign and adds one null direction, even when the original diagonal form is singular, and whether the source domain forces one global sign and one global negative coordinate in the negative case.

## Gap

The source's proposed hyperplane decomposition and block congruences identify the decisive standard mechanism. The bounded source and literature check recorded in issue [#25408](https://github.com/the-omega-institute/trureturing/issues/25408) did not read a complete original settlement of this exact full unit. That bounded check does not establish exhaustive openness, priority or absence of related results.

## Route

The inertia module proves the kernel split directly, derives the nullity increase from rank-nullity, and uses two determinant-one block congruences with the standard Hermitian inertia invariant. Characteristic-polynomial roots give positive and negative counts with multiplicity, and the real diagonal count handles singular entries. The Family module transports the punctured simplex through an explicit log-ratio chart, obtains path connectedness from the finite-complement theorem, and applies the continuous nonzero-pivot sign dichotomy. In the negative branch, positive semidefiniteness forces zero negative index after the inertia identity; the diagonal sign count and a clopen fixed-index partition give one index negative everywhere and all others nonnegative.

## Falsifier

A falsifier must exhibit either a finite real diagonal matrix and vector with nonzero pivot for which one of the two complete inertia triples or its multiplicities fails, or a family satisfying the exact source domain and hypotheses for which the pivot changes sign or no single index is negative throughout the negative branch. A counterexample using an invertibility, connectedness, tolerance, dimension or spectral-gap premise outside the source does not address this unit.

## Evidence

The frozen host is `D5/S3/QuadraticForms/StructuredRankOneFamily.mo513954_revision2`. Its theorem is the conjunction of the finite-dimensional `StructuredRankOneInertia.inertia_downdate` specialization and the complete `continuous_family` clause. The two canonical freeze doors produced current state records for `StructuredRankOneInertia` and `StructuredRankOneFamily`; the existing Lean and Scribe source bytes were unchanged.

The matrix source uses the author's proposed block-congruence mechanism and standard Sylvester inertia. The exact repository derivations also include the kernel and nullity arguments, both signs, all zero multiplicities and singular inputs. The family source includes the original domain transport, nonemptiness, constant pivot sign and globally unique negative index. These are repository-derived formal results; the MathOverflow revision supplies the question and proposed mechanism, not an attestation of the completed proof.

The four-slot audit targets `diagonal_counts`, `kernel_split`, `nullity_downdate`, `inertia_downdate`, `punctured_simplex_pathConnected`, `continuous_family` and `mo513954_revision2` remain unfinished under issue #25408. The accepted linked-issue exception is disclosed here; it is not a validation status and does not add a new theorem or audit gate.

## Triage

This is a Tier 1 external named open problem, resolved as **Proved** for the one complete unit by the frozen host theorem. The decisive mechanisms are the authored hyperplane/block-congruence proposal and standard Sylvester inertia, together with the repository's kernel, spectral-count and topological transport derivations. The proved generalization retains every finite dimension, both pivot signs, singular diagonal inputs, multiplicities, the exact punctured-simplex domain and the pointwise positive-semidefinite family hypothesis. The source dependence is limited to the question's statement and proposed mechanism; the proof and its full conjunction are repository-derived.

The source's remaining successor is the precise audit and publication-completeness work tracked by #25408. It does not reopen the mathematical statement, add an ordinary novelty or priority claim, or count follow-up audit and delivery work as another solved problem.

## ASSUMED-UNVERIFIED

The bounded literature qualification does not establish worldwide absence, priority or author acceptance. Numerical checks and the source's informal proposal are not used as proof. No successor mathematical claim beyond the exact full unit is asserted.
