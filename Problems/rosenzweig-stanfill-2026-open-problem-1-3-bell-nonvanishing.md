---
slug: rosenzweig-stanfill-2026-open-problem-1-3-bell-nonvanishing
bibkey: rosenzweig2026loglaplacian
doi: 10.48550/arXiv.2606.04225
url: https://arxiv.org/abs/2606.04225
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/LogLaplacianBellNonvanishing.result
---

# Rosenzweig–Stanfill Open Problem 1.3

## Problem

Rosenzweig and Stanfill state in Open Problem 1.3 (arXiv:2606.04225v1, page 2):

> Show that $p_{2m,S_1}(\tfrac{1}{2}-m)\neq0$ for all $m\in\mathbb{N}$ where the sequence $S_1$ satisfies \eqref{Eq:S1}.

Their Definition 1.1 gives the Bell-polynomial expression

> Given a sequence of numbers, $S$, indexed over a set $J\supseteq \mathbb{N}$, we define $p_{j,S}(t):=\sum_{k=0}^j \frac{(-1)^k}{k!} \widehat{B}_{j,k}(s_1,\dots,s_{j-k+1})t^k=\frac{(-1)^j}{j!}\det\mathcal{N}_{j,S}(t),\quad j\in\mathbb{N}_0,$

and equation (1.8) gives

> $s_k^{(1)}=(1-2^{1-k})\frac{2 B_{k}}{k}=-\frac{2}{k}B_k(1/2),\quad k\in\mathbb{N}.$

The Lean encoding uses `m : ℕ` with `1 ≤ m` for the source's positive naturals and uses the first Bell-polynomial expression.

## Motivation

The paper leaves this numbered problem open. The frozen declaration
`D5/S3/ArithSums/LogLaplacianBellNonvanishing.result` proves its quantified nonvanishing statement for every positive natural index.

## Gap

Issue #11490 preregistered the Tier 1 external open problem, the verbatim source statement, the literature check, and the 2-adic route before Lean implementation. The bounded search recorded `not-found-in-searched-scope`; the paper's v1 text explicitly presents Open Problem 1.3 as unproved.

## Route

The proof works over the 2-adic valuation on `ℚ`.

1. Odd-index sequence entries vanish, so only even Bell-profile indices contribute.
2. The von Staudt–Clausen formula gives the exact 2-adic valuation of each even Bernoulli number.
3. After scaling by `24^m m!`, every nonprincipal profile has strictly positive valuation, while the unique profile with `j₂ = m` has valuation zero.
4. The ultrametric inequality makes the scaled sum nonzero, and hence the original Bell value is nonzero.

## Falsifier

A counterexample would be a positive `m` for which the Bell-polynomial sum defining `pBell (2*m) S1 ((1:ℚ)/2-m)` is zero. The proof route would also fail if the valuation comparison did not separate the principal profile from every other nonzero profile.

## Evidence

The module compiles with the pinned Lean toolchain and standard axioms. Its public declarations are `BellProfile`, `bellOrdinary`, `pBell`, `S1`, `claim`, and `result`; `result` has type `claim`.

The source note is `Library/Analytic/rosenzweig2026loglaplacian.md`, which records arXiv:2606.04225v1, the DOI locator, the quoted problem, and the relevant definitions.

## Triage

Tier 1 external named open problem, preregistered in issue #11490 before implementation. Resolution: proved. Admission basis: `open-problem-resolution`. The module has no project-level frozen prerequisites and imports only pinned Mathlib.

| declaration | proof_shape | escape witness |
| --- | --- | --- |
| `result` | content | form (1), W1 and W2 on the live proof path |
| private `scaledEntry_pos_val` (W1) | content | nonprincipal even Bell profiles have strictly positive scaled 2-adic valuation |
| private `scaled_pBell` (W2) | content | the defining Bell sum equals the scaled finite-profile sum |

The two witnesses are preregistered in [route v2 of #11490](https://github.com/the-omega-institute/trureturing/issues/11490#issuecomment-5913994997). Every other coefficient valuation, factorial estimate and ultrametric fact is local to its consuming proof. The factorial-valuation bound and strict step are direct upstream applications and are not separate declarations.

### What the settlement shows

**Proved.** The 2-adic valuation argument establishes nonvanishing uniformly for every positive `m`; the unique valuation-zero Bell profile is the one with `j₂ = m`, and all other nonzero profiles have positive valuation after scaling. The result therefore extends across the full quantified domain in Open Problem 1.3, with no numerical cutoff.

**Formalization boundary.** The Lean theorem is the exact rational Bell-polynomial statement encoded by `claim`; the displayed source determinant identity and the analytic fundamental-solution consequences are not part of this module's formal conclusion.

**Open.** The bridge from this result to the paper's separate Open Problem 1.6(i), and any analytic consequence requiring the paper's Theorem 1.2 and residue formula (1.7), remains open in this repository.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish exhaustive worldwide novelty or priority. The source has one arXiv version (v1, 2 June 2026); no claim is made about later unpublished work.
