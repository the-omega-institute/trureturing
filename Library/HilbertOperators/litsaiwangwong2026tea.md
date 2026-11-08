---
bibkey: litsaiwangwong2026tea
authors: Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong
year: 2026
title: "Linear maps of C*-algebras preserving norm parallelism"
doi: 10.48550/arXiv.2611.06187
url: https://arxiv.org/abs/2611.06187v1
claim: "Problem 1.1 asks whether complex-linear bijections between arbitrary complex C*-algebras preserving triangle equality attaining pairs in both directions are scalar multiples of isometries."
strata_touched:
  - D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers
license: citation-only
triage: anchor
---

# Linear maps of C*-algebras preserving norm parallelism

## Verified locator

DOI: 10.48550/arXiv.2611.06187

Source: https://arxiv.org/abs/2611.06187v1

Problem 1.1 is on page 4 of the versioned PDF. The definitions of parallelism and triangle equality attaining pairs are on page 1. The following quotations retain the TeX source's mathematics.

## Problem 1.1

> For which complex $C^*$-algebras $\mathcal A,\mathcal B$ must every
> linear bijection $T:\mathcal A\to\mathcal B$ preserving parallelism
> in both directions be a scalar multiple of an isometry?
> Does the same conclusion hold for arbitrary complex $C^*$-algebras
> if TEA pairs are preserved in both directions?

Only the TEA clause is the target. The conclusion means a nonzero complex scalar times a surjective complex-linear isometry. Nonunital and zero algebras are included, and continuity is not a hypothesis.

## Definitions

> Two elements $a,b$ in a normed space $E$ over $\mathbb F=\mathbb R$ or
> $\mathbb C$ are said to be \emph{norm parallel}, or simply
> \emph{parallel}, if
> $\|a+\lambda b\|=\|a\|+\|b\|$
> for some $\lambda\in\mathbb F$ with $|\lambda|=1$.

> In this case, we write $a\parallel b$. If this equality holds specifically with $\lambda=1$, then
> $(a,b)$ is called a \emph{triangle equality attaining} (TEA) pair.

The Lean encoding takes complex scalars, `NonUnitalCStarAlgebra` carriers and unbounded `LinearMap`s. A TEA pair has the literal condition `‖a + b‖ = ‖a‖ + ‖b‖`. Both directions mean this predicate is equivalent before and after the map on every pair. The scalar representation uses `A ≃ₗᵢ[ℂ] B` and a complex scalar different from zero.

## Evidence boundaries

The numerical experiment is in `the-omega-institute/trureturing-experiments`, commit `0a8b5b395bf1de576349641f772fce816ed17ab2`, `docs/reports/li-tsai-wang-wong-2026-tea-preservers/check.py`, SHA-256 `df7abc38df4149a730114037dcfad1740e3e4b877efe0c7b4db8f92e8c116dfb`. The preregistration #27007 records exit 0 and `ALL_CHECKS_OK`; this is computational evidence, not a universal proof.

The source's finite-dimensional, commutative and type-I results remain valid within their stated hypotheses. The TEA conclusion removes those restrictions on the source clause; no assertion about the parallelism-only question or arbitrary real C*-algebras follows. Literature completeness is `ASSUMED-UNVERIFIED` as recorded in #27007.
