---
slug: gahramanov-mammadov-2026-pais-odd-poisson
bibkey: gahramanovmammadov2026pais
doi: null
url: https://arxiv.org/abs/2611.17457v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/Poisson/PaisPoissonNonisomorphism.result
---

# Gahramanov–Mammadov odd-resonance Poisson nonisomorphism

## Problem

Section 5.3, page 5, of arXiv:2611.17457v1, after (29), states:

> For m and n both odd no such rescaling exists, and we leave open whether the two algebras are isomorphic by a nonlinear change of generators.

The full real coordinate algebra is ℝ[u,v,x,y]/(x²+y²−uⁿvᵐ), where
u=H₁, v=H₂, x=X, y=Y and Ω=nω₁=mω₂. The two brackets are (23),
(26) and (27). The registered event quantifies over every coprime odd
natural m>n≥1 and every real Ω>0 and denies every real Poisson algebra
isomorphism. The formal result strengthens that parameter range to all
odd naturals n,m and nonzero real Ω. The quotient is the full presented
algebra, including all real characters.

| Source clause | Lean declaration |
| --- | --- |
| Equations (16), (21), relation and ideal quotient | Omega.PaisPoisson.relationPoly, relationIdeal, Paper |
| H₁,H₂,X,Y in generator order | Omega.PaisPoisson.qu, qv, qx, qy |
| Equations (23), (26), (27) | Omega.PaisPoisson.paperPoisson, quotientBracket_table with s=1 and s=−1 |
| Two genuine real Poisson brackets | Omega.PaisPoisson.RealPoissonBracket, paperPoisson |
| Arbitrary bracket-preserving real algebra equivalences | Omega.PaisPoisson.PreservesBracket |
| Universal odd obstruction | D5/S3/Geometry/Poisson/PaisPoissonNonisomorphism.result |

## Motivation

Diagonal rescalings account for the even exponent cases in the paper. The
odd case asks whether a nonlinear abstract algebra change can identify
the brackets. The preregistration and subsequent public result are in
[#34936](https://github.com/the-omega-institute/trureturing/issues/34936#issuecomment-7225843074).

## Gap

Tier 1 is appropriate for a recent math-physics paper posing a specific
question after an explicit partial classification. The versioned source
directly confirms the open statement and the limited scope of its
diagonal calculation. Literature discovery identified the primary
question, and the registered event fixes the quantifiers. No claim of
exhaustive worldwide literature coverage follows from the checked
version or from the independent proof replay.

## Route

Pass to the generator-preserving quadratic normal form
ℝ[c,v,x][y]/(y²−((c+v)ⁿvᵐ−x²)), c=u−v. A canonical central element
P+Qy satisfies P_x=0 and ((c+v)ⁿvᵐ−x²)Q_x−xQ=0. Leading coefficients in
the second equation force Q=0. Commuting with x then forces P_v=0,
so the canonical center is exactly ℝ[c]. The alternative central element
u+v has the origin as its sole real zero character, since odd n,m force
x²+y²=−u^(n+m) on that fiber. Each canonical c-fiber contains two
different real characters. An arbitrary real Poisson algebra equivalence
transports central elements and induces a bijection of real characters,
contradicting the singleton zero fiber.

## Falsifier

An actual unital real algebra equivalence of the stated full ideal quotient
preserving the signed brackets for every argument at any registered
odd pair and positive Ω would contradict the event. The scoped
formalization must also realize the exact relation, generator tables,
bilinearity, Leibniz and Jacobi. A published whole answer predating the
registered result would alter the open-problem provenance.

## Evidence

The public result records a kernel proof and independent replay under
Lean 4.35.0 with Mathlib commit 56a005855ea17e0b0958f73ec801ae140b0a1679.
The kernel axiom closure is propext, Classical.choice and Quot.sound.
The paper source and scope are in Library/LieTheory/gahramanovmammadov2026pais.md.
The public proof record is
https://github.com/the-omega-institute/trureturing/issues/34936#issuecomment-7226713190.
The theorem proves the strengthened all-odd statement.
The proof shape is content, with the nontrivial leading-coefficient
equation and real-character obstruction on the live proof path.

## Triage

- Proved. The full abstract real polynomial Poisson algebras are nonisomorphic
  for all odd natural exponents and all nonzero real Ω. Coprimality and strict
  ordering are unnecessary for the obstruction.
- Proved by the paper. If at least one exponent is even, (28) and (29) give
  the indicated abstract diagonal equivalences.
- Proved as a specialization. A polynomial Poisson algebra isomorphism
  preserving the physical domain is ruled out for the odd parameters.
- Open here. The separate problem of smooth or semialgebraic Poisson
  isomorphisms defined solely on the nonnegative physical invariant
  domain (30) is outside the established theorem.
- The same invariant argument applies whenever a central element on one
  side has a singleton real zero-character fiber and all nonempty zero
  fibers of the other center contain distinct characters. Extension to
  other resonant presentations is a separate mathematical question.

## ASSUMED-UNVERIFIED

Exhaustive literature novelty is outside the bounded source check.
No classification of the restricted smooth physical space is asserted.
