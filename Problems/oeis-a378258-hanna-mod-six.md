---
slug: oeis-a378258-hanna-mod-six
bibkey: hanna2024a378258
doi: null
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaA378258ModSix.result
url: https://oeis.org/A378258
---

## Problem

Paul D. Hanna's OEIS A378258 Comments state: "Conjecture: a(n) is not congruent to 1 nor 5 (mod 6) for n > 1."
The Name states: "G.f. satisfies A(x) = B(x) + 5*A(x)^2 where B(A(x) - A(x)^2) = x."
The separate preregistration is [#25601](https://github.com/the-omega-institute/trureturing/issues/25601).

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Rational formal series with offset one and a(1)=1 | The original `HannaA378258SquareRootParity.IsGF A`: constant coefficient zero, linear coefficient one. |
| Both equations, including existential B | The same original predicate, without replacing either equation by a weaker consequence. |
| Existence | The first conjunct of `claim`, reused from the frozen parity result. |
| Every normalized solution | Universal rational `A` satisfying that original predicate. |
| Every natural n>1 | Universal `n : ℕ` with `1 < n`; no cutoff. |
| Integer coefficient excluding both residues | An integer `z` with `coeff n A = (z : ℚ)`, `z % 6 ≠ 1`, and `z % 6 ≠ 5`. |

## Motivation

The frozen parity theorem confines odd coefficients to powers of two. The missing information is divisibility by three at those degrees. A reflection identity derived from the reduced source equations supplies it without a symmetry hypothesis.

## Gap

The literal conjecture is distinct from the parity claim settled under #18825. The accessible OEIS entry supplies both conjectures and algebraic formulas, but no proof of this separate claim. The bounded source and prior-formalization screen is recorded in #25601. Literature completeness and external open status beyond that screen are `ASSUMED-UNVERIFIED`; no global priority is asserted.

## Route

Use the frozen parity result to choose an integer representative for every coefficient of any normalized rational solution A, taking degree zero from normalization. The resulting integer series F maps exactly to A. Injectivity of the integer-to-rational coefficient map and its compatibility with substitution give

$$ (F-5F^2)\circ(F-F^2)=X. $$

Modulo three this is $(F+F^2)\circ(F-F^2)=X$. Both factors have constant coefficient zero and linear coefficient one, so they are mutual compositional inverses.

The normalized inverse-pair system has a unique solution over any commutative domain where two is nonzero. To compare F and G, set $H=F\circ(F+F^2)$ and $K=G\circ(G+G^2)$. The reverse inverse equations give $H-H^2=K-K^2=X$. Mathlib uniqueness of the compositional inverse of $X-X^2$ gives $H=K$. Consequently $F+F^2$ and $G+G^2$ have the same compositional square, and the existing `HannaHalfIterateCubicModThree.half_unique` identifies them. The unit $1+F+G$ then gives $F=G$.

Swapping the inverse factors and conjugating by $X\mapsto-X$ shows that $-F(-X)$ solves the same normalized system. Uniqueness proves $F=-F(-X)$. Over $\mathbb F_3$ every even-degree coefficient therefore vanishes. For n>1, an odd integer coefficient must, by frozen parity, occur at $n=2^k$ with k>0; this is an even degree, so three divides the coefficient. Even coefficients and odd multiples of three both exclude remainders one and five modulo six.

## Falsifier

A normalized source solution and degree n>1 with an integer coefficient congruent to one or five modulo six would refute `claim`. Neither finite coefficient testing nor an added reflection assumption establishes the target. The reflection identity here is derived for every reduced normalized source solution.

## Evidence

`HannaA378258ModSix.result : claim` proves the exact quantified target. This implementation is returned for independent review before freeze/deposit, publication or KPI counting. The source and its Reg mirror compile through the cache-guarded scoped entry. Their axiom closures are contained in `{propext, Classical.choice, Quot.sound}`. The current scoped evidence is supplied with the implementation handoff.

The source-owner mirror `Reg/D5/S1/Recurrence/Invariants/HannaA378258ModSix.lean` enrolls the existing dependent-family template. Its law preserves existence, the original `IsGF`, every degree, the integer witness and both excluded residues. The equivalence bridge is exact. A constant-one family violates the law at degree two, giving whole-family variation and one-role sensitivity. Observation dependence uses degrees two and three of an actual normalized solution: frozen parity makes one coefficient odd and the other even. The current report binds the original `claim` definition and its exact coefficient occurrence. The continuation is `.unknown`; this proves neither undecidability nor inexhaustibility.

## Triage

The new implication is that every even-degree coefficient of an integral normalized source solution is divisible by three. The proof's reflection mechanism applies to the inverse-pair system over any commutative domain of characteristic different from two. These are consumed intermediate steps, not separately claimed external problem settlements.

The final exclusion covers every normalized rational solution and every natural n>1. The separate first-negative-term assertion remains outside the result. No further source theorem depending on the modulo-six conjecture is identified in the inspected entry.

## ASSUMED-UNVERIFIED

The literature screen is bounded, and no global priority is asserted. Source correspondence uses the original OEIS equations and normalization. Independent review, freezing, required checks, merge and synchronization remain caller-owned. The residual continuation is unknown; the four-slot evidence is supplied in the source-owner Reg mirror.
