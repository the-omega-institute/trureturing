---
slug: chakraborty-patra-2026-ideal-zero-product-conjecture-4-2
bibkey: chakrabortypatra2026idealzeroproduct
doi: 10.48550/arXiv.2608.14618
url: https://arxiv.org/html/2608.14618v1#S4.Thmtheorem2
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Algebra/ChakrabortyPatraIdealZeroProductRefutation.result
---

# Chakraborty–Patra Conjecture 4.2

## Problem

> Let \(R\) be a finite commutative ring with identity and let \(k\ge2\).
> If \(\zeta_k(R)=1-\frac{1}{2^k},\) then \(R\) is a field.

Definition 2.1 uses all ordered k-tuples of actual ideals of R, with
repetitions and with both zero and the unit ideal. It divides the number
with zero ideal product by the positive total number of tuples. The same
ring R is the subject of the field conclusion.
[Conjecture 4.2](https://arxiv.org/html/2608.14618v1#S4.Thmtheorem2) ·
[Definition 2.1](https://arxiv.org/html/2608.14618v1#S2.Thmtheorem1)

## Motivation

A finite field has exactly two ideals. Its zero-product probability counts
all tuples except the tuple of unit ideals. The conjecture asks whether the
same probability at a single k determines whether the ring is a field.
[Proposition 4.1](https://arxiv.org/html/2608.14618v1#S4.Thmtheorem1)

## Gap

A square-zero ideal can account for zero products among many proper
ideals at once. The ratio can then coincide with the field ratio even
though the number of ideals and the pattern of zero products differ.
Complete annihilating-ideal graphs capture products of distinct nonzero
annihilating ideals. For the probability one must also count the diagonal
and all ordered pairs involving zero and the unit ideal.
[Behboodi–Rakeei, Theorem 2.7](https://arxiv.org/html/0808.3187v2#p72)

## Route

Take the square-zero extension of the binary field by its two-dimensional
vector space, with multiplication \((a,u)(b,v)=(ab,av+bu)\).
All elements with nonzero scalar part are units. The proper ideals lie in
the square-zero kernel, where the ring acts through its scalar coordinate.
A proper ideal containing two distinct nonzero vectors contains their
sum, the third nonzero vector. The resulting three line ideals, the
kernel, zero and the unit ideal exhaust the lattice and are distinct.

The 25 ordered pairs of proper ideals have zero product. Among pairs with
the unit ideal, only the two orders of zero and the unit ideal have zero
product. The fraction at k = 2 is 27/36 = 3/4. The same ring contains the
nonzero element \((0,(1,0))\), whose square is zero.

## Falsifier

The refutation requires a bijection with the actual ideals and an
equivalence of the zero-product predicates on ordered pairs. A missing
ideal, an extra counted pair, a mismatch with the field probability at
k = 2, or failure of the nonzero square-zero witness would defeat it.

## Evidence

Lean proves the literal negation of the universal proposition as
`D5/S0/Certificates/Algebra/ChakrabortyPatraIdealZeroProductRefutation.result`.
The proof uses Mathlib's native square-zero extension and native ideal
multiplication. It transports the ordered subtype of actual ideal tuples
to finite labels before computing its cardinality. The scoped Lean target
is `D5.S0.Certificates.Algebra.ChakrabortyPatraIdealZeroProductRefutation`.
[Versioned source and attribution](../Library/Certificates/chakrabortypatra2026idealzeroproduct.md) ·
[Problem #33639](https://github.com/the-omega-institute/trureturing/issues/33639)

## Triage

### What the settlement shows

The exact field probability at k = 2 does not imply that a finite
commutative ring with identity is a field.
[Lean result](../D5/S0/Certificates/Algebra/ChakrabortyPatraIdealZeroProductRefutation.lean)

The source's field-to-probability implication remains Proposition 4.1.
For this witness, a tuple has nonzero product exactly when all factors
are the unit ideal or one factor is one of the four nonzero proper ideals
and all others are the unit ideal. This gives the source-level count
\(\zeta_k(R)=1-(1+4k)/6^k\) for k at least two. In particular the count
at k = 3 gives 203/216, distinct from the field value 7/8. The Lean
refutation uses the k = 2 case.

Every element outside the kernel is a unit, so the counterexample is local.
Its maximal ideal is nonprincipal because every nonzero element of it
generates a two-element line. The paper's formulas for chain rings and
principal ideal rings retain their stated hypotheses. Conjecture 4.11 asks
whether agreement of the entire sequence for finite principal ideal rings
determines their multiset of Loewy lengths. Its status is open here.
[Proposition 4.1](https://arxiv.org/html/2608.14618v1#S4.Thmtheorem1) ·
[Conjecture 4.11](https://arxiv.org/html/2608.14618v1#S4.Thmtheorem11)

## ASSUMED-UNVERIFIED

The bounded literature screen located no earlier settlement. Worldwide
priority, unindexed work, and complete reverse-citation coverage are
unverified. The general-k count and the scope observations are
source-level deductions from the ideal classification.
