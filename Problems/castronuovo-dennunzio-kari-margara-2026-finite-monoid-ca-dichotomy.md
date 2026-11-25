---
slug: castronuovo-dennunzio-kari-margara-2026-finite-monoid-ca-dichotomy
bibkey: castronuovo2026groupcaentropy
doi: null
url: https://arxiv.org/abs/2611.16746v1
triage: theorem
motivation_gids:
  - D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.localMap
---

# The finite-monoid extension of the entropy dichotomy

## Problem

Castronuovo, Dennunzio, Kari and Margara ask in the second research direction of
§9, printed p. 32, of [arXiv:2611.16746v1](https://arxiv.org/pdf/2611.16746v1#page=32):

> It would be interesting to understand whether the dichotomy extends to cellular automata over finite monoids, and more generally which algebraic constraints force it.

The first clause asks whether the dichotomy in Theorem 6 (p. 21) extends to
finite monoids. For every natural dimension D ≥ 2 and finite monoid A, equip the
full shift of all functions from Fin D → ℤ to A with the product discrete
uniformity. For every unital pointwise monoid endomorphism F of that full shift
with a finite local presentation, continuity and commutation with all
translations, the proposed alternative is uniform equicontinuity of all forward
iterates with full-shift topological entropy zero, or sensitivity with full-shift
topological entropy +∞. The Lean result is the literal negation of this closed
proposition.

## Motivation

Finite group automata satisfy this alternative by Theorem 6. The finite-monoid
case retains a full-shift endomorphism and finite local presentation. It tests
whether these assumptions force the same restrictions when alphabet elements
need not have inverses.

## Gap

The finite group theorem gives neither alternative for the Boolean semilattice
monoid. At source scale 2⁻ʳ, strict input closeness means agreement on the
entire centered radius-r box. The question requires the uniform dynamics and the
entropy of the entire configuration space.

## Route

Take the alphabet Bool with OR multiplication and false identity. In dimension
two, the local rule takes the OR of the origin and the two positive coordinate
neighbors. A single true immediately outside a box reaches the origin along
the first axis. Every true site persists, so every coordinate trace of length
n is determined by a first true time or the sentinel n. For each finite W,
the realized trace count is at most (n + 1)^|W|. Matching traces are exactly the
dynamical entourage classes, which gives one spanning center per realized
trace. The cofinal centered boxes and the subexponential trace bound give
full-shift entropy zero. With propagation and zero entropy, each alternative
leads to a contradiction.

## Falsifier

A violation of the unit or multiplication law would invalidate the monoid
example. A missed coordinate in the strict source distance correspondence, a
seed that fails to reach the origin, or a true-to-false transition in a site
trace would invalidate the corresponding step. An initial flip at either
positive coordinate neighbor changes the output at the origin.

## Evidence

The settling declaration is
`D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.result`. The native local
map is `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.localMap`. The source
distance and its box basis identify the source predicates with the
product-uniform ones. The orbit of the all-true configuration is fixed, and
agreement with it on a box persists under every iterate, yielding an
independent failure of sensitivity. [Issue #32397](https://github.com/the-omega-institute/trureturing/issues/32397#issuecomment-7048015750)

## Triage

Tier 1 external open problem under issue #32397. The settlement is a
refutation with substantive proof content from the propagating seed and the
first-true-time trace construction. Its admission basis is
`open-problem-resolution`. The exact Lean result negates the full
entropy-bearing dichotomy.

### What the settlement shows

- **Proved in this module.** The OR rule propagates a true seed from arbitrarily
  far outside an input box to the origin, which rules out uniform equicontinuity.
  At each site the center term preserves true, so a trace can switch at most
  once. The first true times give at most `(n + 1)^|W|` traces on a fixed window
  `W` over `n` steps. This yields zero full-shift entropy.
- **Source theorem.** Theorem 6 (p. 21) holds for finite group alphabets in
  dimensions `D ≥ 2`. A group cellular automaton is either equicontinuous with
  zero entropy or sensitive with infinite entropy.
- **Same-witness consequence.** Zero entropy and failure of equicontinuity for
  the Boolean OR automaton also refute the equicontinuity entry at `H = 0` in
  the monoid row of Table 2 (p. 31).
- **Open here.** Which algebraic constraints on finite monoids force the
  dichotomy, and whether finite strictly positive entropy can occur in the
  finite-monoid setting of Table 2.

## ASSUMED-UNVERIFIED

The bounded literature screen for issue #32397 found no settlement. It
does not establish priority outside the reviewed sources and search results.
The algebraic constraints that force the dichotomy, and whether finite
positive entropy occurs in the monoid setting of Table 2, remain open here.
