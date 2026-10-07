---
slug: abdesselam-2022-xy-pgg-cycle-refutation
bibkey: abdesselam2022nonabelian
doi: 10.48550/arXiv.2207.07603
url: https://arxiv.org/abs/2207.07603v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.result
---

# Abdesselam's Problem 2: padded general Ginibre inequalities for the XY model

## Problem

Abdelmalek Abdesselam, “Non-Abelian correlation inequalities and stable
determinantal polynomials”, arXiv:2207.07603v2, §4, Problem 2, printed p. 14:

> For the XY model, or O(2) model, the GG inequalities were proved by
> Ginibre [18]. What about the padded generalizations given by the PGG
> inequalities?

The free O(2) measure is the product of the rotation-invariant probability
measures on S¹. Its angle coordinates use normalized Haar measure on
Real.Angle, with spin θ = (cos θ, sin θ). The basic observables are all pair
inner products σᵢ·σⱼ, i < j. The parity map assigns one bit to each endpoint
of each pair; the source's evenness means ρ(u) = 0.

For every p ≥ 1, the proposed assertion requires, for every m ≥ 0, every
natural row matrix V, every ε ∈ {−1,1}ᵐ, and every even natural padding u,

$$
\int_{X^2} \mathcal O(x)^u\mathcal O(y)^u
\prod_{i=1}^{m}\left[\mathcal O(x)^{V_{i*}}
+\varepsilon_i\mathcal O(y)^{V_{i*}}\right]
\,d\mu(x)\,d\mu(y) \ge 0.
$$

The Lean `claim` retains these quantifiers and the literal duplicated
integral. Its evenness premise is inline: `parity p (fun e => (u e : ℤ)) = 0`.
The sole settling theorem is `result : ¬ claim`.

## Motivation

Ginibre's GG inequalities for the XY model do not answer whether inserting
an arbitrary even natural padding preserves the entire PGG collection.
One admissible negative padded integral refutes that universal assertion.

## Gap

Tier 1; preregistration issue #13353 quotes Problem 2 and the complete PGG
statement. Its literature check reports no settlement in the searched
paper-title, padded-Ginibre, XY-PGG and MathDB queries. The existing
repository settlement of Problem 3 concerns determinantal polynomials and
arbitrary positive exponents, a separate question. The literature conclusion
is `not-found-in-searched-scope`.

## Route

Take p = 5 and cycle edges (0,1), (1,2), (2,3), (3,4), (0,4). Let u be their
indicator, m = 2, both rows Vᵢ = u, and both signs εᵢ = −1. Every vertex has
two incident cycle edges, so ρ(u) = 0. Put Z(x) equal to the product of the
five edge observables and Mₖ = E[Zᵏ].

Expanding each cosine power into Fourier characters and integrating the
five independent angles leaves only constant edge frequencies around the
cycle. The first three moments are M₁ = 1/16, M₂ = 17/512, M₃ = 61/4096.
Product integration evaluates the padded functional as

$$
E[Z(x)Z(y)(Z(x)-Z(y))^2]
=2(M_1M_3-M_2^2)=-\frac{45}{131072}<0.
$$

## Falsifier

The refutation requires the normalized free O(2) measure, the pair inner
products, zero endpoint parity of u, allowed signs, the three exact moments,
and the product-integral reduction. All of these obligations occur in the
proof of `result`. A mismatch in any of them would invalidate this witness.

## Evidence

`D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.result` has closed type
`¬ claim`. Its proof imports only pinned Mathlib Fourier and product-integral
machinery. Every helper proposition is local to the proof. The axiom closure
is contained in {propext, Classical.choice, Quot.sound}; no new axiom,
`sorry`, floating-point certificate, or `native_decide` is used.

## Triage

`theorem`. The universal XY-PGG assertion is refuted. The settling proof is
`bind-only`, with escape witness `none` and admission basis
`open-problem-resolution (#13353; Refuted)`.

### What the settlement shows

- [proved: D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.result]
  The five-cycle instance satisfies every source premise and has negative
  PGG value −45/131072. Endpoint evenness does not force the monomial Z to
  have a fixed sign. The factor (Z(x)−Z(y))² is nonnegative, but its padding
  factor Z(x)Z(y) can be negative. The exact first three moments establish
  that the negative contribution exceeds the positive contribution.
- [computed] For the candidate cycle-moment formula
  Mₖ = 2^(−kℓ) Σᵣ₌₀ᵏ binomial(k,r)^ℓ, exact rational evaluation gives:

  | ℓ | M₁ | M₂ | M₃ | 2(M₁M₃−M₂²) |
  | --- | --- | --- | --- | --- |
  | 3 | 1/4 | 5/32 | 7/64 | 3/512 |
  | 4 | 1/8 | 9/128 | 41/1024 | 1/8192 |
  | 5 | 1/16 | 17/512 | 61/4096 | −45/131072 |
  | 6 | 1/32 | 33/2048 | 365/65536 | −359/2097152 |

  Reproduction command: `python3 -` with the following stdin program; exit 0.
  SHA256 of the program's UTF-8 bytes, including its terminal newline:
  `d559c1b407d4a81e84c1c33ca8c68466fba3d9a29cbd5d61529acd859f0d619b`.

  ```python
  from fractions import Fraction
  from math import comb
  for ell in (3, 4, 5, 6):
      moments = [Fraction(sum(comb(k, r)**ell for r in range(k + 1)), 2**(k * ell)) for k in (1, 2, 3)]
      value = 2 * (moments[0] * moments[2] - moments[1]**2)
      print(ell, *moments, value)
  ```

  The tested scope is ℓ ∈ {3,4,5,6} and k ∈ {1,2,3}. Only the five-cycle
  moments are kernel-checked as actual XY spin integrals in this module.
  The positive computed values for ℓ = 3,4 are surviving instances of the
  candidate formula, without a universal positivity conclusion.
- [open] Establish the general cycle-moment formula for the actual XY
  measure and the negative PGG value for every ℓ ≥ 5. The finite evaluations
  above do not establish the unbounded extension.
- [open] Establish the reported tensor-moment extension for every N ≥ 2
  and every ℓ ≥ 5. This module proves the O(2), five-cycle instance only.
- [open] Evaluate the same padding with a = b = u against equation
  `(Oinframod)`, the O(N) branch of Problem 1. It is a separate question.
- [open] Determine conditions on padding that restore PGG positivity. In
  particular, u = 0 removes the sign-changing padding factor for this
  two-identical-row, two-negative-sign construction. A full characterization
  of allowed padding and the other sign/row choices is not proved here.
- [open: formal verification of the cited GG theorem] The GG inequalities cited in Problem 2 retain their stated
  range. Problem 2 is a question, rather than a premise of a theorem in the
  source. This refutation supplies its negative answer; it does not settle
  Problems 1 or 4, or change the separate Problem 3 settlement.

## ASSUMED-UNVERIFIED

The literature status in #13353 is a scoped, orchestrator-reported search,
not an exhaustive priority determination. The general cycle-moment and
all-N extensions are open here. Angle coordinates use the normalized Haar
convention explicitly allowed in #13353. Distinct model families for
codex-cli and ChatGPT Pro are not established.
