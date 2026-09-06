---
bibkey: vishnyakova2026polynomially
authors: Anna Vishnyakova
year: 2026
title: Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros
doi: 10.48550/arXiv.2608.03723
claim: Definition 1.4 specifies the normalized falling-Pochhammer linear operator; Example 6.2 exhibits the two quadratic inputs whose images are perfect squares; Example 6.4 defines its real-root parameter sets; Conjecture 6.5 proposes an upper bound on their even-degree extent.
strata_touched:
  - D5/S3/Zeros/PochhammerDeformation/QuadraticInterval
license: citation-only
triage: anchor
---

# Polynomially Deformed Normalized Pochhammer Sequences

The attribution covers the operator and the parameter-set definitions. The
quadratic closed form and its small-positive-parameter refutation are derived
in the repository. The refutation concerns the strict upper bound at degree
two, while the asserted interval shape at that degree holds. It makes no claim
about higher degrees, their monotonicity, or their limiting extent.

### Antecedent to distinguish: Example 6.2

Example 6.2 of the source already exhibits two inputs. Write `s = sqrt(a(a+1))`.
The two branches carry **different constant-term signs** and must be quoted
separately; compressing them into one `±` formula flips the negative branch:

- `P(x) = (x + (a + s)/2)^2`  gives  `L_a(P)(x) = (s x + (a + s)/2)^2`
- `P(x) = (x + (a - s)/2)^2`  gives  `L_a(P)(x) = (s x - (a - s)/2)^2`

Each image is a perfect square whose double root lies in `[-1,0]` (for `a > 0`
one has `s > a`, so `(a - s)/2 < 0` and the second root `(a - s)/(2s)` is
negative, of modulus at most one). Because `s = sqrt(a^2 + a)`, the two
parameters `(a ± s)/2` are **exactly the two endpoints** of the interval
classified here. The source therefore already establishes that both endpoints
belong to the degree-two parameter set, at the repeated-root boundary.

What this repository adds is disjoint from that antecedent:

1. **Necessity / whole-interval classification** — that the parameter set
   *equals* the closed interval between those endpoints, not merely contains
   them. The source states no such equality at even degree and writes that for
   even `n` "the situation is much more complicated".
2. **The closed form of the extent** `c_2(a) = (sqrt(a^2+a) - a)/2`. Stated
   precisely: the source gives no closed form at any even degree, and its
   sentence `The proof of this fact and the possible value of the limit ...
   remain open` refers to the general even-degree conjecture and to the limit,
   **not** to a separately declared open problem at `k = 1`. The increment here
   is a specific-case classification, not the resolution of a question the
   source singled out.
3. **The sharp threshold** `c_2(a) < 2a` iff `1/24 < a`, with equality at
   `a = 1/24`, refuting Conjecture 6.5's strict clause `0 < c_{2k}(a) < 2a`
   throughout `0 < a <= 1/24`. The source neither proves nor conjectures any
   sharpness statement in this direction.

This distinction was raised by an independent review seat reading the source,
not by the implementation; it is recorded here so the increment is not
overstated.

## Search Log

- 2026-09-06: Read the v1 HTML, including the mathematical `alttext` for
  Definition 1.4, Example 6.2, Example 6.4, and Conjecture 6.5. The last
  explicitly states the strict bound `0 < c_{2k}(a) < 2a`.
- 2026-09-06 (review round): an independent review seat identified Example 6.2
  as an antecedent supplying both interval endpoints. Re-read and confirmed
  against the source `alttext`; the antecedent and the increment are separated
  above.
- Searched pinned Mathlib, the repository's D5 declarations, installed Lean
  packages, and GitHub repositories for Lean Pochhammer formalizations.
  The unrelated GaussianWhoWhere project studies finite Hermite-Pochhammer
  translation rigidity. No matching interval classification was found in the
  searched scope. This is not a claim of worldwide priority.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2608.03723
- Version inspected: https://arxiv.org/html/2608.03723v1
- Definition: https://arxiv.org/html/2608.03723v1#S1.count4
- Conjecture: https://arxiv.org/html/2608.03723v1#S6.count5
