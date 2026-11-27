---
bibkey: alpoge2026dirichletgrh
authors: Levent Alpöge with Claude
year: 2026
title: The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)
doi: null
url: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md
claim: For every complex Dirichlet character of positive modulus, each zero of its L-function in the open critical strip has real part one half.
strata_touched:
  - D5/S3/Zeros/GRH
license: Apache-2.0
triage: anchor
---

# The compact proof of the Dirichlet GRH

The compact edition credits Levent Alpöge with the proof, developed with Claude, and credits Claude with the Lean text and documentation. The five concluding statements use Mathlib's Riemann zeta function and Dirichlet L-function. [Source and authorship](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md)

The half-plane theorem applies to every character of every positive modulus. It excludes the pair consisting of the principal character and the point 1. The separate strip theorem locates all zeros with real part strictly between 0 and 1, including those of imprimitive characters. For zeta, the statement explicitly excludes 1 and the negative even integers. [Definitions](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Statements.lean) · [Five concluding theorems](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Main.lean)

In the compact proof, upper and lower bounds for a common covolume yield the inequality `star_inequality`. For the admissible parameters and each real ε with 0 < ε < 1/100, `eventually_primeError_le_rpow` bounds the prime-sum remainder above by x raised to the power 8ε − 1/2 for all sufficiently large x. The one-sided nonvanishing criterion uses this estimate at an exponent chosen below the real part of a hypothetical zero. [Proof in New.Main](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Main.lean) · [Guide to the proof](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/GUIDE.md)

The source uses Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The five theorems use propositional extensionality, classical choice and quotient soundness. When this repository adopts a Mathlib revision supplying equivalent proofs, consumers can use those declarations directly and the superseded source closure can be retired. [Upstream axiom queries](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/scripts/PrintAxioms.lean)

Build the D5 entry point with `make lean LEAN_TARGETS=D5.S3.Zeros.GRH` from the repository root. A Lean consumer can then write `import D5.S3.Zeros.GRH` and use the five declarations under their upstream names. The compact edition's bibliography records sources for the individual arguments. [Upstream references](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/REFERENCES.md)

The compact edition carries copyright 2026 Anthropic, PBC, and records its adaptations of Mathlib declarations. [License](../../docs/reports/third-party/grh-lean/LICENSE.txt) · [Notice](../../docs/reports/third-party/grh-lean/NOTICE.txt) · [Attribution](../../docs/reports/third-party/grh-lean/ATTRIBUTION-NOTICE.txt)

## Verified locator

https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md
