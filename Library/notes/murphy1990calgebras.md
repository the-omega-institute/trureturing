---
bibkey: murphy1990calgebras
authors: Gerard J. Murphy
year: 1990
title: C*-Algebras and Operator Theory
doi: 10.1016/C2009-0-22289-6
claim: Full complex matrix algebras are simple noncommutative C*-algebras and have no characters above dimension one.
strata_touched:
  - D5/S3/Quantum/FiniteDimensional
license: citation-only
triage: anchor
---

# C*-Algebras and Operator Theory

Gerard J. Murphy's text develops full matrix algebras as the basic
finite-dimensional noncommutative C*-algebras, together with the standard
ideal and character theory that rules out a unital complex-algebra character
on `M_n(C)` for `n > 1`. The repository proves the `n = 2` instance directly
from the anticommuting Pauli generators.

The formal declaration does not prove the arbitrary-`n` theorem. It is also
strictly stronger in its algebraic preservation laws than a valuation on
projections, so it is not presented as a Kochen-Specker result.

## Search log

- 2026-07-17: Queried NyxID/Tavily for `"C*-Algebras and Operator Theory"
  Murphy DOI`. Publisher and bibliographic records verified Gerard J. Murphy,
  the 1990 title, and DOI `10.1016/C2009-0-22289-6`.
- 2026-07-17: Queried `Murphy full matrix algebra simple characters M_n C
  C*-algebra`. Results located the book's standard finite-dimensional matrix
  algebra and character context. The repository proof was independently
  checked from Pauli anticommutation rather than inferred from snippets.
- 2026-07-17: Queried `M2 C unital algebra homomorphism to C no character`.
  Results agreed with the elementary simplicity/commutator obstruction; the
  exact Lean statement remains deliberately limited to `M_2(C)`.

## Verified locator

- DOI: https://doi.org/10.1016/C2009-0-22289-6
