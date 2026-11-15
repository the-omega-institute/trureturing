---
bibkey: ratushnyak2026a400520
authors: Alex Ratushnyak; OEIS Foundation and contributors
year: 2026
title: "OEIS A400520: least square-and-triangular multipliers"
doi: null
url: https://oeis.org/A400520
claim: "Conjecture: a(n) > 0."
strata_touched:
  - D5/S3/Arith/Congruence/SquareTriangularMultipliers
license: CC-BY-SA-4.0
triage: anchor
---

# Square-and-triangular multipliers

A400520 asks for the least multiplier for which the product or its successor
is a square, and independently the product or its successor is triangular.
The offset is zero. The listed initial values at indices zero and one are
both one. Together with the source program, these specify the convention
that multipliers are positive; positivity is not an extra word in NAME.
Square roots and triangular indices are natural numbers, including zero.

The relevant quadratic form is the indefinite binary form
`X^2 - 8 Y^2`. Its Pell solutions with odd `X` give
`Y^2 = T(T+1)/2`, where `X=2T+1`. The transformation
`(X,Y) -> (3X+8Y,X+3Y)` preserves this form and has determinant one.
These classical ingredients do not constitute a novelty claim about Pell
equations or square triangular numbers.

## Verified locator

- URL: https://oeis.org/A400520
- Revision: #22, Nov 14 2026 14:42:25 EST.
- NAME: the least-multiplier definition, with failure value `-1`.
- COMMENT: "Conjecture: a(n) > 0."
- OFFSET: `0,3`; DATA: `a(0)=a(1)=1`.
- AUTHOR: Alex Ratushnyak, Nov 06 2026.
- Readable source: https://oeis.org/A400520/internal?fmt=text

The OEIS text is attributed to the OEIS Foundation and its contributors
under https://oeis.org/LICENSE (CC-BY-SA-4.0). No source program is copied.
The Lean argument directly invokes Mathlib's Apache-2.0 Pell and finite
dynamics results; those mathematical dependencies retain their own license.
