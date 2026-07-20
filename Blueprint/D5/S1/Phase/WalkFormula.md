# Walk Formula Algebra

This module records four algebraic laws with all structural premises explicit. It does not prove the BHK theorem, its finite certificates, or the canonical endpoint divisibility premise, and it does not identify any word, column, or Dedekind walk with the displayed expressions. The endpoint integrality theorem is only a conditional corollary and does not discharge the endpoint-translation-integrality residual.

## Theorem: Concatenation carries the parity sign

Provenance: `repo-derived`

Statement: `D5/S1/Phase/WalkFormula.alternating_walk_append` `✓ std3`

Concatenating two integer coefficient lists adds the second alternating walk with sign determined by the length of the first list. No continued-fraction normalization or orbit interpretation is inferred.

## Theorem: Reversal carries the length-parity sign

Provenance: `repo-derived`

Statement: `D5/S1/Phase/WalkFormula.alternating_walk_reverse` `✓ std3`

Literal list reversal multiplies the alternating walk by minus one to the length-plus-one power. The theorem does not identify reversal with a fixed-point branch or an inverse orbit.

## Theorem: An explicit endpoint multiple gives an integral correction

Provenance: `repo-derived`

Statement: `D5/S1/Phase/WalkFormula.endpoint_correction_is_integer` `✓ std3`

When an integer endpoint difference is explicitly equal to a nonzero denominator times an integer translation, its rational quotient is that integer. This is only a conditional corollary and does not discharge the endpoint-translation-integrality residual; the canonical endpoint divisibility witness remains a separate semantic obligation.

## Theorem: Endpoint translation is exactly covariant

Provenance: `repo-derived`

Statement: `D5/S1/Phase/WalkFormula.w3_walk_endpoint_translation` `✓ std3`

Adding an integral denominator multiple to the first endpoint adds exactly that integer to the rational W3 expression. This algebraic covariance does not assert a BHK or three-walk semantic identification.
