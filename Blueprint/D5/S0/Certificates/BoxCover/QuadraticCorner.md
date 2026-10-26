# QuadraticCorner

## Abstract

Rational enclosures of recursive quadratic polynomials.

**Definition 1.1 (Recursive quadratic syntax).**

Lean statement: `D5/S0/Certificates/BoxCover/QuadraticCorner.Poly`

*Formalization.* `D5/S0/Certificates/BoxCover/QuadraticCorner.Poly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate is eliminated at both closed endpoints. The lower correction is max(d,0) times the squared interval width divided by four; the upper correction uses max(-d,0). Induction encloses every real point of the box, including zero-width intervals.

**Definition 1.2 (Exact lower enclosure).**

Lean statement: `D5/S0/Certificates/BoxCover/QuadraticCorner.lower`

*Formalization.* `D5/S0/Certificates/BoxCover/QuadraticCorner.lower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate is eliminated at both closed endpoints. The lower correction is max(d,0) times the squared interval width divided by four; the upper correction uses max(-d,0). Induction encloses every real point of the box, including zero-width intervals.

**Definition 1.3 (Exact upper enclosure).**

Lean statement: `D5/S0/Certificates/BoxCover/QuadraticCorner.upper`

*Formalization.* `D5/S0/Certificates/BoxCover/QuadraticCorner.upper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate is eliminated at both closed endpoints. The lower correction is max(d,0) times the squared interval width divided by four; the upper correction uses max(-d,0). Induction encloses every real point of the box, including zero-width intervals.

**Theorem 1.4 (Real point enclosure with diagonal correction).**

Lean statement: `D5/S0/Certificates/BoxCover/QuadraticCorner.encloses`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BoxCover/QuadraticCorner.encloses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coordinate is eliminated at both closed endpoints. The lower correction is max(d,0) times the squared interval width divided by four; the upper correction uses max(-d,0). Induction encloses every real point of the box, including zero-width intervals.

## References

- Truth anchor: `D5/S0/Certificates/BoxCover/QuadraticCorner.Poly`
- Truth anchor: `D5/S0/Certificates/BoxCover/QuadraticCorner.encloses`
- Truth anchor: `D5/S0/Certificates/BoxCover/QuadraticCorner.lower`
- Truth anchor: `D5/S0/Certificates/BoxCover/QuadraticCorner.upper`
