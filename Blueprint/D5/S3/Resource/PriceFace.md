# The Price Face of an Equality

## Abstract

The price of an equality is the minimal face of the tax receipts carried by all of its valid witnesses.

**Definition 1.1 (The price face is the minimal valid-witness receipt set).**

Lean statement: `D5/S3/Resource/PriceFace.priceFace`

*Formalization.* `D5/S3/Resource/PriceFace.priceFace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A cost profile is a function of the input scale, ordered by eventual domination: one profile is no greater than another when the inequality holds at every sufficiently large scale. A physical-cost record carries the time and space profiles of both directions of a witness.

A tax receipt records the two algorithm costs, a rate field, the four physical cost profiles, and a heat cost. Receipts use the componentwise order. The rate type is abstract, so a caller may use an option type when that field is derived only for a restricted class of witnesses.

For two objects, priceFace selects Mathlib Minimal elements among exactly the receipts produced by witnesses satisfying the supplied validity predicate. It defines a set rather than a scalar. No claim that the face has multiple independent cost directions is included.

## References

- Truth anchor: `D5/S3/Resource/PriceFace.priceFace`
