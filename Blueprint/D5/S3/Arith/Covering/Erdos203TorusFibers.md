# Exact original-row restrictions

## Abstract

The torus is the square of the original common period. Its six-row subgroup is defined from the actual original equations.

**Definition 1.1 (The full-period exponent torus).**

Lean statement: `D5/S3/Arith/Covering/Erdos203TorusFibers.Torus`

*Formalization.* `D5/S3/Arith/Covering/Erdos203TorusFibers.Torus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Torus is ZMod period times ZMod period.

**Definition 1.2 (Simultaneous coordinate reduction).**

Lean statement: `D5/S3/Arith/Covering/Erdos203TorusFibers.periodMap`

*Formalization.* `D5/S3/Arith/Covering/Erdos203TorusFibers.periodMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The additive homomorphism reduces both integer coordinates modulo the common original period.

**Definition 1.3 (The unchanged original linear form).**

Lean statement: `D5/S3/Arith/Covering/Erdos203TorusFibers.originalMap`

*Formalization.* `D5/S3/Arith/Covering/Erdos203TorusFibers.originalMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For row i, originalMap reduces the torus coordinates modulo its original modulus and evaluates a_i x + b_i y. The original modulus divides period.

**Definition 1.4 (Common homogeneous kernel).**

Lean statement: `D5/S3/Arith/Covering/Erdos203TorusFibers.sixTorus`

*Formalization.* `D5/S3/Arith/Covering/Erdos203TorusFibers.sixTorus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The additive subgroup is the intersection of the kernels of the first six originalMap homomorphisms.

**Definition 1.5 (Integer linear form).**

Lean statement: `D5/S3/Arith/Covering/Erdos203TorusFibers.integerForm`

*Formalization.* `D5/S3/Arith/Covering/Erdos203TorusFibers.integerForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The additive homomorphism on integer pairs evaluates a x + b y.

**Theorem 1.6 (Original modular fiber counts).**

Lean statement: `D5/S3/Arith/Covering/Erdos203TorusFibers.original_six_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/Erdos203TorusFibers.original_six_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The restricted image has size e/g, with g the gcd of the original modulus and the two restricted coefficients. A translated original phase is compatible exactly when its residual value is divisible by g. Compatible fibers satisfy e times 8640 times their cardinality equals M squared times g; incompatible fibers are empty. No primitivity assumption is used.

## References

- Truth anchor: `D5/S3/Arith/Covering/Erdos203TorusFibers.Torus`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203TorusFibers.integerForm`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203TorusFibers.originalMap`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203TorusFibers.original_six_fibers`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203TorusFibers.periodMap`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203TorusFibers.sixTorus`
- Dependency: [D5/S3/Arith/Covering/Erdos203Lattice](Erdos203Lattice.md)
