# Integer matrices, Hurwitz units and exact fraction programs

## Abstract

Exact integer matrices, modulo-five splitting and fraction programs for the OmegaMath architecture.

**Theorem 1.1 (Cyclicity of the trace).**

$$\forall A \in Mat2, B \in Mat2,\; \operatorname{tr}\left(A \cdot B\right) = \operatorname{tr}\left(B \cdot A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.trace_mul_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the two traces gives the same four integer products.

**Theorem 1.2 (The two adjugate identities).**

$$\forall A \in Mat2,\; A \cdot \operatorname{adj}\left(A\right) = \operatorname{scale}\left(\operatorname{det}\left(A\right), I\right) \land \operatorname{adj}\left(A\right) \cdot A = \operatorname{scale}\left(\operatorname{det}\left(A\right), I\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.adjugate_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal entries are the determinant. The off-diagonal entries vanish.

**Theorem 1.3 (The quadratic characteristic identity).**

$$\forall A \in Mat2,\; A \cdot A - \operatorname{scale}\left(\operatorname{tr}\left(A\right), A\right) + \operatorname{scale}\left(\operatorname{det}\left(A\right), I\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.cayley_hamilton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every matrix of size two with integer entries satisfies the monic quadratic determined by its trace and determinant.

**Theorem 1.4 (Norms of the twelve Hurwitz representatives).**

$$\forall u \in Core,\; \operatorname{normSq}\left(\operatorname{doubled}\left(u\right)\right) = 4$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.hurwitz_core_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four axial representatives have a single doubled coordinate equal to two. Each of the eight others has four doubled coordinates of magnitude one.

**Theorem 1.5 (Rank-one splitting of the norm-five generators).**

$$\forall g \in Generator,\; \operatorname{split5}\left(\operatorname{coordinates}\left(g\right)\right) = \operatorname{outer}\left(\operatorname{u}\left(\operatorname{factors}\left(g\right)\right), \operatorname{v}\left(\operatorname{factors}\left(g\right)\right), \operatorname{s}\left(\operatorname{factors}\left(g\right)\right), \operatorname{t}\left(\operatorname{factors}\left(g\right)\right)\right) \land \operatorname{isZero}\left(\operatorname{split5}\left(\operatorname{coordinates}\left(g\right)\right)\right) = false$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.mod_five_rank_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The split sends i to the diagonal matrix with entries two and minus two. Each listed factorization is an outer product over residues modulo five.

**Theorem 1.6 (Zero products among split generators).**

$$\forall g \in Generator, h \in Generator,\; \operatorname{isZero}\left(\operatorname{mul5}\left(\operatorname{split5}\left(\operatorname{coordinates}\left(g\right)\right), \operatorname{split5}\left(\operatorname{coordinates}\left(h\right)\right)\right)\right) = \operatorname{isOpposite}\left(g, h\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.mod_five_product_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Among the thirty-six ordered products, precisely the six ordered conjugate pairs vanish.

**Theorem 1.7 (The evaluator realizes the ordered transition relation).**

$$\forall P \in Program, n \in OmegaNat, m \in OmegaNat,\; \operatorname{step}\left(P, n\right) = \operatorname{some}\left(m\right) \Leftrightarrow \operatorname{Step}\left(P, n, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.fractran_step_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A guard holds when the stored denominator divides the state. This is Conway's integral-product test for a reduced fraction. The first enabled rule multiplies the exact quotient by its positive numerator.

**Theorem 1.8 (Determinism of the transition relation).**

$$\forall P \in Program, n \in OmegaNat, m \in OmegaNat, r \in OmegaNat,\; \left(\operatorname{Step}\left(P, n, m\right) \land \operatorname{Step}\left(P, n, r\right)\right) \Rightarrow m = r$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.fractran_deterministic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both transitions compute the same result of the ordered scan.

**Theorem 1.9 (Runs preserve positivity).**

$$\forall P \in Program, k \in OmegaNat, n \in OmegaNat,\; 0 < n \Rightarrow 0 < \operatorname{run}\left(P, k, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.fractran_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An enabled positive denominator at a positive state gives a positive quotient. Every numerator is positive by construction.

**Theorem 1.10 (Runs stabilize at a halting state).**

$$\forall P \in Program, k \in OmegaNat, n \in OmegaNat, t \in OmegaNat,\; \operatorname{Halts}\left(P, \operatorname{run}\left(P, k, n\right)\right) \Rightarrow \operatorname{run}\left(P, k + t, n\right) = \operatorname{run}\left(P, k, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.fractran_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every guard fails, another iteration returns the same state.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.adjugate_identities`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.cayley_hamilton`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.fractran_deterministic`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.fractran_positive`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.fractran_stable`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.fractran_step_iff`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.hurwitz_core_unit`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.mod_five_product_zero`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.mod_five_rank_one`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.trace_mul_comm`
