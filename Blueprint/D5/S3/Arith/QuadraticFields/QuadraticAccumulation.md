# Quadratic approximation and trace-dual norms

## Abstract

Every signed nonzero norm value of the trace dual is approached by distinct normalized quadratic approximations.

Dhanda and Haynes, Theorem 4, classify the complete accumulation set of normalized approximations to a real quadratic irrational. The result below proves the norm-value inclusion. The exclusion of all other accumulation points is not asserted here.

The radicand is an arbitrary squarefree integer at least two. The constant and square-root coefficients are rational, and the latter is nonzero. Denominators range over all nonzero integers and numerators over all integers; there is no coprimality hypothesis.

**Definition 1.1 (K).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.K`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.K` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The rational quadratic algebra has distinguished generator whose square is the radicand. Under the stated hypotheses it is a field.

**Definition 1.2 (alpha).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.alpha`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.alpha` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The irrational is represented by its constant and square-root coordinates.

**Definition 1.3 (lattice).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.lattice`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.lattice` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The integer lattice is the span of one and the quadratic irrational.

**Definition 1.4 (traceDual).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.traceDual`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.traceDual` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The dual is defined by integrality of the actual algebra trace pairing with every element of the lattice.

**Definition 1.5 (approximationValues).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.approximationValues`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.approximationValues` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The signed normalized error multiplies the error by the absolute value of its integer denominator. This is a set of real values.

**Definition 1.6 (realEmbedding).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realEmbedding`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realEmbedding` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The real algebra homomorphism sends the distinguished generator to the positive square root.

**Definition 1.7 (RealField).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.RealField`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.RealField` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The actual intermediate field of the real numbers is generated over the rationals by the irrational.

**Definition 1.8 (realAlpha).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realAlpha`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realAlpha` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The irrational is regarded as an element of its generated real subfield.

**Definition 1.9 (realLattice).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realLattice`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realLattice` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The integer span of one and the irrational lies inside the actual generated real field.

**Definition 1.10 (realTraceDual).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realTraceDual`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realTraceDual` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The original lattice is dualized using the actual trace form of the generated real field.

**Definition 1.11 (coordinateEquiv).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.coordinateEquiv`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.coordinateEquiv` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

The coordinate algebra is faithfully identified with the generated real subfield. The inverse recovers the square root by subtracting the rational constant and dividing by the nonzero square-root coefficient.

**Definition 1.12 (HasDistinctApproximationSequence).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.HasDistinctApproximationSequence`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.HasDistinctApproximationSequence` (`✓ std3`).

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

An injective sequence lies in the specified set, avoids its proposed limit, and converges to that limit. This condition implies genuine set accumulation.

**Theorem 1.13 (signed_norm_values_accumulate).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.signed_norm_values_accumulate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.signed_norm_values_accumulate` (`✓ std3`). ∎

*Citation.* Kavita Dhanda; Alan Haynes (2025). *Accumulation points of normalized approximations*. DOI: [10.1016/j.jnt.2024.09.002](https://doi.org/10.1016/j.jnt.2024.09.002). URL: <https://arxiv.org/html/2310.00173v2>.

*Commentary.*

For every nonzero element of the trace dual in the actual generated real subfield, multiply its field norm by twice the rational square-root coefficient and the positive square root of the radicand. Both signs of this value admit injective sequences of normalized approximation values avoiding the limit, and are genuine set accumulation points.

Trace integrality gives an integer denominator and numerator from every dual vector. Clearing the three rational multiplication coefficients and applying the positive Pell existence theorem produces a norm-one multiplier preserving the exact dual lattice. Its positive real embedding exceeds one and its conjugate is its reciprocal. Powers of the multiplier expand one embedding and contract the other.

After a finite shift the denominators are positive. The normalized values equal their limiting scaled norm plus a nonzero geometric correction. This correction proves injectivity and exclusion of the limit itself. Negating both integer coordinates produces the opposite signed limit. Algebra traces and norms are computed through the coordinate basis and transported by an algebra equivalence to the actual generated real subfield.

## References

- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.HasDistinctApproximationSequence`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.K`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.RealField`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.alpha`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.approximationValues`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.coordinateEquiv`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.lattice`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realAlpha`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realEmbedding`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realLattice`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.realTraceDual`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.signed_norm_values_accumulate`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticAccumulation.traceDual`
- Dependency: [D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal](QuadraticOrderMaximal.md)
