# Natural integer bulk maximum

## Abstract

Natural integer bulk maximum.

The real matrix A has rows (-1,-2,-3,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3), (-1,-2,-3,-4,-5,-6,-5,-4,-3,-2,-1,0,1,2,3,4), and (-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2). All sixteen slots are retained.

**Definition 1.1 (Three boundary rows).**

$$A:Matrix\left(Fin\left(3\right), Fin\left(16\right), \mathbb{R}\right)=((-1,-2,-3,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3),(-1,-2,-3,-4,-5,-6,-5,-4,-3,-2,-1,0,1,2,3,4),(-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A has three rows and sixteen ordered gap slots. Each row retains the complete original boundary inequality.

**Theorem 1.2 (Ordered boundary and middle positions).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes.positions_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes.positions_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N at least 67 and middle position j from 6 through N-10, the sixteen natural step positions 1,2,3,4,5,j,N-9 through N are strictly increasing. These positions and A are shared by the arbitrary-defect cone estimate and the spectrum compression proof. The latter remains with the scalar endpoint and handles positive middle mass by barycentric weights and zero middle mass without division.

**Theorem 1.3 (Natural integer bulk maximum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes.bulk_integer_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes.bulk_integer_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N at least 67 and natural j, the bulk ratio (9N+16j)/(3N+2j)^2 is at most its value at natural t=(3N+4)/8. The boundary and middle rational envelopes are bounded by a common envelope, which is below the integer bulk value after the exact rounding inequalities. Natural division takes place before coercion to the reals.

These statements concern real scalar spectra and exact rational comparisons. Connecting the boundary inequalities to a physical APPT model, constructing an attaining state, and determining a purity supremum require additional results.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes.A`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes.bulk_integer_maximum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes.positions_strict`
