# Projection tests for the BKM transpose

## Abstract

Positivity of the BKM transpose forces commutation with projections in the reduced state's commutant inside the star-subalgebra.

**Definition 1.1 (The tracial expectation).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.traceExpectation`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.traceExpectation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict the codomain of the native ordered GNS projection at the normalized identity to the given unital star-subalgebra.

**Definition 1.2 (The actual BKM transpose).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.bkmTranspose`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.bkmTranspose` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Hideki Kosaki; Dénes Petz; Mary Beth Ruskai (2013). *Families of completely positive maps associated with monotone metrics*. URL: <https://arxiv.org/abs/1212.1337v3>.

*Commentary.*

Invert the restricted BKM integral at the reduced faithful base, then include the result in the ambient algebra and apply the ambient BKM integral. The order of composition follows the metric transpose in Appendix B of Hiai, Kosaki, Petz, and Ruskai.

**Theorem 1.3 (Positive transpose projection test).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.bkmTranspose_positive_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.bkmTranspose_positive_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a projection P that commutes with the reduced state, the reduced BKM integral gives the positive compression of that state by P. The transpose sends this test to the ambient BKM image of P. Projection rigidity then forces the ambient state to commute with P.

**Definition 1.4 (Defect of the BKM transpose).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.positivityDefect`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.positivityDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the supremum of negative spectral mass over the images of positive elements of the subalgebra with ambient trace one.

**Theorem 1.5 (Trace-norm error of pinching).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.bkm_pinching_traceNorm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.bkm_pinching_traceNorm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Test the transpose on the reduced state times each projection. The exact inverse identifies the output with the ambient BKM image, so its negative mass controls the squared Frobenius norm of the corresponding off-diagonal row. Row orthogonality allows their squared norms to be summed. The finite Schatten bound gives the trace-norm error with the coefficient stated in the theorem.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.bkmTranspose`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.bkmTranspose_positive_commute`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.bkm_pinching_traceNorm_le`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.positivityDefect`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSubalgebraDefect.traceExpectation`
- Dependency: [D5/S3/Quantum/Algebra/OrderedGNSProjection](../Algebra/OrderedGNSProjection.md)
- Dependency: [D5/S3/Quantum/Foundation/HilbertSchmidtTraceStability](../Foundation/HilbertSchmidtTraceStability.md)
- Dependency: [D5/S3/Quantum/Matrix/BKMProjectionRigidity](../Matrix/BKMProjectionRigidity.md)
