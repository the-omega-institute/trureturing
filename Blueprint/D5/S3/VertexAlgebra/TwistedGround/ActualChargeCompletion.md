# Fixed Inputs and Infinite Actual Charge Support

## Abstract

Fixed Inputs and Infinite Actual Charge Support

The original correctedField and correctedDualCoefficient are used throughout. Reduction of the actual sign quotient proves that the lift of a+a is the identity. The vacuum coefficient at norm zero therefore acts as the identity. Nondegeneracy of the SAME selected ground pairing used by actualForm supplies one pair u,v before the charge quantifier; no pigeonhole argument or quantifier exchange occurs.

The consumed support arguments apply abstractly to a full functional on the charge direct sum: a finitely supported family of oscillator duals has finite charge support, and a representative under a separately supplied charge-orthogonal form is supported in the finite image of its source support. The actual fixed-input coefficient violates both support consequences.

The proof reuses creation_zero for vacuum normalization, wick_constant_left for the oscillator pairing, and corrected_singleton_coeff_charged to identify the actual corrected-field coefficient. These are existing results; their public visibility adds no mathematical claim. The singleton macro name adjustment in CorrectedDualCoefficient is inherited compatibility.

Infinite charge support does not exclude the standard energy restricted dual when energy grades are infinite dimensional. This result proves neither all restricted-dual failure nor full corrected inversion, source covariance, Jacobi, fusion, Monster moonshine, string theory or AdS/CFT. It assumes neither ground symmetry nor source L1.

**Definition 1.1 (ChargeFinite).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.ChargeFinite`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.ChargeFinite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite set of integral charges outside which every oscillator evaluation of a full algebraic functional vanishes.

**Definition 1.2 (ChargeOrthogonal).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.ChargeOrthogonal`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.ChargeOrthogonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A separately supplied bilinear source form P has P(single q p,single r s)=0 when r differs from sigma(q). The representative orientation is P(a,-); the theorem assumes neither existence nor nondegeneracy of P.

**Definition 1.3 (completedCorrectedCoefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.completedCorrectedCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.completedCorrectedCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original corrected coefficient transported through the existing Mathlib Finsupp.lsum equivalence into the product of full oscillator duals. The equivalence and its reconstruction are reused, with no novelty claim.

**Theorem 1.4 (actual_even_isotropic_completion_boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.actual_even_isotropic_completion_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.actual_even_isotropic_completion_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary original lattice data D and unimodularity witness hu, an injective family of doubled charges of norm zero admits ONE FIXED pair of vacuum tensors with nonzero form. At exponent zero every family charge has the same nonzero coefficient. The coefficient is not charge finite, has no finite family of oscillator duals, and has no ordinary-source representative under any separately supplied charge-orthogonal form in orientation P(a,-). Its all-charge product coordinates have infinite support and reconstruct every finite source evaluation.

**Definition 1.5 (hyperbolic).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.hyperbolic`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.hyperbolic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit integral symmetric even unimodular hyperbolic plane with Gram matrix [[0,1],[1,0]]. The determinant is -1 and charges q(n)=(2n,0) are distinct with norm zero.

**Definition 1.6 (allCorrectedCoefficientsChargeFinite).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.allCorrectedCoefficientsChargeFinite`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.allCorrectedCoefficientsChargeFinite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The universal assertion that every original corrected dual coefficient is charge finite, with arbitrary lattice, unimodularity witness, exponent and actual tensor inputs.

**Theorem 1.7 (result).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.result`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hyperbolic plane refutes the universal finite-charge assertion using the generic completion boundary on c(n)=(n,0).

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.ChargeFinite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.ChargeOrthogonal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.actual_even_isotropic_completion_boundary`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.allCorrectedCoefficientsChargeFinite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.completedCorrectedCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.hyperbolic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargeCompletion.result`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/CorrectedDualCoefficient](CorrectedDualCoefficient.md)
