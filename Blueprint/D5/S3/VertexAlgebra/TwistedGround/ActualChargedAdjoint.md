# Actual Tensor Charged Bilinear Adjoint

## Abstract

Actual Tensor Charged Bilinear Adjoint

The ground module is exactly the already selected ActualGround D hu, defined using the existing Classical.choose actual twisted ground representation. A GroundPairing is chosen from actual_ground_pairing, and actualForm is the tensor product of its complex bilinear form with SignedOscillatorWick.wick. The ground pairing may be nonsymmetric. This module proves and uses no symmetry assertion.

On pure tensors the existing charge scalar 2^(-N) is retained. The actual same-charge ground signed adjoint contributes paritySign(N/2), and the oscillator rectangle contributes exponent -e-2N. Tensor induction gives the full statement B(C(a,e)x,y)=paritySign(N/2)B(x,C(a,-e-2N)y) for arbitrary actual tensor inputs. No positivity, rank restriction, Jacobi, covariance or desired adjoint premise is supplied.

Tensor nondegeneracy uses a finite basis of the actual ground coordinate space, its dual basis for G, and a different dual basis for G.flip. These isolate the two tensor slots separately. No symmetry-dependent right-dual identity and no infinite-dimensional full-dual isomorphism is used.

The full algebraic dual coefficient on charged generators is a genuine consumer: for each charge and each nonzero actual ground u, tensor nondegeneracy detects the existing charged_ground_leading at exponent -N. The proved actual adjoint moves that nonzero test into the first coefficient slot, retaining its parity sign. The original corrected-source consumer uses this result. Restricted-dual representability, full corrected adjointness, a two-twisted intertwining field, mixed Jacobi, fusion and the complete Monster/string/AdS objective remain open. Classical construction; no novelty claim.

Information-escape registration remains unfinished: the faithful compiled Reg mirrors currently report declared_unresolved. The source-reconstruction diagnostics and missing binding certificates are recorded at https://github.com/the-omega-institute/trureturing/issues/21134 under the repository linked-issue exception. Compilation does not assert a validated registration.

**Definition 1.1 (actualForm).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.actualForm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.actualForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tensor form on the original ActualTensor, using the exact chosen actual ground and the signed oscillator Wick form.

**Theorem 1.2 (actual charged coefficient adjoint).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.actual_charged_coefficient_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.actual_charged_coefficient_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unrestricted same-charge signed adjoint at the exact reflected integer exponent -e-2*bilinear D a a. Both tensor inputs are actual twisted tensors.

**Theorem 1.3 (actualForm nondegenerate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.actualForm_nondegenerate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.actualForm_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both-sided tensor nondegeneracy is proved by finite coordinate isolation using G.dualBasis and G.flip.dualBasis separately.

**Definition 1.4 (chargedDualCoefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.chargedDualCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.chargedDualCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Left-oriented full algebraic functional on finitely supported charged generators: the coefficient acts on the first twisted input.

**Theorem 1.5 (chargedDualCoefficient nonzero second ground).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.chargedDualCoefficient_nonzero_second_ground`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.chargedDualCoefficient_nonzero_second_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every charge and nonzero actual ground second input, some actual first input gives a nonzero generator coordinate at exponent minus the original signed norm. It consumes the constructed adjoint, nondegeneracy and existing actual leading coefficient.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.actualForm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.actualForm_nondegenerate`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.actual_charged_coefficient_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.chargedDualCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.chargedDualCoefficient_nonzero_second_ground`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/InvariantPairing](InvariantPairing.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick](SignedOscillatorWick.md)
