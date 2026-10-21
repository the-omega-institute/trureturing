# Charged collision kernel

## Abstract

Charged collision kernel.

**Definition 1.1 (The normalized square-root unit).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionUnit`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

collisionUnit is the unit of PowerSeries Complex whose value is one half times (binomialSeries(1/2)+1). Its constant coefficient is one.

**Definition 1.2 (Every scalar Taylor coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionScalar`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionScalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a,B:Int and N:Nat, collisionScalar a B N is coefficient N of binomialSeries(a/2) multiplied by collisionUnit^(-2*B). The signed integer power is taken in the power-series unit group.

**Definition 1.3 (The finite oscillator coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionOscillator`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionOscillator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For D:LatticeData, sigma,tau:Charge D, N:Nat and e:Int, collisionOscillator D sigma tau N e is a Complex-linear endomorphism of Oscillator D. It first applies the actual pairTranslation and then evaluates each translated monomial by the finite creator sum described above. Polynomial coefficients and repeated-variable multiplicities are retained.

**Definition 1.4 (The complete actual tensor coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For D:LatticeData, hu:IsUnit D.G.det, sigma,tau:Charge D, N:Nat and e:Int, collisionCoefficient D hu sigma tau N e is chargeScalar D (sigma+tau) times TensorProduct.map of collisionOscillator D sigma tau N e and the chosen groundAction D hu (sigma+tau). Thus it acts on arbitrary oscillator and ground inputs and extends linearly to every ActualTensor D hu.

**Definition 1.5 (The pointwise lower-truncated collision field).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionField`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionField` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For D:LatticeData, hu:IsUnit D.G.det, sigma,tau:Charge D and N:Nat, collisionField D hu sigma tau N is the NativeField with signed coefficient collisionCoefficient D hu sigma tau N. Its lower bound depends on the actual input. For p tensor g one bound is -Q(sigma+tau)-2*N minus the largest d(0)+d(1) in the support of pairTranslation(p); tensor induction extends this bound to arbitrary inputs. Endomorphism support is not assumed finite.

**Theorem 1.6 (The ordinary charged ground-source mode).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.bare_source_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.bare_source_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordinary Carrier source product retains epsilon(sigma,tau), the signed creation degree -r-1-bilinear(sigma,tau), and both charges. It is consumed by the source-iterate comparison.

**Definition 1.7 (The finite charge insertion field).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.chargeInsertion`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.chargeInsertion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The charge-weighted singleton insertion and the finite neutral-mode correction use the actual source frequency bound. No bound on Taylor order is assumed.

**Theorem 1.8 (The corrected creation step).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.corrected_creation_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.corrected_creation_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Physical translation and the ordinary creation recurrence give the signed coefficient step on every ActualTensor input, with the actual charge insertion term.

**Definition 1.9 (One signed creator summand).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.diagonalTerm`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.diagonalTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar Taylor coefficient multiplies the two signed half-creation coefficients. Negative creator degrees are retained and vanish through the existing constructors.

**Theorem 1.10 (The finite creator diagonal).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.diagonal_as_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.diagonal_as_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer finsum is zero at negative total degree and otherwise equals the finite natural interval sum. This supplies the support bound used by the current and finite-balance calculations.

**Definition 1.11 (The translated creator diagonal).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionDiagonal`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two translation degrees determine the signed total. Its nonnegative branch sums every allowed creator split and its negative branch is zero.

**Definition 1.12 (The linear finite-polynomial readout).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionConvolution`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionConvolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient-linear equivalence and Finsupp.lsum evaluate each pair polynomial with its own finite support. The current calculation applies it to transformed polynomials.

**Theorem 1.13 (The actual translated-input expansion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collision_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collision_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The oscillator endomorphism expands over the actual pairTranslation support, with a finite signed creator diagonal for each translated monomial.

**Definition 1.14 (The input translation bound).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.translatedDegree`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.translatedDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supremum of the two translation degrees is taken over the finite support of the actual translated input. This bounds the negative current branch without any global End-valued support assertion.

**Definition 1.15 (The charge-weighted normal current).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.normalCurrent`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.normalCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The current is the charge-weighted sum of singletonLinear insertions. It acts on whole fields, including coefficients evaluated on current-transformed inputs.

**Definition 1.16 (The inverse square-root coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionR`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient halfBinomial(j)/(j+1) is shared by the scalar Taylor recurrence, source insertion identity, and all-order comparison.

**Theorem 1.17 (The scalar Taylor recurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionScalar_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionScalar_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the binomial series and normalized square-root unit gives the recurrence for all signed scalar parameters and every natural order. It is the scalar input to the finite oscillator balance.

**Theorem 1.18 (Ordinary current action on the creation source).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.source_neutral_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.source_neutral_creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero neutral mode pairs with sigma+tau. Positive modes pair with sigma and shift the ordinary creation degree, retaining negative shifted degrees through the signed constructor.

**Theorem 1.19 (The whole-field insertion identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.chargeInsertion_field_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.chargeInsertion_field_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual insertion constructor equals the normal current minus the norm and finite bilinear corrections. Source support is padded using both the original frequency bound and the Taylor degree, without assuming either bounds the other.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.bare_source_product`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.chargeInsertion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.chargeInsertion_field_identity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionConvolution`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionDiagonal`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionField`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionOscillator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionR`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionScalar`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionScalar_recurrence`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionUnit`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collision_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.corrected_creation_step`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.diagonalTerm`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.diagonal_as_sum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.normalCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.source_neutral_creation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.translatedDegree`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualAnnihilation](../LatticeActualAnnihilation.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualOrderedProducts](../LatticeActualOrderedProducts.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts](../LatticeHalfFockGroundProducts.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts](../LatticeHalfFockOrderedProducts.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](../LatticeHalfFockOriginalTranslation.md)
