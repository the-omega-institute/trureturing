# Order-Three Momentum Charge Action

## Abstract

Descent of the normalized moving-charge scalar and construction of the order-three charge operators on the integral momentum module.

Use the native symmetric even integral lattice, an additive equivalence g with g³ = 1, and preservation of the pairing ⟨·,·⟩. Write d = 1 − g and N = 1 + g + g². The input Multiplier consists of a normalized bimultiplicative complex-unit multiplier c, a unit ζ with ζ³ = 1, and the relation c(d a,b)/c(b,d a) = ζ to the power −⟨N a,b⟩. The input LiftPhase consists of η with η(a)η(b)c(a,b) = η(a+b)c(g a,g b) and η = 1 on fixed charges. The concrete multiplier and moving commutator come from ThirdTwistedChargeCocycle, based on Bakalov–Kac, arXiv:math/0402315v3, §4.3, equations (4.42) and (4.43).

**Theorem 1.1 (The difference lies in the norm kernel).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.norm_difference`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.norm_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For g³ = 1, the integral telescoping sum N(d a) = 0 uses only additivity of g. Thus every difference charge is a member of the moving lattice ker N.

**Definition 1.2 (Rational charge shift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.bShift`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.bShift` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Equation (4.27) of BK uses half the difference of the squared norms of the fixed projection and the original charge. The integral formula is bShift(a) = (⟨N a,N a⟩/9 − ⟨a,a⟩)/2.

**Theorem 1.3 (The shift has an integral numerator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.three_mul_bShift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.three_mul_bShift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For the period-three isometry, N is self-adjoint for the pairing and its image is fixed. Consequently 3 bShift(a) = q(a), where q(a) = ⟨a,g a⟩ − ⟨a,a⟩.

**Theorem 1.4 (Polarization of the integral numerator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.q_polarization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.q_polarization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding both pairings and using preservation of the form and g³ = 1 gives q(a+b) − q(a) − q(b) = ⟨N a,b⟩ − 3⟨a,b⟩.

**Definition 1.5 (Native standard phase).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.nativeStandardEta`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.nativeStandardEta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

If τ is IsometryLift.phase, define η(a) = τ(a)/τ(N a). The normalization implements the fixed-charge convention of BK (4.18)–(4.19) using the native lattice lift.

**Theorem 1.6 (Normalization on fixed charges).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.nativeStandardEta_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.nativeStandardEta_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For an isometry, the native sign phase is multiplicative on fixed charges and has square one. When g a = a, its norm phase is τ(3a) = τ(a), so the corrected phase is one.

**Definition 1.7 (Transfer to the twisted multiplier).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.nativeLiftPhase`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.nativeLiftPhase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Assume in addition c(a,b)ε(a,b) = c(g a,g b)ε(g a,g b) in the complex numbers, where ε is the native lattice sign. The native phase law gives the multiplier phase law by cancellation. The inverse norm phase is a character since N a and N b are fixed, so the correction preserves the law. This constructs the LiftPhase with the stated normalization.

**Definition 1.8 (Difference-charge scalar at zero momentum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.f`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.f` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The scalar f(a) = η(a)⁻¹ c(g a,d a) ζ to the power −q(a) is the form of BK (4.46) obtained from the charge d a of the ordered product U_(g a)⁻¹ U_a and the multiplier relation (4.42).

**Theorem 1.9 (Twisted multiplication before descent).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.f_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.f_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The lift-phase law and bimultiplicativity expand f(a)f(b)/(c(d a,d b)f(a+b)) into the moving commutator against g b and the phase of the polarization of q. The exponents cancel to −3⟨a,b⟩, whose phase is one by ζ³ = 1. Thus f(a)f(b) = c(d a,d b) f(a+b).

**Theorem 1.10 (Descent along the difference map).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.f_congr`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.f_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

If d a = d b then a − b is fixed. The normalized scalar of a fixed charge is one, and the twisted multiplication with this fixed difference reduces to f(a) = f(b).

**Theorem 1.11 (Descent of the nonzero-momentum scalar).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.fAt_congr`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.fAt_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The momentum scalar fAt(a,b) is f(a) times ζ to the power −⟨N a,b⟩. The moving commutator and self-adjointness of N prove that it depends only on d a and N b. With physical momentum N b / 3 this is the fixed-momentum phase in BK (4.46).

**Definition 1.12 (Integral moving-lattice exactness).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.MovingExact`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.MovingExact` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

MovingExact requires every integral charge in ker N to lie in range d. When g³ = 1, norm_difference gives the reverse inclusion, so this is ker N = range d. This hypothesis extends the descended scalar to every moving charge. The P48q application supplies it from the Nebe row-lattice moving certificate.

**Definition 1.13 (Scalar on the moving lattice).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.chi`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.chi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

With MovingExact, choose a preimage a of each m in ker N under d and set χ(m) = f(a). The theorem chi_difference follows from f_congr and identifies the value on every difference representative.

**Theorem 1.14 (Multiplication on the integral moving subgroup).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.chi_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.chi_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Choose integral difference representatives a and b for m and n in ker N. The difference of a+b represents m+n. Descending f_mul proves χ(m)χ(n) = c(m,n)χ(m+n).

**Definition 1.15 (Coefficient for a momentum translation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.coefficient`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Index the projected momenta by p ∈ range N, representing p/3. Choose a section s with N(s(p)) = p. The shift by a is p′ = p + N a, and the difference m = a + s(p) − s(p′) lies in ker N. Define the coefficient as c(a,s(p)) χ(m)/c(s(p′),m).

**Theorem 1.16 (Multiplication of the translation coefficients).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.coefficient_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.coefficient_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Successive shifts by b and a equal the shift by a+b. The section differences add, and the identity c(a,b)c(a+b,t) = c(b,t)c(a,b+t) follows from bimultiplicativity. Together with chi_mul this gives coefficient(b,p) coefficient(a,p+N b) = c(a,b) coefficient(a+b,p).

**Definition 1.17 (Actual charge operator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Ground is the complex Finsupp module on range N. Extend the action on each momentum basis vector linearly using Finsupp.lsum. The operator U(a) shifts p to p+N a and multiplies its coefficient by coefficient(a,p).

**Theorem 1.18 (Unit operator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The shift and section difference at a = 0 are p and zero respectively. The normalized multiplier and χ(0) = 1 give U(0) equal to the identity on Ground.

**Theorem 1.19 (Twisted group algebra multiplication).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U_comp`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The coefficient multiplication holds at every momentum, and finite-support linear-map extensionality gives U(a) composed with U(b) = c(a,b) U(a+b) on the whole Ground module. This realizes BK (4.42) for the charge operators with the stated algebraic inputs and integral exactness.

**Theorem 1.20 (Moving-charge relation at every momentum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U_difference_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U_difference_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The shift by d a fixes p and its section difference is d a. The commutator ratio c(d a,s(p))/c(s(p),d a) equals ζ to the power −⟨N a,s(p)⟩, and χ(d a) = f(a). Thus U(d a) on the momentum vector with complex coefficient z is multiplication by fAt(a,s(p)). This proves the moving scalar from BK (4.46) on actual momentum states.

The scope is the charge action conditional on the normalized multiplier, compatible lift phase and integral exactness. The concrete P48q inputs, oscillator field construction and full orbifold obstruction are subsequent mathematical steps.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.MovingExact`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U_comp`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U_difference_single`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.U_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.bShift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.chi`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.chi_mul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.coefficient_mul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.f`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.fAt_congr`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.f_congr`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.f_mul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.nativeLiftPhase`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.nativeStandardEta`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.nativeStandardEta_fixed`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.norm_difference`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.q_polarization`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.three_mul_bShift`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle](ThirdTwistedChargeCocycle.md)
