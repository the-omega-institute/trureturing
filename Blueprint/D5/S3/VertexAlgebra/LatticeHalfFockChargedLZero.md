# Original Charged Half-Fock L0

## Abstract

Exact original charged all-state energy covariance

Let D:LatticeData be an integral symmetric even-diagonal Gram datum of arbitrary finite rank, hu:IsUnit D.G.det, a:Charge D and e:Int. No positive definiteness, metric, adjoint, positive rank or input homogeneity is assumed. Rank zero and indefinite unimodular Gram data remain in scope. The actual tensor space is Oscillator D tensor_C ActualGround D hu, using the previously constructed ground representation.

Set q=B(a,a), s=2^(-q), and H=HalfFockSpectralFiberSource.actualInverse D=(D.G inverse).map(Int.castRingHom C). Both H*gramComplex(D)=1 and gramComplex(D)*H=1 follow from hu by the integral nonsingular-inverse laws and mapping multiplication to C. The definition and these two private laws live in this substantive owner and are consumed by its tensor proof; they are support, not an inverse-only result.

Use exactly the original halfTranslationVariable, halfTranslatedPolynomial, oscillatorTerm, oscillatorCoefficient, chargedCoefficient, tensorL and groundAction. The native oscillator variable (i,k) has odd weight omega(i,k)=2k+1 and half-frequency k+1/2. The native L0 ground shift is rank(D)/16. Physical z=t^2 and the cover prefactor is t^(-q). The complete coefficient on p tensor g is s times sum_r coeff_r(Q_a(p))*C_a[e+q+r] tensor groundAction(a)g. Neither s nor any sign or phase is absorbed into groundAction.

WeightedPolynomialSubstitution proves that Q_a(p) has mixed weight N whenever p has natural odd weight N. Thus its r-th coefficient has signed odd weight N-r. The existing half_creation_coefficient_grading gives C_a[j] weight j for j>=0, while the original definition makes j<0 literally zero. Every original summand has signed weight (N-r)+(e+q+r)=N+e+q. The existing term_support confines the original finsum to Polynomial.support(Q_a(p)); finite homogeneous summation proves the same output weight for oscillatorCoefficient. This does not impose finite Laurent support or any occupation cutoff.

The existing LatticeHalfFock.L_zero_monomial_coeff gives rank/16 plus the sum of occupations times k+1/2. A finite support calculation identifies that sum with half the signed odd weight. Expanding a homogeneous polynomial over its actual monomials gives its L0 eigenvalue; subtracting input and output energies cancels rank/16 and N/2 and leaves (e+q)/2. A second finite monomial expansion removes input homogeneity for every oscillator polynomial. TensorProduct.ext then proves the stated endomorphism equality directly, with both inverse laws from hu. Tensor linearity and scalar commutation retain the original s and the opaque ground action.

For every v:ActualTensor D hu, evaluation of this map equality is exactly tensorL(D,ActualGround(D,hu),H,0)(chargedCoefficient(D,hu,a,e)v) - chargedCoefficient(D,hu,a,e)(tensorL(D,ActualGround(D,hu),H,0)v) = (((e+B(a,a):Int):Complex)/2) smul chargedCoefficient(D,hu,a,e)v. There is no added inverse, positivity, metric or homogeneity premise. This all-state consequence is exposition and a transient exact compiled application, not a second named canonical evaluation wrapper.

Signed boundaries are literal: r>N makes the translated coefficient zero, e+q+r<0 makes the creation factor zero, and negative signed output weight admits no nonzero monomial. Both upward and downward half-energy displacement are included. The same proof covers rank zero and indefinite Gram forms; it does not infer a positive-energy grading from unimodularity.

Attribution: the algebraic twisted lattice Fock construction and normalization follow Frenkel, Lepowsky and Meurman, Vertex Operator Algebras and the Monster (1988), using this repository's original half-Fock and charged-coefficient suppliers and Mathlib polynomial, matrix and tensor-product APIs. The added implementation joins mixed weighted substitution to the original finite charged coefficient and all-state L0 operator. Definitions, casts, inverse laws and directly instantiated spectrum facts are consumed support. No literature novelty is asserted.

This is one exact algebraic energy-covariance milestone in the unchanged Monster moonshine to VOA/CFT, anomaly/fusion, string theory and AdS/CFT programme. It does not establish full Virasoro covariance, charged pair locality, twisted Jacobi, a full conformal twisted module, a completed VOA, analytic CFT, fusion or anomaly structures, geometric reconstruction, string dynamics or AdS/CFT. Those further endpoints remain open.

**Theorem 1.1 (The original left inverse Gram identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.actualInverse_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.actualInverse_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The original actualInverse times gramComplex is the identity for every original determinant-unit lattice. This visibility-only change preserves the exact statement and proof body. ActualMobiusCovariance consumes it in both charge contractions and the actual tensor-current L1 law.

**Theorem 1.2 (The original right inverse Gram identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.actualInverse_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.actualInverse_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The original gramComplex times actualInverse is the identity. This visibility-only exposure preserves the statement and proof body and is consumed by the original charged L1 contraction and tensor-current commutator, with rank zero and indefinite forms retained.

**Theorem 1.3 (The original tensor current L0 law).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.tensor_current_L_zero_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.tensor_current_L_zero_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original tensor current, the commutator with the exact actual inverse zero mode is minus frequency k times that current. The in-place private inverse laws and existing oscillator commutator prove it; ActualEnergyCovariance consumes it in the normal-word induction.

**Theorem 1.4 (The original all-state charged L0 commutator).**

$$\operatorname{L0}\left(D, hu\right)\operatorname{A}\left(a, e\right)-\operatorname{A}\left(a, e\right)\operatorname{L0}\left(D, hu\right)=\frac{e+\operatorname{B}\left(a, a\right)}{2}\operatorname{A}\left(a, e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.charged_tensor_L_zero_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all D:LatticeData, hu:IsUnit D.G.det, a:Charge D and e:Int, the displayed equality is in Module.End C (ActualTensor D hu). L0 is exactly tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 0 and A[a,e] is exactly chargedCoefficient D hu a e. Multiplication is composition. The proof is the finite signed-grading and tensor-extension chain described above, not an inverse-instantiation alias.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.actualInverse_left`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.actualInverse_right`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.charged_tensor_L_zero_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero.tensor_current_L_zero_commutator`
- Dependency: [D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution](../Quantum/Algebra/WeightedPolynomialSubstitution.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
