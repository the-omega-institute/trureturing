# Rectangular recovery from corner states

## Abstract

A square bound for every state of the actual left corner controls a rectangular product in an arbitrary unital complex C-star algebra.

**Theorem 1.1 (The actual corner).**

$$\forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall e \in A,\; \forall x \in A,\; \operatorname{IsStarProjection}\left(e\right) \Rightarrow \left(x \in \operatorname{cornerSpace}\left(e\right) \Leftrightarrow x = e \cdot x \cdot e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FullRectangularRecovery.corner_mem_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex submodule cornerSpace(e) consists of x with ex=x and xe=x. For a star projection e this is equivalent to x=exe. Its norm, topology and order are inherited from A.

**Theorem 1.2 (Self-adjoint values are real).**

$$\forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall phi \in \operatorname{PositiveContinuousLinearMap}\left(\operatorname{Complex}\left(\right), A, \operatorname{Complex}\left(\right)\right),\; \forall a \in A,\; \operatorname{IsSelfAdjoint}\left(a\right) \Rightarrow phi\left(a\right) = \operatorname{ofReal}\left(\operatorname{re}\left(phi\left(a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FullRectangularRecovery.positive_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive continuous complex functional takes a self-adjoint element to a real complex number. The notation re denotes real part and ofReal denotes the real inclusion in Complex.

**Theorem 1.3 (Order bounds for positive functionals).**

$$\forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall phi \in \operatorname{PositiveContinuousLinearMap}\left(\operatorname{Complex}\left(\right), A, \operatorname{Complex}\left(\right)\right),\; \forall a \in A,\; \operatorname{IsSelfAdjoint}\left(a\right) \Rightarrow \left(0 - \operatorname{norm}\left(a\right) \cdot \operatorname{re}\left(phi\left(1\right)\right) \le \operatorname{re}\left(phi\left(a\right)\right) \land \operatorname{re}\left(phi\left(a\right)\right) \le \operatorname{norm}\left(a\right) \cdot \operatorname{re}\left(phi\left(1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FullRectangularRecovery.positive_re_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying positivity to the two order-unit bounds for a self-adjoint element bounds its real functional value by its norm times the real unit mass. The functional need not be normalized.

**Theorem 1.4 (An internally obtained signed norm-attaining state).**

$$\forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall a \in A,\; \operatorname{IsSelfAdjoint}\left(a\right) \Rightarrow \left(a \ne 0 \Rightarrow \left(\exists phi \in \operatorname{PositiveContinuousLinearMap}\left(\operatorname{Complex}\left(\right), A, \operatorname{Complex}\left(\right)\right),\; \exists s \in \operatorname{Real}\left(\right),\; phi\left(1\right) = 1 \land \left(phi\left(a\right) = \operatorname{ofReal}\left(s\right) \land s^{2} = \operatorname{norm}\left(a\right)^{2}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FullRectangularRecovery.exists_norming_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each nonzero self-adjoint a, real Hahn-Banach on the inherited real self-adjoint subspace and the norm-additive positive extension theorem give positive functionals p and q. Their masses sum to one. Equality in the two norm bounds forces p(a)=norm(a)p(1) and q(a)=-norm(a)q(1). At least one mass is positive; normalizing that functional gives the displayed state and either spectral sign. No state or norm-attainment premise is supplied.

**Theorem 1.5 (Zero variance gives both multiplication identities).**

$$\forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall phi \in \operatorname{PositiveContinuousLinearMap}\left(\operatorname{Complex}\left(\right), A, \operatorname{Complex}\left(\right)\right),\; phi\left(1\right) = 1 \Rightarrow \left(\forall a \in A,\; \operatorname{IsSelfAdjoint}\left(a\right) \Rightarrow \left(\forall s \in \operatorname{Real}\left(\right),\; phi\left(a\right) = \operatorname{ofReal}\left(s\right) \Rightarrow \left(s^{2} = \operatorname{norm}\left(a\right)^{2} \Rightarrow \left(\forall x \in A,\; phi\left(a \cdot x\right) = \operatorname{ofReal}\left(s\right) \cdot phi\left(x\right) \land phi\left(x \cdot a\right) = \operatorname{ofReal}\left(s\right) \cdot phi\left(x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FullRectangularRecovery.norming_state_multiplication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same normalized functional phi, put r=a-s1. Contractivity of the original positive state bound and the C-star identity force phi(r*r)=0. The two positive-functional Cauchy-Schwarz inequalities then give phi(rx)=phi(xr)=0 for every actual middle element x. Both multiplication identities use this one phi.

**Theorem 1.6 (The exact sandwich identity).**

$$\forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall phi \in \operatorname{PositiveContinuousLinearMap}\left(\operatorname{Complex}\left(\right), A, \operatorname{Complex}\left(\right)\right),\; phi\left(1\right) = 1 \Rightarrow \left(\forall a \in A,\; \operatorname{IsSelfAdjoint}\left(a\right) \Rightarrow \left(\forall s \in \operatorname{Real}\left(\right),\; phi\left(a\right) = \operatorname{ofReal}\left(s\right) \Rightarrow \left(s^{2} = \operatorname{norm}\left(a\right)^{2} \Rightarrow \left(\forall C \in A,\; phi\left(a \cdot C \cdot a\right) = \operatorname{ofReal}\left(\operatorname{norm}\left(a\right)^{2}\right) \cdot phi\left(C\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FullRectangularRecovery.norming_state_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the two multiplication identities to a*C and C gives the sandwich formula for every C in the ambient algebra. The two occurrences of phi refer to the same state.

**Theorem 1.7 (The row Gram element is in the left corner).**

$$\forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall e \in A,\; \forall U \in A,\; \operatorname{IsStarProjection}\left(e\right) \Rightarrow \left(e \cdot U = U \Rightarrow U \cdot \operatorname{star}\left(U\right) \in \operatorname{cornerSpace}\left(e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FullRectangularRecovery.rowGram_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If eU=U, taking adjoints gives U-star e=U-star. Consequently U U-star belongs to eAe. This uses the row Gram element, whereas U-star U belongs to the right corner in the rectangular situation.

**Theorem 1.8 (Rectangular norm recovery).**

$$\forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall e \in A,\; \forall f \in A,\; \forall a \in A,\; \forall U \in A,\; \forall he \in \operatorname{IsStarProjection}\left(e\right),\; \forall hf \in \operatorname{IsStarProjection}\left(f\right),\; \operatorname{IsSelfAdjoint}\left(a\right) \Rightarrow \left(a = e \cdot a \cdot e \Rightarrow \left(U = e \cdot U \cdot f \Rightarrow \left(\forall kappa \in \operatorname{Real}\left(\right),\; 0 < kappa \Rightarrow \left(\left(\forall omega \in \operatorname{CornerState}\left(e, he\right),\; \operatorname{norm}\left(\operatorname{functional}\left(omega\right)\left(a\right)\right)^{2} \le kappa \cdot \operatorname{re}\left(\operatorname{functional}\left(omega\right)\left(U \cdot \operatorname{star}\left(U\right)\right)\right)\right) \Rightarrow \frac{\operatorname{norm}\left(a\right)^{2}}{\operatorname{sqrt}\left(kappa\right)} \le \operatorname{norm}\left(a \cdot U\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FullRectangularRecovery.full_rectangular_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A has exactly the classes CStarAlgebra A, PartialOrder A and StarOrderedRing A. Let e and f be actual star projections, a self-adjoint with a=eae, and U=eUf. A CornerState(e,he) is a positive continuous complex-linear functional on cornerSpace(e), normalized at the actual unit e. In the display omega(x) abbreviates omega.functional applied to x with its corner-membership proof. Both a and U U-star have that membership. All corner states are quantified, including states without any normality requirement. There is no dimension, nontriviality, invertibility, positivity of a, or supplied norming-state hypothesis.

The a=0 case gives the bound directly. Otherwise an ambient norm-attaining state phi and a nonzero real s are constructed internally. Since ea=a, the multiplication identity gives phi(e)=1. Restricting this same positive continuous phi to the actual corner yields a normalized CornerState, so the all-state premise gives norm(a)^2 <= kappa re(phi(U U-star)). The sandwich identity and the original normalized-state bound give norm(a)^2 re(phi(U U-star)) <= norm(aU)^2. Multiplication and the positive square root yield the displayed inequality.

The zero projections, zero algebra, zero channel, unequal corners and noninvertible channels are included. Positivity and continuity on the inherited corner are the usual mathematical state conditions; normalized positive functionals on a C-star corner are automatically continuous. The argument needs only the restriction of the constructed ambient state, so no ambient extension of an arbitrary corner state is assumed.

For the two-corner application one takes (a,U,kappa)=(sP,T,1) and (sQ,star(T),4). The second row Gram element is star(T)*T and the denominator is two. Deriving those two all-state premises from P2, the separate product estimates, and the resulting uniform stability theorem are additional mathematical steps. This result concerns the fixed C-star elements only and makes no assertion about a physical state source or the origin of quantum theory.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/FullRectangularRecovery.corner_mem_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/FullRectangularRecovery.exists_norming_state`
- Truth anchor: `D5/S3/Quantum/Algebra/FullRectangularRecovery.full_rectangular_recovery`
- Truth anchor: `D5/S3/Quantum/Algebra/FullRectangularRecovery.norming_state_multiplication`
- Truth anchor: `D5/S3/Quantum/Algebra/FullRectangularRecovery.norming_state_sandwich`
- Truth anchor: `D5/S3/Quantum/Algebra/FullRectangularRecovery.positive_re_bounds`
- Truth anchor: `D5/S3/Quantum/Algebra/FullRectangularRecovery.positive_real`
- Truth anchor: `D5/S3/Quantum/Algebra/FullRectangularRecovery.rowGram_mem`
- Dependency: [D5/S3/Quantum/Algebra/CentralPositiveFunctionalExtension](CentralPositiveFunctionalExtension.md)
- Dependency: [D5/S3/QuantumStates/GNSCompatibleStateExtension](../../QuantumStates/GNSCompatibleStateExtension.md)
