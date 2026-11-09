# Common positive roots in the first-Arens bidual

## Abstract

One positive element of the real first-Arens bidual has one common root realizing all its canonical GNS square roots.

**Theorem 1.1 (A single bidual root for every actual positive reading).**

$$\forall V \in \operatorname{Type}\left(\right)*,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), V\right)] \forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall i \in \operatorname{LinearIsometry}\left(\operatorname{Real}\left(\right), V, A\right),\; \forall hi \in \left(\forall x \in V,\; \operatorname{IsSelfAdjoint}\left(i\left(x\right)\right)\right),\; \forall S \in \operatorname{ContinuousBilinearMap}\left(\operatorname{Real}\left(\right), V, V, V\right),\; \left(\forall x \in V,\; \forall y \in V,\; i\left(S\left(x\right)\left(y\right)\right) = \operatorname{smul}\left(\operatorname{Divide}\left(1, 2\right), \operatorname{Add}\left(\operatorname{Multiply}\left(i\left(x\right), i\left(y\right)\right), \operatorname{Multiply}\left(i\left(y\right), i\left(x\right)\right)\right)\right)\right) \Rightarrow \left(\forall u \in V,\; i\left(u\right) = \operatorname{one}\left(A\right) \Rightarrow \left(\forall F \in \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), V\right)\right),\; \operatorname{Positive}\left(i, hi, F\right) \Rightarrow \left(\exists G \in \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), V\right)\right),\; \operatorname{arens}\left(S, G, G\right) = F \land \left(\operatorname{pow}\left(\operatorname{norm}\left(G\right), 2\right) = \operatorname{norm}\left(F\right) \land \left(\operatorname{Positive}\left(i, hi, G\right) \land \left(\operatorname{Member}\left(G, \operatorname{generated}\left(\operatorname{arensBilinear}\left(S\right), \operatorname{inclusionInDoubleDual}\left(\operatorname{Real}\left(\right), V\right)\left(u\right), F\right)\right) \land \left(\forall psi \in \operatorname{PositiveLinearMap}\left(\operatorname{Complex}\left(\right), A, \operatorname{Complex}\left(\right)\right),\; \operatorname{gnsLinear}\left(i, hi, psi\right)\left(G\right) = \operatorname{cfc}\left(Real.sqrt, \operatorname{gnsLinear}\left(i, hi, psi\right)\left(F\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ActualCommonBidualRoot.exists_common_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be any real normed space, possibly incomplete. Let A have the classes CStarAlgebra A, PartialOrder A and StarOrderedRing A. Let i be a real linear isometry from V into A with self-adjoint values. Let S be a bounded real bilinear product on V satisfying i(S(x,y))=(i(x)i(y)+i(y)i(x))/2, and let u be an original vector with i(u)=1. There is no assumption that i(V) is closed or equals the full self-adjoint part of A.

M means literally StrongDual real (StrongDual real V), with its canonical norm. Write j for the canonical inclusion of V into M. The product is the first-Arens extension arens(S,F,G)(phi)=F(G composed with rows(S,phi)); rows(S,phi)(x)(y)=phi(S(x,y)). In particular F remains the outer evaluation. arensBilinear bundles this same function as a real bilinear map.

For each unnormalized positive complex-linear functional psi on A, the space psi.GNS and its canonical representation pi_psi define coefficient(xi,eta)(x)=inner(xi,pi_psi(i(x))eta). The actual operator B_psi(F)=gnsLinear(i,hi,psi)(F) is determined by inner(xi,B_psi(F)eta)=F(realPart composed with coefficient(xi,eta))+I F(imaginaryPart composed with coefficient(xi,eta)). It is self-adjoint and has norm at most norm(F). The representation is real-linear in F; psi is an index and is not a linear variable.

Positive(i,hi,F) means that B_psi(F) is nonnegative for every actual positive psi. For each such F there is one G in this same M with arens(S,G,G)=F, norm(G) squared=norm(F), and Positive(i,hi,G). Moreover G belongs to generated(arensBilinear(S),j(u),F), the norm closure of the real span of the existing Jordan powers of F with zeroth power j(u). For every psi simultaneously, B_psi(G)=cfc(Real.sqrt,B_psi(F)). The functions cfc and Real.sqrt have their pinned Mathlib meanings.

The coefficient operators come from the bounded Hermitian form and the Hilbert-space duality theorem. CentralPositiveFunctionalExtension.exists_positive_extensions_norm_additive decomposes every real functional on the original isometric image as the difference of two ambient positive continuous functionals, with total unit mass equal to its norm. Their actual cyclic-vector coefficients imply joint detection of the canonical bidual norm and separation of its elements. No positive mass is divided out.

Original Jordan compatibility first gives the actual first-Arens product identity in every same-psi representation. Induction sends existing Jordan powers to associative operator powers. Each scalar polynomial q then gives one element q(F) in M whose psi reading is the operator polynomial q(B_psi(F)). The same family also gives the square-norm identity norm(arens(S,G,G))=norm(G) squared.

Put R=norm(F). All spectra of B_psi(F) lie in [0,R]. Mathlib's exists_polynomial_near_of_continuousOn supplies real polynomials q_n approximating the scalar square root on that interval with error at most (1/2)^n. This sequence is chosen before psi. The CFC polynomial and norm identities bound norm(B_psi(q_n(F))-cfc(Real.sqrt,B_psi(F))) by the same error for every psi. Joint norm detection makes q_n(F) Cauchy in the actual M, and completeness of this bidual supplies one limit G. Continuity of each actual reading identifies its value with the designated operator root.

The common readings and their product identity identify arens(S,G,G) with F. The square-norm identity gives the stated norm of G, operator CFC gives positivity, and closedness of the generated subspace preserves membership at the limit. If F=0 the witness is G=0. Zero functionals, zero GNS spaces and the zero ambient algebra remain in scope. Completeness of V, separability, norm attainment, normality of the original functionals, and closure of an operator image under square roots are not premises.

The construction composes classical Hilbert duality, positive Hahn-Banach extension, scalar polynomial approximation and operator continuous functional calculus. No literary novelty is claimed for those tools. The root lies in the mathematical bidual; it does not supply an original input in V or a physical preparation. The full original signed overlap budget and the identification of the original coset slope with the kernel response require their own original-response arguments.

**Theorem 1.2 (Actual nonnegative quadratic readings are exactly bidual squares).**

$$\forall V \in \operatorname{Type}\left(\right)*,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), V\right)] \forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall i \in \operatorname{LinearIsometry}\left(\operatorname{Real}\left(\right), V, A\right),\; \forall hi \in \left(\forall x \in V,\; \operatorname{IsSelfAdjoint}\left(i\left(x\right)\right)\right),\; \forall S \in \operatorname{ContinuousBilinearMap}\left(\operatorname{Real}\left(\right), V, V, V\right),\; \left(\forall x \in V,\; \forall y \in V,\; i\left(S\left(x\right)\left(y\right)\right) = \operatorname{smul}\left(\operatorname{Divide}\left(1, 2\right), \operatorname{Add}\left(\operatorname{Multiply}\left(i\left(x\right), i\left(y\right)\right), \operatorname{Multiply}\left(i\left(y\right), i\left(x\right)\right)\right)\right)\right) \Rightarrow \left(\forall u \in V,\; i\left(u\right) = \operatorname{one}\left(A\right) \Rightarrow \left(\forall F \in \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), V\right)\right),\; \left(\forall psi \in \operatorname{PositiveLinearMap}\left(\operatorname{Complex}\left(\right), A, \operatorname{Complex}\left(\right)\right),\; \forall v \in \operatorname{GNS}\left(psi\right),\; \operatorname{Le}\left(0, \operatorname{re}\left(\operatorname{inner}\left(\operatorname{Complex}\left(\right), v, \operatorname{gnsLinear}\left(i, hi, psi\right)\left(F\right)\left(v\right)\right)\right)\right)\right) \Leftrightarrow \left(\exists G \in \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), V\right)\right),\; \operatorname{arens}\left(S, G, G\right) = F\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ActualCommonBidualRoot.quadratic_iff_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the same V,A,i,hi,S,hS,u,hu hypotheses, an arbitrary F in M has nonnegative real quadratic reading inner(v,B_psi(F)v) for every positive psi and every v in psi.GNS if and only if F=arens(S,G,G) for some G in M. The inner product is linear in its second argument.

Self-adjointness identifies these quadratic inequalities with Positive(i,hi,F). The forward implication consumes the single common-root construction. For the reverse implication the actual product formula sends arens(S,G,G) to B_psi(G) squared, which is nonnegative because B_psi(G) is self-adjoint. All degeneracies and unnormalized readings have the same scope as in the root theorem.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ActualCommonBidualRoot.exists_common_root`
- Truth anchor: `D5/S3/Quantum/Algebra/ActualCommonBidualRoot.quadratic_iff_square`
- Dependency: [D5/S3/Quantum/Algebra/CentralPositiveFunctionalExtension](CentralPositiveFunctionalExtension.md)
- Dependency: [D5/S3/QuantumStates/GNSCompatibleStateExtension](../../QuantumStates/GNSCompatibleStateExtension.md)
- Dependency: [D5/S3/Topology/JBAlgebra](../../Topology/JBAlgebra.md)
