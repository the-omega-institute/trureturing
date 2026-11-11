# Bounded lifts in irreducible representations

## Abstract

Bounded lifts in irreducible representations

For a nontrivial C*-algebra A in Type u with PartialOrder A and StarOrderedRing A, and any irreducible star representation on a complete complex inner product space H in Type v, every self-adjoint operator T has a positive original-algebra bound L chosen before the vectors and accuracy. A common original self-adjoint e, of norm at most L, approximates T on any two specified vectors. The construction uses self-adjoint density and clips in A by continuous functional calculus, without injectivity, a norm bound on raw approximants, separability or a sequential restriction. The basic state and cyclic-vector definitions and the purity-to-irreducibility supplier results provide the representation interface. The original namespace and complete telescopes are retained. The bound is consumed by uniform_signed_original_square in UniformSignedSquare, whose common e controls the square at Omega and T(Omega). This C*-algebra result leaves general JB algebras and approximants in a possibly incomplete dense original E unresolved; it does not establish the further Jordan-algebra or PB Gram consequences.

**Theorem 1.1 (selfAdjoint_lift).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] \{H : Type v\} [NormedAddCommGroup.\{v\} H] [InnerProductSpace.\{0, v\} \mathbb{C} H] [CompleteSpace.\{v\} H] (\pi : StarAlgHom.\{0, u, v\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, v, v\} (RingHom.id.\{0\} \mathbb{C} ) H H)) \{b : ContinuousLinearMap.\{0, 0, v, v\} (RingHom.id.\{0\} \mathbb{C} ) H H\}, Membership.mem.\{v, v\} (StarAlgHom.range.\{0, u, v\} \pi ) b \to IsSelfAdjoint.\{v\} b \to \exists (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{v + 1\} (\pi \operatorname{coe} a) b$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.selfAdjoint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose any original preimage a of b from membership in pi.range, and replace it by its real symmetrization one half times (a+star a). map_add and map_star show that its image is one half times (b+star b), which equals b by self-adjointness. The construction needs no faithful or injective representation.

**Theorem 1.2 (bounded_strong_lift).**

$$\forall A \in \operatorname{Type} u,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall H \in \operatorname{Type} v,\; [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] [\operatorname{CompleteSpace}\left(H\right)] \forall pi \in \operatorname{StarAlgHom}\left(\mathbb{C}, A, \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)\right),\; (\operatorname{IsIrreducible}\left(pi\right)) \Rightarrow (\forall T \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; (\operatorname{IsSelfAdjoint}\left(T\right)) \Rightarrow (\exists L \in \mathbb{R},\; (0 < L) \land (\forall x \in H,\; \forall y \in H,\; \forall delta \in \mathbb{R},\; (0 < delta) \Rightarrow (\exists e \in \operatorname{selfAdjoint}\left(A\right),\; (\left\lVert e \right\rVert \le L) \land ((\left\lVert pi\left((e:A)\right)\left(x\right) - T\left(x\right) \right\rVert < delta) \land (\left\lVert pi\left((e:A)\right)\left(y\right) - T\left(y\right) \right\rVert < delta))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.bounded_strong_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set R=1+norm(T) before choosing vectors or accuracy and normalize B=T/R to a self-adjoint contraction. Its inverse Kaplansky value U satisfies f(U)=B by cfc_kaplanskyFun_cfc_kaplanskyFunInv. Irreducibility and closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint, together with selfAdjoint_lift, put U in the strong closure of represented original self-adjoint elements. Along the resulting nontrivial neighborhood filter, tendsto_cfc_kaplanskyFun_apply and StarAlgHom.map_cfc make e=R cfc(f,a) approximate T strongly, while norm_cfc_kaplanskyFun_le bounds norm(e) in A by R. Intersecting the two eventual accuracy sets gives simultaneous approximation of x and y.

**Theorem 1.3 (eq_smul_one_of_commute_of_cyclic).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] \{\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)\} \{\omega : H\}, Physicslib4.GNS.IsCyclicVector.\{u_1, u_2\} \pi \omega \to \forall \{T : ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H\}, (\forall (a : A), Eq.\{u_2 + 1\} (HMul.hMul.\{u_2, u_2, u_2\} (\pi a) T) (HMul.hMul.\{u_2, u_2, u_2\} T (\pi a))) \to \forall \{c : \mathbb{C} \}, (\forall (a : A), Eq.\{1\} (Inner.inner.\{0, u_2\} \mathbb{C} \omega (T ((\pi a) \omega ))) (HMul.hMul.\{0, 0, 0\} c (Inner.inner.\{0, u_2\} \mathbb{C} \omega ((\pi a) \omega )))) \to Eq.\{u_2 + 1\} T (HSMul.hSMul.\{0, u_2, u_2\} c 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.eq_smul_one_of_commute_of_cyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Move pi(b) from the first inner-product slot to pi(star b) in the second, commute T through that operator, and apply the proportional coefficient hypothesis at star b*a. Thus T and scalar multiplication by c have the same inner products against every cyclic-orbit vector. DenseRange.eq_of_inner_right identifies their values on the orbit, and Continuous.ext_on extends equality to all of H.

**Theorem 1.4 (coeffFunctional_apply).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] (\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)) (\omega : H) (T : ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H) (a : A), Eq.\{1\} ((Physicslib4.GNS.coeffFunctional.\{u_1, u_2\} \pi \omega T) a) (Inner.inner.\{0, u_2\} \mathbb{C} \omega (T ((\pi a) \omega )))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.coeffFunctional_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuous functional coeffFunctional is obtained by LinearMap.mkContinuous from the coefficient a mapped to inner(Omega,T(pi(a)Omega)). Evaluation retains that defining linear map, so the asserted identity is definitional. The continuity bound used in the definition is norm(Omega) squared times norm(T), using contractivity of pi.

**Theorem 1.5 (coeffFunctional_star_mul).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] \{\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)\} \{\omega : H\} \{T : ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H\}, (\forall (a : A), Eq.\{u_2 + 1\} (HMul.hMul.\{u_2, u_2, u_2\} (\pi a) T) (HMul.hMul.\{u_2, u_2, u_2\} T (\pi a))) \to \forall (a : A), Eq.\{1\} ((Physicslib4.GNS.coeffFunctional.\{u_1, u_2\} \pi \omega T) (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} a) a)) (Inner.inner.\{0, u_2\} \mathbb{C} ((\pi a) \omega ) (T ((\pi a) \omega )))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.coeffFunctional_star_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand pi(star a*a) as pi(star a) composed with pi(a), and use the commutant hypothesis to move T past pi(star a). The identity map_star turns pi(star a) into the adjoint of pi(a); ContinuousLinearMap.adjoint_inner_right then transfers it to the first slot.

**Theorem 1.6 (scalar_of_isSelfAdjoint_of_isPure).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] \{omega : Physicslib4.GNS.State.\{u_1\} A\} \{\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)\} \{\omega : H\}, Physicslib4.GNS.IsCyclicVector.\{u_1, u_2\} \pi \omega \to (\forall (a : A), Eq.\{1\} (omega a) (Inner.inner.\{0, u_2\} \mathbb{C} \omega ((\pi a) \omega ))) \to Physicslib4.GNS.IsPure.\{u_1\} omega \to \forall \{S : ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H\}, IsSelfAdjoint.\{u_2\} S \to (\forall (a : A), Eq.\{u_2 + 1\} (HMul.hMul.\{u_2, u_2, u_2\} (\pi a) S) (HMul.hMul.\{u_2, u_2, u_2\} S (\pi a))) \to \exists (c : \mathbb{C} ), Eq.\{u_2 + 1\} S (HSMul.hSMul.\{0, u_2, u_2\} c 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.scalar_of_isSelfAdjoint_of_isPure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose r>0 with r norm(S) at most one half and set T=r S+one half times the identity. The operator norm estimate bounds every diagonal quadratic form between 0 and norm(v) squared, proving positivity of T and 1-T. By coeffFunctional_star_mul and ContinuousLinearMap.IsPositive.inner_nonneg_right, the coefficient functional of T is positive and dominated by omega. Purity makes it proportional to omega, eq_smul_one_of_commute_of_cyclic makes T scalar, and solving the affine relation makes S scalar.

**Theorem 1.7 (isIrreducible_of_isPure).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] \{omega : Physicslib4.GNS.State.\{u_1\} A\} \{\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)\} \{\omega : H\}, Physicslib4.GNS.IsCyclicVector.\{u_1, u_2\} \pi \omega \to (\forall (a : A), Eq.\{1\} (omega a) (Inner.inner.\{0, u_2\} \mathbb{C} \omega ((\pi a) \omega ))) \to Physicslib4.GNS.IsPure.\{u_1\} omega \to Physicslib4.GNS.IsIrreducible.\{u_1, u_2\} \pi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.isIrreducible_of_isPure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking adjoints of the commutation relation shows that star T also commutes with the representation. Hence the self-adjoint operators T+star T and i(star T-T) commute as well. Apply scalar_of_isSelfAdjoint_of_isPure to each, then reconstruct T as one half times the sum of the first and i times the second.

**Theorem 1.8 (gnsVonNeumann_eq_univ_of_isIrreducible).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] \{\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)\}, Physicslib4.GNS.IsIrreducible.\{u_1, u_2\} \pi \to Eq.\{u_2 + 1\} (Physicslib4.GNS.gnsVonNeumann.\{u_1, u_2\} \pi ) Set.univ.\{u_2\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.gnsVonNeumann_eq_univ_of_isIrreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Irreducibility identifies the centralizer of the representation's range with scalar multiples of 1; smul_one_mem_centralizer supplies the converse inclusion. Every bounded operator commutes with such scalars, so the centralizer of this centralizer is the entire operator space. This proves the full bicommutant equality, beyond a statement only about its center.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.bounded_strong_lift`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.coeffFunctional_apply`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.coeffFunctional_star_mul`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.eq_smul_one_of_commute_of_cyclic`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.gnsVonNeumann_eq_univ_of_isIrreducible`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.isIrreducible_of_isPure`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.scalar_of_isSelfAdjoint_of_isPure`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift.selfAdjoint_lift`
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky](TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.md)
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density](TauCeti/Analysis/VonNeumannAlgebra/Density.md)
