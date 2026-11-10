# Pure cyclic representations and commutants

## Abstract

Pure cyclic representations and commutants

A cyclic representation reproducing a pure state has scalar commutant: every bounded operator commuting with all represented elements is a complex scalar multiple of the identity. Consequently its bicommutant is all bounded operators. The Hilbert space and algebra are arbitrary in their respective universes, with no finite-dimensional or separability restriction.

**Theorem 1.1 (gns_construction).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] (omega : Physicslib4.GNS.State.\{u\} A), \exists (H : Type u) (x : NormedAddCommGroup.\{u\} H) (x_1 : InnerProductSpace.\{0, u\} \mathbb{C} H) (x_2 : CompleteSpace.\{u\} H) (\pi : StarAlgHom.\{0, u, u\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u, u\} (RingHom.id.\{0\} \mathbb{C} ) H H)) (\omega : H), Physicslib4.GNS.IsCyclicVector.\{u, u\} \pi \omega \land (\forall (a : A), Eq.\{1\} (omega a) (Inner.inner.\{0, u\} \mathbb{C} \omega ((\pi a) \omega ))) \land (Physicslib4.GNS.State.IsFaithful.\{u\} omega \to Function.Injective.\{u + 1, u + 1\} \operatorname{coe} \pi )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.gns_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Give A its spectral order and apply Mathlib's PositiveLinearMap GNS construction to State.toPositiveLinearMap. Take Omega to be the completed image of 1; left multiplication sends it to the image of a, so UniformSpace.Completion.denseRange_coe proves cyclicity and preGNS_inner_def gives the moment identity. If omega is faithful, equality of represented operators makes the squared GNS norm of a-b zero, contradicting strict positivity unless a=b. The completion stays in the universe of A.

**Theorem 1.2 (eq_smul_one_of_commute_of_cyclic).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] \{\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)\} \{\omega : H\}, Physicslib4.GNS.IsCyclicVector.\{u_1, u_2\} \pi \omega \to \forall \{T : ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H\}, (\forall (a : A), Eq.\{u_2 + 1\} (HMul.hMul.\{u_2, u_2, u_2\} (\pi a) T) (HMul.hMul.\{u_2, u_2, u_2\} T (\pi a))) \to \forall \{c : \mathbb{C} \}, (\forall (a : A), Eq.\{1\} (Inner.inner.\{0, u_2\} \mathbb{C} \omega (T ((\pi a) \omega ))) (HMul.hMul.\{0, 0, 0\} c (Inner.inner.\{0, u_2\} \mathbb{C} \omega ((\pi a) \omega )))) \to Eq.\{u_2 + 1\} T (HSMul.hSMul.\{0, u_2, u_2\} c 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.eq_smul_one_of_commute_of_cyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Move pi(b) from the first inner-product slot to pi(star b) in the second, commute T through that operator, and apply the proportional coefficient hypothesis at star b*a. Thus T and scalar multiplication by c have the same inner products against every cyclic-orbit vector. DenseRange.eq_of_inner_right identifies their values on the orbit, and Continuous.ext_on extends equality to all of H.

**Theorem 1.3 (coeffFunctional_apply).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] (\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)) (\omega : H) (T : ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H) (a : A), Eq.\{1\} ((Physicslib4.GNS.coeffFunctional.\{u_1, u_2\} \pi \omega T) a) (Inner.inner.\{0, u_2\} \mathbb{C} \omega (T ((\pi a) \omega )))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.coeffFunctional_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuous functional coeffFunctional is obtained by LinearMap.mkContinuous from the coefficient a mapped to inner(Omega,T(pi(a)Omega)). Evaluation retains that defining linear map, so the asserted identity is definitional. The continuity bound used in the definition is norm(Omega) squared times norm(T), using contractivity of pi.

**Theorem 1.4 (coeffFunctional_star_mul).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] \{\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)\} \{\omega : H\} \{T : ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H\}, (\forall (a : A), Eq.\{u_2 + 1\} (HMul.hMul.\{u_2, u_2, u_2\} (\pi a) T) (HMul.hMul.\{u_2, u_2, u_2\} T (\pi a))) \to \forall (a : A), Eq.\{1\} ((Physicslib4.GNS.coeffFunctional.\{u_1, u_2\} \pi \omega T) (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} a) a)) (Inner.inner.\{0, u_2\} \mathbb{C} ((\pi a) \omega ) (T ((\pi a) \omega )))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.coeffFunctional_star_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand pi(star a*a) as pi(star a) composed with pi(a), and use the commutant hypothesis to move T past pi(star a). The identity map_star turns pi(star a) into the adjoint of pi(a); ContinuousLinearMap.adjoint_inner_right then transfers it to the first slot.

**Theorem 1.5 (isPositive_inner_nonneg).**

$$\forall \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] \{S : ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H\}, ContinuousLinearMap.IsPositive.\{0, u_2\} S \to \forall (v : H), LE.le.\{0\} 0 (Inner.inner.\{0, u_2\} \mathbb{C} v (S v))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.isPositive_inner_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real part is nonnegative by IsPositive.re_inner_nonneg_right. Symmetry of the positive operator, together with inner_conj_symm, makes the diagonal coefficient equal to its conjugate, so Complex.conj_eq_iff_im forces its imaginary part to be zero. Complex.le_def combines these facts; completeness is unnecessary.

**Theorem 1.6 (scalar_of_isSelfAdjoint_of_isPure).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] \{omega : Physicslib4.GNS.State.\{u_1\} A\} \{\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)\} \{\omega : H\}, Physicslib4.GNS.IsCyclicVector.\{u_1, u_2\} \pi \omega \to (\forall (a : A), Eq.\{1\} (omega a) (Inner.inner.\{0, u_2\} \mathbb{C} \omega ((\pi a) \omega ))) \to Physicslib4.GNS.IsPure.\{u_1\} omega \to \forall \{S : ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H\}, IsSelfAdjoint.\{u_2\} S \to (\forall (a : A), Eq.\{u_2 + 1\} (HMul.hMul.\{u_2, u_2, u_2\} (\pi a) S) (HMul.hMul.\{u_2, u_2, u_2\} S (\pi a))) \to \exists (c : \mathbb{C} ), Eq.\{u_2 + 1\} S (HSMul.hSMul.\{0, u_2, u_2\} c 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.scalar_of_isSelfAdjoint_of_isPure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose r>0 with r norm(S) at most one half and set T=r S+one half times the identity. The operator norm estimate bounds every diagonal quadratic form between 0 and norm(v) squared, proving positivity of T and 1-T. By coeffFunctional_star_mul and isPositive_inner_nonneg, the coefficient functional of T is positive and dominated by omega. Purity makes it proportional to omega, eq_smul_one_of_commute_of_cyclic makes T scalar, and solving the affine relation makes S scalar.

**Theorem 1.7 (isIrreducible_of_isPure).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] \{omega : Physicslib4.GNS.State.\{u_1\} A\} \{\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)\} \{\omega : H\}, Physicslib4.GNS.IsCyclicVector.\{u_1, u_2\} \pi \omega \to (\forall (a : A), Eq.\{1\} (omega a) (Inner.inner.\{0, u_2\} \mathbb{C} \omega ((\pi a) \omega ))) \to Physicslib4.GNS.IsPure.\{u_1\} omega \to Physicslib4.GNS.IsIrreducible.\{u_1, u_2\} \pi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.isIrreducible_of_isPure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking adjoints of the commutation relation shows that star T also commutes with the representation. Hence the self-adjoint operators T+star T and i(star T-T) commute as well. Apply scalar_of_isSelfAdjoint_of_isPure to each, then reconstruct T as one half times the sum of the first and i times the second.

**Theorem 1.8 (gnsVonNeumann_eq_univ_of_isIrreducible).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] \{H : Type u_2\} [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{0, u_2\} \mathbb{C} H] [CompleteSpace.\{u_2\} H] \{\pi : StarAlgHom.\{0, u_1, u_2\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u_2, u_2\} (RingHom.id.\{0\} \mathbb{C} ) H H)\}, Physicslib4.GNS.IsIrreducible.\{u_1, u_2\} \pi \to Eq.\{u_2 + 1\} (Physicslib4.GNS.gnsVonNeumann.\{u_1, u_2\} \pi ) Set.univ.\{u_2\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.gnsVonNeumann_eq_univ_of_isIrreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Irreducibility identifies the centralizer of the representation's range with scalar multiples of 1; smul_one_mem_centralizer supplies the converse inclusion. Every bounded operator commutes with such scalars, so the centralizer of this centralizer is the entire operator space. This proves the full bicommutant equality, beyond a statement only about its center.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.coeffFunctional_apply`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.coeffFunctional_star_mul`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.eq_smul_one_of_commute_of_cyclic`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.gnsVonNeumann_eq_univ_of_isIrreducible`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.gns_construction`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.isIrreducible_of_isPure`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.isPositive_inner_nonneg`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility.scalar_of_isSelfAdjoint_of_isPure`
