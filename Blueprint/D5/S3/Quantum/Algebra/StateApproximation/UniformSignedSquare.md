# Uniform signed squares in the original algebra

## Abstract

Uniform signed squares in the original algebra

Let A be an arbitrary nontrivial C*-algebra in Type u with PartialOrder A and StarOrderedRing A. Let beta be a real linear positive normalized functional on selfAdjoint A, extreme in the whole original real state space. For every original self-adjoint k with beta(k) nonzero, one finite nonnegative L is chosen before every positive eta. There is an original self-adjoint e of norm at most L. Define square(e) as the self-adjoint subtype of e squared, sigma(r)=1 for positive r and minus one otherwise, and c=sigma(beta(k)) times square(e). The element c is self-adjoint, sigma(beta(k)) times c is nonnegative in A, its original norm is at most L squared, and sqrt(beta(square(c-k))) is less than eta. Both signs are included. There is no finite-dimensional, sequential or separability restriction. This assertion concerns C*-algebras; general JB algebras and the further Jordan-algebra conclusion are separate questions. The construction first forms a positive rank-one operator from pi(k)Omega, then its self-adjoint square root T. The bound L=1+norm(T) precedes the accuracy. Strong self-adjoint density and the original-A truncation e=L times cfc(f,a), f(t)=2t/(1+t squared), give the original norm bound and simultaneous approximation on Omega and T(Omega). Contractivity controls the squared actions. The exact GNS moment identity identifies the original beta square reading with the represented vector norm.

**Theorem 1.1 (sigma_sq).**

$$\forall (r : \mathbb{R} ), Eq.\{1\} (HMul.hMul.\{0, 0, 0\} (UniformSignedSquare.sigma r) (UniformSignedSquare.sigma r)) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.sigma_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

By the definition of sigma, its value is 1 when r is positive and -1 otherwise. In either branch multiplying it by itself gives 1. The nonpositive branch includes r=0, so no nonzero hypothesis is needed for this identity.

**Theorem 1.2 (sigma_abs).**

$$\forall (r : \mathbb{R} ), Eq.\{1\} (abs.\{0\} (UniformSignedSquare.sigma r)) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.sigma_abs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfold sigma and split on positivity of r. Both possible values, 1 and -1, have absolute value 1, including the convention at zero. This identity will remove the sign from norm estimates.

**Theorem 1.3 (signedSquare_cone).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (r : \mathbb{R} ) (e : \operatorname{carrier} (selfAdjoint.\{u\} A)), LE.le.\{u\} 0 (HSMul.hSMul.\{0, u, u\} (UniformSignedSquare.sigma r) \operatorname{coe} (UniformSignedSquare.signedSquare.\{u\} r e))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.signedSquare_cone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand signedSquare as sigma(r) times the original algebra square of e. Scalar associativity and sigma_sq cancel the two signs. IsSelfAdjoint.sq_nonneg then gives positivity of e squared in the original ordered C*-algebra.

**Theorem 1.4 (signedSquare_norm).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (r : \mathbb{R} ) (e : \operatorname{carrier} (selfAdjoint.\{u\} A)) \{L : \mathbb{R} \}, LE.le.\{0\} 0 L \to LE.le.\{0\} (Norm.norm.\{u\} e) L \to LE.le.\{0\} (Norm.norm.\{u\} \operatorname{coe} (UniformSignedSquare.signedSquare.\{u\} r e)) (HPow.hPow.\{0, 0, 0\} L 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.signedSquare_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

norm_smul and sigma_abs remove the sign without changing the norm. norm_pow_le bounds the original square norm by norm(e) squared. Since both norm(e) and L are nonnegative and norm(e) is at most L, squaring preserves this bound and gives L squared.

**Theorem 1.5 (selfAdjoint_lift).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] \{H : Type v\} [NormedAddCommGroup.\{v\} H] [InnerProductSpace.\{0, v\} \mathbb{C} H] [CompleteSpace.\{v\} H] (\pi : StarAlgHom.\{0, u, v\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, v, v\} (RingHom.id.\{0\} \mathbb{C} ) H H)) \{b : ContinuousLinearMap.\{0, 0, v, v\} (RingHom.id.\{0\} \mathbb{C} ) H H\}, Membership.mem.\{v, v\} (StarAlgHom.range.\{0, u, v\} \pi ) b \to IsSelfAdjoint.\{v\} b \to \exists (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{v + 1\} (\pi \operatorname{coe} a) b$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.selfAdjoint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose any original preimage a of b from membership in pi.range, and replace it by its real symmetrization one half times (a+star a). map_add and map_star show that its image is one half times (b+star b), which equals b by self-adjointness. The construction needs no faithful or injective representation.

**Theorem 1.6 (bounded_strong_lift).**

$$\forall A \in \operatorname{Type} u,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall H \in \operatorname{Type} v,\; [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] [\operatorname{CompleteSpace}\left(H\right)] \forall pi \in \operatorname{StarAlgHom}\left(\mathbb{C}, A, \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)\right),\; (\operatorname{IsIrreducible}\left(pi\right)) \Rightarrow (\forall T \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; (\operatorname{IsSelfAdjoint}\left(T\right)) \Rightarrow (\exists L \in \mathbb{R},\; (0 < L) \land (\forall x \in H,\; \forall y \in H,\; \forall delta \in \mathbb{R},\; (0 < delta) \Rightarrow (\exists e \in \operatorname{selfAdjoint}\left(A\right),\; (\left\lVert e \right\rVert \le L) \land ((\left\lVert pi\left((e:A)\right)\left(x\right) - T\left(x\right) \right\rVert < delta) \land (\left\lVert pi\left((e:A)\right)\left(y\right) - T\left(y\right) \right\rVert < delta))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.bounded_strong_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set R=1+norm(T) before choosing vectors or accuracy and normalize B=T/R to a self-adjoint contraction. Its inverse Kaplansky value U satisfies f(U)=B by cfc_kaplanskyFun_cfc_kaplanskyFunInv. Irreducibility and closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint, together with selfAdjoint_lift, put U in the strong closure of represented original self-adjoint elements. Along the resulting nontrivial neighborhood filter, tendsto_cfc_kaplanskyFun_apply and StarAlgHom.map_cfc make e=R cfc(f,a) approximate T strongly, while norm_cfc_kaplanskyFun_le bounds norm(e) in A by R. Intersecting the two eventual accuracy sets gives simultaneous approximation of x and y.

**Theorem 1.7 (square_reading).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] \{H : Type v\} [NormedAddCommGroup.\{v\} H] [InnerProductSpace.\{0, v\} \mathbb{C} H] [CompleteSpace.\{v\} H] (\beta : LinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{R} ) \operatorname{carrier} (selfAdjoint.\{u\} A) \mathbb{R} ) (\pi : StarAlgHom.\{0, u, v\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, v, v\} (RingHom.id.\{0\} \mathbb{C} ) H H)) (\omega : H), (\forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (Inner.inner.\{0, v\} \mathbb{C} \omega ((\pi \operatorname{coe} a) \omega )) \operatorname{coe} (\beta a)) \to \forall (d : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (\operatorname{sqrt} (\beta (UniformSignedSquare.square.\{u\} d))) (Norm.norm.\{v\} ((\pi \operatorname{coe} d) \omega ))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.square_reading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Self-adjointness of d makes pi(d) equal to its adjoint. apply_norm_sq_eq_inner_adjoint_right and multiplicativity express norm(pi(d)Omega) squared as the real part of the moment of d squared. The hypothesis hm identifies that moment with beta(square d), and Real.sqrt_sq removes the square using nonnegativity of the norm.

**Theorem 1.8 (signed_endpoint).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] \{H : Type v\} [NormedAddCommGroup.\{v\} H] [InnerProductSpace.\{0, v\} \mathbb{C} H] [CompleteSpace.\{v\} H] (\pi : StarAlgHom.\{0, u, v\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, v, v\} (RingHom.id.\{0\} \mathbb{C} ) H H)) (\omega : H) (\beta : LinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{R} ) \operatorname{carrier} (selfAdjoint.\{u\} A) \mathbb{R} ), (\forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (Inner.inner.\{0, v\} \mathbb{C} \omega ((\pi \operatorname{coe} a) \omega )) \operatorname{coe} (\beta a)) \to \forall (k : \operatorname{carrier} (selfAdjoint.\{u\} A)), Ne.\{1\} (\beta k) 0 \to \exists (T : ContinuousLinearMap.\{0, 0, v, v\} (RingHom.id.\{0\} \mathbb{C} ) H H), IsSelfAdjoint.\{v\} T \land Eq.\{v + 1\} (T (T \omega )) (HSMul.hSMul.\{0, v, v\} (UniformSignedSquare.sigma (\beta k)) ((\pi \operatorname{coe} k) \omega ))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.signed_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write r=beta(k) and v=pi(k)Omega. Self-adjoint symmetry and hm give inner(v,Omega)=r. The positive rank-one operator S=abs(r) inverse times rankOne(v,v) therefore sends Omega to sigma(r)v, since r is nonzero and r/abs(r)=sigma(r). CFC.sqrt_nonneg makes T=sqrt(S) self-adjoint, and CFC.sqrt_mul_sqrt_self gives the required action of T squared. Both signs of r are handled explicitly.

**Theorem 1.9 (uniform_signed_original_square).**

$$\forall A \in \operatorname{Type} u,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall beta \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{selfAdjoint}\left(A\right), \mathbb{R}\right),\; (\operatorname{IsRealState}\left(beta\right)) \Rightarrow ((beta \in \operatorname{extremePoints}\left(\mathbb{R}, \operatorname{realStateSpace}\left(A\right)\right)) \Rightarrow (\forall k \in \operatorname{selfAdjoint}\left(A\right),\; (beta\left(k\right) \ne 0) \Rightarrow (\exists L \in \mathbb{R},\; (0 \le L) \land (\forall eta \in \mathbb{R},\; (0 < eta) \Rightarrow (\exists e \in \operatorname{selfAdjoint}\left(A\right),\; (\left\lVert e \right\rVert \le L) \land ((\operatorname{IsSelfAdjoint}\left((\operatorname{signedSquare}\left(beta\left(k\right), e\right):A)\right)) \land ((0 \le (\operatorname{sigma}\left(beta\left(k\right)\right)) \cdot ((\operatorname{signedSquare}\left(beta\left(k\right), e\right):A))) \land ((\left\lVert (\operatorname{signedSquare}\left(beta\left(k\right), e\right):A) \right\rVert \le L^{2}) \land (\operatorname{sqrt}\left(beta\left(\operatorname{square}\left(\operatorname{signedSquare}\left(beta\left(k\right), e\right) - k\right)\right)\right) < eta)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.uniform_signed_original_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

actual_pure_gns supplies the same-universe irreducible representation and exact original moments. Obtain T from signed_endpoint, then choose the bound L from bounded_strong_lift before any eta. Given eta>0, approximate T simultaneously on Omega and T(Omega) to delta=eta/(L+1); contractivity of pi bounds E=pi(e) by L, so the square error is less than L delta+delta=eta. square_reading converts this vector error into the original beta square reading; sigma_sq and sigma_abs preserve the sign and norm, while signedSquare_cone and signedSquare_norm provide the remaining original-algebra conclusions.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.bounded_strong_lift`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.selfAdjoint_lift`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.sigma_abs`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.sigma_sq`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.signedSquare_cone`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.signedSquare_norm`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.signed_endpoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.square_reading`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.uniform_signed_original_square`
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS](ReconstructedStateGNS.md)
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky](TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.md)
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density](TauCeti/Analysis/VonNeumannAlgebra/Density.md)
