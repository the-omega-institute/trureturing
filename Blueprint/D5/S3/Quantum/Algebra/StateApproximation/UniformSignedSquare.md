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

**Theorem 1.5 (square_reading).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] \{H : Type v\} [NormedAddCommGroup.\{v\} H] [InnerProductSpace.\{0, v\} \mathbb{C} H] [CompleteSpace.\{v\} H] (\beta : LinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{R} ) \operatorname{carrier} (selfAdjoint.\{u\} A) \mathbb{R} ) (\pi : StarAlgHom.\{0, u, v\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, v, v\} (RingHom.id.\{0\} \mathbb{C} ) H H)) (\omega : H), (\forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (Inner.inner.\{0, v\} \mathbb{C} \omega ((\pi \operatorname{coe} a) \omega )) \operatorname{coe} (\beta a)) \to \forall (d : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (\operatorname{sqrt} (\beta (UniformSignedSquare.square.\{u\} d))) (Norm.norm.\{v\} ((\pi \operatorname{coe} d) \omega ))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.square_reading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Self-adjointness of d makes pi(d) equal to its adjoint. apply_norm_sq_eq_inner_adjoint_right and multiplicativity express norm(pi(d)Omega) squared as the real part of the moment of d squared. The hypothesis hm identifies that moment with beta(square d), and Real.sqrt_sq removes the square using nonnegativity of the norm.

**Theorem 1.6 (signed_endpoint).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] \{H : Type v\} [NormedAddCommGroup.\{v\} H] [InnerProductSpace.\{0, v\} \mathbb{C} H] [CompleteSpace.\{v\} H] (\pi : StarAlgHom.\{0, u, v\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, v, v\} (RingHom.id.\{0\} \mathbb{C} ) H H)) (\omega : H) (\beta : LinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{R} ) \operatorname{carrier} (selfAdjoint.\{u\} A) \mathbb{R} ), (\forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (Inner.inner.\{0, v\} \mathbb{C} \omega ((\pi \operatorname{coe} a) \omega )) \operatorname{coe} (\beta a)) \to \forall (k : \operatorname{carrier} (selfAdjoint.\{u\} A)), Ne.\{1\} (\beta k) 0 \to \exists (T : ContinuousLinearMap.\{0, 0, v, v\} (RingHom.id.\{0\} \mathbb{C} ) H H), IsSelfAdjoint.\{v\} T \land Eq.\{v + 1\} (T (T \omega )) (HSMul.hSMul.\{0, v, v\} (UniformSignedSquare.sigma (\beta k)) ((\pi \operatorname{coe} k) \omega ))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.signed_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write r=beta(k) and v=pi(k)Omega. Self-adjoint symmetry and hm give inner(v,Omega)=r. The positive rank-one operator S=abs(r) inverse times rankOne(v,v) therefore sends Omega to sigma(r)v, since r is nonzero and r/abs(r)=sigma(r). CFC.sqrt_nonneg makes T=sqrt(S) self-adjoint, and CFC.sqrt_mul_sqrt_self gives the required action of T squared. Both signs of r are handled explicitly.

**Theorem 1.7 (uniform_signed_original_square).**

$$\forall A \in \operatorname{Type} u,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall beta \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{selfAdjoint}\left(A\right), \mathbb{R}\right),\; (\operatorname{IsRealState}\left(beta\right)) \Rightarrow ((beta \in \operatorname{extremePoints}\left(\mathbb{R}, \operatorname{realStateSpace}\left(A\right)\right)) \Rightarrow (\forall k \in \operatorname{selfAdjoint}\left(A\right),\; (beta\left(k\right) \ne 0) \Rightarrow (\exists L \in \mathbb{R},\; (0 \le L) \land (\forall eta \in \mathbb{R},\; (0 < eta) \Rightarrow (\exists e \in \operatorname{selfAdjoint}\left(A\right),\; (\left\lVert e \right\rVert \le L) \land ((\operatorname{IsSelfAdjoint}\left((\operatorname{signedSquare}\left(beta\left(k\right), e\right):A)\right)) \land ((0 \le (\operatorname{sigma}\left(beta\left(k\right)\right)) \cdot ((\operatorname{signedSquare}\left(beta\left(k\right), e\right):A))) \land ((\left\lVert (\operatorname{signedSquare}\left(beta\left(k\right), e\right):A) \right\rVert \le L^{2}) \land (\operatorname{sqrt}\left(beta\left(\operatorname{square}\left(\operatorname{signedSquare}\left(beta\left(k\right), e\right) - k\right)\right)\right) < eta)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.uniform_signed_original_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

actual_pure_gns supplies the same-universe irreducible representation and exact original moments. Obtain T from signed_endpoint, then choose the bound L from bounded_strong_lift before any eta. Given eta>0, approximate T simultaneously on Omega and T(Omega) to delta=eta/(L+1); contractivity of pi bounds E=pi(e) by L, so the square error is less than L delta+delta=eta. square_reading converts this vector error into the original beta square reading; sigma_sq and sigma_abs preserve the sign and norm, while signedSquare_cone and signedSquare_norm provide the remaining original-algebra conclusions.

**Theorem 1.8 (gns_construction).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] (omega : Physicslib4.GNS.State.\{u\} A), \exists (H : Type u) (x : NormedAddCommGroup.\{u\} H) (x_1 : InnerProductSpace.\{0, u\} \mathbb{C} H) (x_2 : CompleteSpace.\{u\} H) (\pi : StarAlgHom.\{0, u, u\} \mathbb{C} A (ContinuousLinearMap.\{0, 0, u, u\} (RingHom.id.\{0\} \mathbb{C} ) H H)) (\omega : H), Physicslib4.GNS.IsCyclicVector.\{u, u\} \pi \omega \land (\forall (a : A), Eq.\{1\} (omega a) (Inner.inner.\{0, u\} \mathbb{C} \omega ((\pi a) \omega ))) \land (Physicslib4.GNS.State.IsFaithful.\{u\} omega \to Function.Injective.\{u + 1, u + 1\} \operatorname{coe} \pi )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.gns_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Give A its spectral order and apply Mathlib's PositiveLinearMap GNS construction to State.toPositiveLinearMap. Take Omega to be the completed image of 1; left multiplication sends it to the image of a, so UniformSpace.Completion.denseRange_coe proves cyclicity and preGNS_inner_def gives the moment identity. If omega is faithful, equality of represented operators makes the squared GNS norm of a-b zero, contradicting strict positivity unless a=b. The completion stays in the universe of A.

**Theorem 1.9 (norm_eq_re_apply_one_of_positive).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] [Nontrivial.\{u_1\} A] \{\phi : ContinuousLinearMap.\{0, 0, u_1, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} \}, (\forall (a : A), LE.le.\{0\} 0 (\phi (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} a) a))) \to Eq.\{1\} (Norm.norm.\{u_1\} \phi ) (\phi 1).re$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.norm_eq_re_apply_one_of_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equip A locally with its spectral order. Positivity on star(b) times b makes phi a positive continuous linear map by CStarAlgebra.nonneg_iff_eq_star_mul_self and PositiveContinuousLinearMap.mk₀. Apply the pinned PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one and take real parts. The local order does not add a hypothesis on A.

**Theorem 1.10 (apply_one).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] (omega : Physicslib4.GNS.State.\{u_1\} A), Eq.\{1\} (omega 1) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.apply_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The helper nontrivial_of_state excludes the zero algebra using the normalized operator norm. Then norm_eq_re_apply_one_of_positive identifies the real part of omega(1) with 1, while positivity at 1 forces its imaginary part to vanish. Complex extensionality gives the value 1.

**Theorem 1.11 (isExtremePoint_of_isPure).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] (omega : Physicslib4.GNS.State.\{u_1\} A), Physicslib4.GNS.IsPure.\{u_1\} omega \to Physicslib4.GNS.State.IsExtremePoint.\{u_1\} omega$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.isExtremePoint_of_isPure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a decomposition with 0<t<1, the positive functional psi=t omega1 is dominated by omega because the remaining term (1-t) omega2 is positive. Purity makes psi a scalar multiple of omega; State.apply_one fixes that scalar to t. Cancellation first identifies omega1 with omega, and then the decomposition identifies omega2 with omega.

**Theorem 1.12 (isPure_of_isExtremePoint).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] (omega : Physicslib4.GNS.State.\{u_1\} A), Physicslib4.GNS.State.IsExtremePoint.\{u_1\} omega \to Physicslib4.GNS.IsPure.\{u_1\} omega$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.isPure_of_isExtremePoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a dominated positive psi, norm_eq_re_apply_one_of_positive gives lambda=Re(psi(1))=norm(psi) in [0,1]. If lambda=0 then psi=0; if lambda=1 the positive complement omega-psi has norm zero. Otherwise normalize psi and omega-psi by lambda and 1-lambda to obtain two states in a genuine convex decomposition of omega; extremality equates these states and yields psi=lambda omega.

**Theorem 1.13 (isPure_iff_isExtremePoint).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] (omega : Physicslib4.GNS.State.\{u_1\} A), Physicslib4.GNS.IsPure.\{u_1\} omega \iff Physicslib4.GNS.State.IsExtremePoint.\{u_1\} omega$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.isPure_iff_isExtremePoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two implications are isExtremePoint_of_isPure and isPure_of_isExtremePoint. Their conjunction identifies the order-theoretic domination definition of purity with the pointwise convex-decomposition definition of extremality; no new characterization of representations is required here.

**Theorem 1.14 (toContinuousLinearMap_injective).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A], Function.Injective.\{u_1 + 1, u_1 + 1\} Physicslib4.GNS.State.toContinuousLinearMap.\{u_1\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.toContinuousLinearMap_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A State consists of its continuous linear functional and proofs of positivity and normalization. Equality of the functional therefore determines equality of states, since the remaining fields are propositions; State.mk.injEq implements this extensionality.

**Theorem 1.15 (mem_extremePoints_iff_isExtremePoint).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] (omega : Physicslib4.GNS.State.\{u_1\} A), Membership.mem.\{u_1, u_1\} (Set.extremePoints.\{0, u_1\} \mathbb{R} (Physicslib4.GNS.stateSpace.\{u_1\} A)) (Physicslib4.GNS.State.toContinuousLinearMap.\{u_1\} omega ) \iff Physicslib4.GNS.State.IsExtremePoint.\{u_1\} omega$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.mem_extremePoints_iff_isExtremePoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translate a pointwise convex decomposition into membership of an openSegment in the real vector space of continuous linear functionals. In the forward direction, Mathlib's mem_extremePoints equates the endpoint functionals and State.toContinuousLinearMap_injective equates their states. Conversely write the positive segment coefficients as t and 1-t, apply State.IsExtremePoint, and use their sum being 1 to identify both endpoints with omega.

**Theorem 1.16 (state_abs_le).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : LinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{R} ) \operatorname{carrier} (selfAdjoint.\{u\} A) \mathbb{R} ), ReconstructedStateGNS.IsRealState.\{u\} \beta \to \forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), LE.le.\{0\} (abs.\{0\} (\beta a)) (Norm.norm.\{u\} a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.state_abs_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity on y-x makes beta monotone. The self-adjoint order bounds neg_algebraMap_norm_le_self and le_algebraMap_norm_self place a between minus norm(a) times 1 and norm(a) times 1. Apply monotonicity and beta(1)=1 to these bounds, then use abs_le.

**Theorem 1.17 (realCLM_norm_le).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : LinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{R} ) \operatorname{carrier} (selfAdjoint.\{u\} A) \mathbb{R} ) (h\beta : ReconstructedStateGNS.IsRealState.\{u\} \beta ), LE.le.\{0\} (Norm.norm.\{u\} (ReconstructedStateGNS.realCLM.\{u\} \beta h\beta )) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.realCLM_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The estimate state_abs_le bounds the original real linear functional by norm(a) with constant 1. LinearMap.mkContinuous_norm_le therefore bounds the operator norm of realCLM by 1; continuity is obtained from positivity and normalization rather than assumed of beta.

**Theorem 1.18 (state_moment).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\phi : ContinuousLinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} ), Membership.mem.\{u, u\} (ReconstructedStateGNS.complexStateSpace.\{u\} A) \phi \to \forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (\phi \operatorname{coe} a) \operatorname{coe} ((ReconstructedStateGNS.restriction.\{u\} \phi ) a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.state_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Regard phi as the positive map positiveMap phi hphi. Positive maps preserve self-adjointness, so phi(a) is a real complex number for self-adjoint a. Complex.re_eq_ofReal_of_isSelfAdjoint identifies it with the embedded real part, which is exactly restriction phi a.

**Theorem 1.19 (restriction_mem).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\phi : ContinuousLinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} ), Membership.mem.\{u, u\} (ReconstructedStateGNS.complexStateSpace.\{u\} A) \phi \to Membership.mem.\{u, u\} (ReconstructedStateGNS.realStateSpace.\{u\} A) (ReconstructedStateGNS.restriction.\{u\} \phi )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.restriction_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive original self-adjoint a, positivity of phi and Complex.nonneg_iff give nonnegativity of its real part. At the unit, phi(1)=1 implies that the restriction has value 1. These are precisely the two conditions of IsRealState.

**Theorem 1.20 (ext_selfAdjoint).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\phi \psi : ContinuousLinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} ), (\forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (\phi \operatorname{coe} a) (\psi \operatorname{coe} a)) \to Eq.\{u + 1\} \phi \psi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.ext_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decompose an arbitrary a with realPart_add_I_smul_imaginaryPart into a self-adjoint real part plus i times a self-adjoint imaginary part. Complex linearity and the assumed equality on both parts imply equality at a, and continuous-linear-map extensionality finishes.

**Theorem 1.21 (exists_extension).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : LinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{R} ) \operatorname{carrier} (selfAdjoint.\{u\} A) \mathbb{R} ), ReconstructedStateGNS.IsRealState.\{u\} \beta \to \exists (\phi : ContinuousLinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} ), Membership.mem.\{u, u\} (ReconstructedStateGNS.complexStateSpace.\{u\} A) \phi \land \forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (\phi \operatorname{coe} a) \operatorname{coe} (\beta a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.exists_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply exists_positive_extensions_norm_additive to realCLM beta, obtaining positive p,n with beta=Re(p-n) on the self-adjoint part and norm(realCLM)=Re(p(1))+Re(n(1)). Normalization and realCLM_norm_le force Re(n(1))=0. PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one then makes n zero. Self-adjoint preservation identifies p(a) with the embedded beta(a), including p(1)=1, so p is the required positive normalized complex extension.

**Theorem 1.22 (extension_moment).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)) (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (\operatorname{coe} (ReconstructedStateGNS.extension.\{u\} \beta ) \operatorname{coe} a) \operatorname{coe} (\operatorname{coe} \beta a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.extension_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The extension is chosen from exists_extension, whose second conclusion specifies every original self-adjoint moment. Its choose_spec therefore supplies this equality for each a. This records the exact moments of the chosen extension, without adding a continuity assumption on the starting beta.

**Theorem 1.23 (restriction_extension).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)), Eq.\{u + 1\} (ReconstructedStateGNS.restriction.\{u\} \operatorname{coe} (ReconstructedStateGNS.extension.\{u\} \beta )) \operatorname{coe} \beta$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.restriction_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate both real linear maps at an arbitrary self-adjoint a. By extension_moment the complex value of the extension is the embedded beta(a); taking its real part and using Complex.ofReal_re recovers beta(a). Extensionality gives equality of maps.

**Theorem 1.24 (extension_restriction).**

$$\forall \{A : Type u\} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A] (\phi : complexStateSpace A), extension \langle restriction \phi .val, restriction_{mem} \phi .val \phi .property\rangle = \phi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.extension_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use ext_selfAdjoint to compare the two complex states after Subtype.ext. On each self-adjoint a, extension_moment equals the embedded restriction of phi, while state_moment identifies the latter with phi(a). Thus extension after restriction recovers the original complex state.

**Theorem 1.25 (extension_affine_iff).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (x y z : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)) (s t : \mathbb{R} ), Eq.\{u + 1\} (\operatorname{coe} z) (HAdd.hAdd.\{u, u, u\} (HSMul.hSMul.\{0, u, u\} s \operatorname{coe} x) (HSMul.hSMul.\{0, u, u\} t \operatorname{coe} y)) \iff Eq.\{u + 1\} (\operatorname{coe} (ReconstructedStateGNS.extension.\{u\} z)) (HAdd.hAdd.\{u, u, u\} (HSMul.hSMul.\{0, u, u\} s \operatorname{coe} (ReconstructedStateGNS.extension.\{u\} x)) (HSMul.hSMul.\{0, u, u\} t \operatorname{coe} (ReconstructedStateGNS.extension.\{u\} y)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.extension_affine_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the forward implication, evaluate the real affine identity at a self-adjoint element, embed the resulting real equality into the complex numbers, and use extension_moment and ext_selfAdjoint. For the reverse implication apply the real linear map restriction to the complex affine identity and simplify with restriction_extension. The coefficients s,t are arbitrary real numbers, without convexity assumptions.

**Theorem 1.26 (extreme_forward).**

$$\forall \{E : Type u_1\} \{F : Type u_2\} [AddCommGroup.\{u_1\} E] [Module.\{0, u_1\} \mathbb{R} E] [AddCommGroup.\{u_2\} F] [Module.\{0, u_2\} \mathbb{R} F] \{S : Set.\{u_1\} E\} \{T : Set.\{u_2\} F\} (e : Equiv.\{u_1 + 1, u_2 + 1\} \operatorname{coe} S \operatorname{coe} T), (\forall (x y z : \operatorname{coe} S) (s t : \mathbb{R} ), Eq.\{u_1 + 1\} (\operatorname{coe} z) (HAdd.hAdd.\{u_1, u_1, u_1\} (HSMul.hSMul.\{0, u_1, u_1\} s \operatorname{coe} x) (HSMul.hSMul.\{0, u_1, u_1\} t \operatorname{coe} y)) \iff Eq.\{u_2 + 1\} (\operatorname{coe} (e z)) (HAdd.hAdd.\{u_2, u_2, u_2\} (HSMul.hSMul.\{0, u_2, u_2\} s \operatorname{coe} (e x)) (HSMul.hSMul.\{0, u_2, u_2\} t \operatorname{coe} (e y)))) \to \forall (x : \operatorname{coe} S), Membership.mem.\{u_1, u_1\} (Set.extremePoints.\{0, u_1\} \mathbb{R} S) \operatorname{coe} x \to Membership.mem.\{u_2, u_2\} (Set.extremePoints.\{0, u_2\} \mathbb{R} T) \operatorname{coe} (e x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.extreme_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use mem_extremePoints_iff_left. Pull the two endpoints of a target open segment back through e.symm, and use haff to pull back its same positive coefficients and sum-one relation. Extremality of x forces the first preimage to equal x; applying e transports that equality to the target endpoint.

**Theorem 1.27 (extreme_equiv).**

$$\forall \{E : Type u_1\} \{F : Type u_2\} [AddCommGroup.\{u_1\} E] [Module.\{0, u_1\} \mathbb{R} E] [AddCommGroup.\{u_2\} F] [Module.\{0, u_2\} \mathbb{R} F] \{S : Set.\{u_1\} E\} \{T : Set.\{u_2\} F\} (e : Equiv.\{u_1 + 1, u_2 + 1\} \operatorname{coe} S \operatorname{coe} T), (\forall (x y z : \operatorname{coe} S) (s t : \mathbb{R} ), Eq.\{u_1 + 1\} (\operatorname{coe} z) (HAdd.hAdd.\{u_1, u_1, u_1\} (HSMul.hSMul.\{0, u_1, u_1\} s \operatorname{coe} x) (HSMul.hSMul.\{0, u_1, u_1\} t \operatorname{coe} y)) \iff Eq.\{u_2 + 1\} (\operatorname{coe} (e z)) (HAdd.hAdd.\{u_2, u_2, u_2\} (HSMul.hSMul.\{0, u_2, u_2\} s \operatorname{coe} (e x)) (HSMul.hSMul.\{0, u_2, u_2\} t \operatorname{coe} (e y)))) \to \forall (x : \operatorname{coe} S), Membership.mem.\{u_1, u_1\} (Set.extremePoints.\{0, u_1\} \mathbb{R} S) \operatorname{coe} x \iff Membership.mem.\{u_2, u_2\} (Set.extremePoints.\{0, u_2\} \mathbb{R} T) \operatorname{coe} (e x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.extreme_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply extreme_forward first to e with haff. For the converse, the same affine equivalence for e.symm follows by substituting inverse images into haff and reversing the equivalence. A second application of extreme_forward and the inverse laws returns extremality of x.

**Theorem 1.28 (real_complex_extreme_iff).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)), Membership.mem.\{u, u\} (Set.extremePoints.\{0, u\} \mathbb{R} (ReconstructedStateGNS.realStateSpace.\{u\} A)) \operatorname{coe} \beta \iff Membership.mem.\{u, u\} (Set.extremePoints.\{0, u\} \mathbb{R} (ReconstructedStateGNS.complexStateSpace.\{u\} A)) \operatorname{coe} (ReconstructedStateGNS.extension.\{u\} \beta )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.real_complex_extreme_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse identities restriction_extension and extension_restriction define realComplexEquiv, and extension_affine_iff preserves every real affine relation. Applying extreme_equiv to these data transports extremality in the whole real state space to extremality in the whole complex state space.

**Theorem 1.29 (provider_mem).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (omega : Physicslib4.GNS.State.\{u\} A), Membership.mem.\{u, u\} (ReconstructedStateGNS.complexStateSpace.\{u\} A) (Physicslib4.GNS.State.toContinuousLinearMap.\{u\} omega )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.provider_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

State.toPositiveLinearMap makes every nonnegative algebra element have nonnegative image, and State.apply_one gives the value 1 at the unit. Consequently the underlying continuous linear functional satisfies exactly complexStateSpace's positivity and normalization conditions.

**Theorem 1.30 (provider_stateSpace_eq).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A], Eq.\{u + 1\} (Physicslib4.GNS.stateSpace.\{u\} A) (ReconstructedStateGNS.complexStateSpace.\{u\} A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.provider_stateSpace_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unpack membership in the range defining Physicslib4.GNS.stateSpace. Each such underlying functional lies in complexStateSpace by provider_mem. Conversely provider bundles any member of complexStateSpace into a State with that same functional, giving the opposite inclusion.

**Theorem 1.31 (original_moment).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)) (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} ((ReconstructedStateGNS.originalState.\{u\} \beta ) \operatorname{coe} a) \operatorname{coe} (\operatorname{coe} \beta a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.original_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

originalState is provider applied to extension, and provider leaves the continuous linear functional unchanged. Therefore extension_moment supplies the original beta moment directly; the bundling adds only positivity and normalization proofs.

**Theorem 1.32 (original_extreme_iff).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)), Membership.mem.\{u, u\} (Set.extremePoints.\{0, u\} \mathbb{R} (ReconstructedStateGNS.realStateSpace.\{u\} A)) \operatorname{coe} \beta \iff Physicslib4.GNS.State.IsExtremePoint.\{u\} (ReconstructedStateGNS.originalState.\{u\} \beta )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.original_extreme_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rewrite State.IsExtremePoint using mem_extremePoints_iff_isExtremePoint, then identify the provider state space with complexStateSpace using provider_stateSpace_eq. The remaining real-to-complex equivalence is real_complex_extreme_iff, so the original whole-state-space extremality is retained.

**Theorem 1.33 (original_pure_iff).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)), Membership.mem.\{u, u\} (Set.extremePoints.\{0, u\} \mathbb{R} (ReconstructedStateGNS.realStateSpace.\{u\} A)) \operatorname{coe} \beta \iff Physicslib4.GNS.IsPure.\{u\} (ReconstructedStateGNS.originalState.\{u\} \beta )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.original_pure_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use isPure_iff_isExtremePoint to replace purity of originalState by its convex extremality. The equivalence original_extreme_iff then identifies this with extremality of beta in the whole original real state space.

**Theorem 1.34 (actual_pure_gns).**

$$\forall A \in \operatorname{Type} u,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall beta \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{selfAdjoint}\left(A\right), \mathbb{R}\right),\; (\operatorname{IsRealState}\left(beta\right)) \Rightarrow ((beta \in \operatorname{extremePoints}\left(\mathbb{R}, \operatorname{realStateSpace}\left(A\right)\right)) \Rightarrow (\exists phi \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, A, \mathbb{C}\right),\; (phi \in \operatorname{complexStateSpace}\left(A\right)) \land ((\forall a \in \operatorname{selfAdjoint}\left(A\right),\; phi\left((a:A)\right) = (beta\left(a\right):\mathbb{C})) \land ((\forall psi \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, A, \mathbb{C}\right),\; (psi \in \operatorname{complexStateSpace}\left(A\right)) \Rightarrow ((\forall a \in \operatorname{selfAdjoint}\left(A\right),\; psi\left((a:A)\right) = (beta\left(a\right):\mathbb{C})) \Rightarrow (psi = phi))) \land (\exists H \in \operatorname{Type} u,\; \exists [\operatorname{NormedAddCommGroup}\left(H\right)] , \exists [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)], \exists [\operatorname{CompleteSpace}\left(H\right)] , \exists pi \in \operatorname{StarAlgHom}\left(\mathbb{C}, A, \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)\right),\; \exists Omega \in H,\; (\left\lVert Omega \right\rVert = 1) \land ((\operatorname{Dense}\left(\operatorname{range}\left((a:A) \mapsto pi\left(a\right)\left(Omega\right)\right)\right)) \land ((\forall a \in A,\; phi\left(a\right) = \operatorname{inner}\left(\mathbb{C}, Omega, pi\left(a\right)\left(Omega\right)\right)) \land ((\forall a \in \operatorname{selfAdjoint}\left(A\right),\; \operatorname{inner}\left(\mathbb{C}, Omega, pi\left((a:A)\right)\left(Omega\right)\right) = (beta\left(a\right):\mathbb{C})) \land (\forall T \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; (\forall a \in A,\; pi\left(a\right) \cdot T = T \cdot pi\left(a\right)) \Rightarrow (\exists c \in \mathbb{C},\; T = (c) \cdot (1)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.actual_pure_gns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bundle beta as a real state and use original_pure_iff to obtain purity of originalState. gns_construction gives a same-universe cyclic representation and its exact moments; evaluating the unit moment and State.apply_one gives norm(Omega)=1. ext_selfAdjoint proves uniqueness of the complex extension from its prescribed moments, and isIrreducible_of_isPure gives the scalar commutant conclusion. No representation, density or separability hypothesis is supplied as an input.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.actual_pure_gns`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.apply_one`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.exists_extension`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.ext_selfAdjoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.extension_affine_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.extension_moment`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.extension_restriction`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.extreme_equiv`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.extreme_forward`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.gns_construction`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.isExtremePoint_of_isPure`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.isPure_iff_isExtremePoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.isPure_of_isExtremePoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.mem_extremePoints_iff_isExtremePoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.norm_eq_re_apply_one_of_positive`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.original_extreme_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.original_moment`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.original_pure_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.provider_mem`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.provider_stateSpace_eq`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.realCLM_norm_le`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.real_complex_extreme_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.restriction_extension`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.restriction_mem`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.sigma_abs`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.sigma_sq`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.signedSquare_cone`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.signedSquare_norm`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.signed_endpoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.square_reading`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.state_abs_le`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.state_moment`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.toContinuousLinearMap_injective`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare.uniform_signed_original_square`
- Dependency: [D5/S3/Quantum/Algebra/CentralPositiveFunctionalExtension](../CentralPositiveFunctionalExtension.md)
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift](IrreducibleBoundedLift.md)
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky](TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.md)
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density](TauCeti/Analysis/VonNeumannAlgebra/Density.md)
