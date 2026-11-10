# Pure GNS for original real states

## Abstract

Pure GNS for original real states

Let A be an arbitrary nontrivial unital complex C*-algebra in Type u with PartialOrder A and StarOrderedRing A. A real state beta is an arbitrary real linear functional on selfAdjoint A, positive on original nonnegative elements, with beta(1)=1. Continuity is a consequence of positivity and normalization. It has a unique positive normalized continuous complex linear extension phi to the same A, agreeing with beta on every original self-adjoint element. Restriction and extension give an affine equivalence of the whole real and complex state spaces. If beta is extreme in the whole original real state space, there are a complete complex Hilbert space H in Type u, a unital star representation pi of A and a unit cyclic vector Omega. For every a in A, phi(a)=inner(Omega,pi(a)Omega); for every original self-adjoint a the moment is beta(a). Every bounded operator commuting with pi(A) is a complex scalar multiple of the identity. Continuity, purity, interpolation and a GNS representation are not premises.

**Theorem 1.1 (state_abs_le).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : LinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{R} ) \operatorname{carrier} (selfAdjoint.\{u\} A) \mathbb{R} ), ReconstructedStateGNS.IsRealState.\{u\} \beta \to \forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), LE.le.\{0\} (abs.\{0\} (\beta a)) (Norm.norm.\{u\} a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.state_abs_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity on y-x makes beta monotone. The self-adjoint order bounds neg_algebraMap_norm_le_self and le_algebraMap_norm_self place a between minus norm(a) times 1 and norm(a) times 1. Apply monotonicity and beta(1)=1 to these bounds, then use abs_le.

**Theorem 1.2 (realCLM_norm_le).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : LinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{R} ) \operatorname{carrier} (selfAdjoint.\{u\} A) \mathbb{R} ) (h\beta : ReconstructedStateGNS.IsRealState.\{u\} \beta ), LE.le.\{0\} (Norm.norm.\{u\} (ReconstructedStateGNS.realCLM.\{u\} \beta h\beta )) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.realCLM_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The estimate state_abs_le bounds the original real linear functional by norm(a) with constant 1. LinearMap.mkContinuous_norm_le therefore bounds the operator norm of realCLM by 1; continuity is obtained from positivity and normalization rather than assumed of beta.

**Theorem 1.3 (state_moment).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\phi : ContinuousLinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} ), Membership.mem.\{u, u\} (ReconstructedStateGNS.complexStateSpace.\{u\} A) \phi \to \forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (\phi \operatorname{coe} a) \operatorname{coe} ((ReconstructedStateGNS.restriction.\{u\} \phi ) a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.state_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Regard phi as the positive map positiveMap phi hphi. Positive maps preserve self-adjointness, so phi(a) is a real complex number for self-adjoint a. Complex.re_eq_ofReal_of_isSelfAdjoint identifies it with the embedded real part, which is exactly restriction phi a.

**Theorem 1.4 (restriction_mem).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\phi : ContinuousLinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} ), Membership.mem.\{u, u\} (ReconstructedStateGNS.complexStateSpace.\{u\} A) \phi \to Membership.mem.\{u, u\} (ReconstructedStateGNS.realStateSpace.\{u\} A) (ReconstructedStateGNS.restriction.\{u\} \phi )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.restriction_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive original self-adjoint a, positivity of phi and Complex.nonneg_iff give nonnegativity of its real part. At the unit, phi(1)=1 implies that the restriction has value 1. These are precisely the two conditions of IsRealState.

**Theorem 1.5 (ext_selfAdjoint).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\phi \psi : ContinuousLinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} ), (\forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (\phi \operatorname{coe} a) (\psi \operatorname{coe} a)) \to Eq.\{u + 1\} \phi \psi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.ext_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decompose an arbitrary a with realPart_add_I_smul_imaginaryPart into a self-adjoint real part plus i times a self-adjoint imaginary part. Complex linearity and the assumed equality on both parts imply equality at a, and continuous-linear-map extensionality finishes.

**Theorem 1.6 (exists_extension).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : LinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{R} ) \operatorname{carrier} (selfAdjoint.\{u\} A) \mathbb{R} ), ReconstructedStateGNS.IsRealState.\{u\} \beta \to \exists (\phi : ContinuousLinearMap.\{0, 0, u, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} ), Membership.mem.\{u, u\} (ReconstructedStateGNS.complexStateSpace.\{u\} A) \phi \land \forall (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (\phi \operatorname{coe} a) \operatorname{coe} (\beta a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.exists_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply exists_positive_extensions_norm_additive to realCLM beta, obtaining positive p,n with beta=Re(p-n) on the self-adjoint part and norm(realCLM)=Re(p(1))+Re(n(1)). Normalization and realCLM_norm_le force Re(n(1))=0. PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one then makes n zero. Self-adjoint preservation identifies p(a) with the embedded beta(a), including p(1)=1, so p is the required positive normalized complex extension.

**Theorem 1.7 (extension_moment).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)) (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} (\operatorname{coe} (ReconstructedStateGNS.extension.\{u\} \beta ) \operatorname{coe} a) \operatorname{coe} (\operatorname{coe} \beta a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.extension_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The extension is chosen from exists_extension, whose second conclusion specifies every original self-adjoint moment. Its choose_spec therefore supplies this equality for each a. This records the exact moments of the chosen extension, without adding a continuity assumption on the starting beta.

**Theorem 1.8 (restriction_extension).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)), Eq.\{u + 1\} (ReconstructedStateGNS.restriction.\{u\} \operatorname{coe} (ReconstructedStateGNS.extension.\{u\} \beta )) \operatorname{coe} \beta$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.restriction_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate both real linear maps at an arbitrary self-adjoint a. By extension_moment the complex value of the extension is the embedded beta(a); taking its real part and using Complex.ofReal_re recovers beta(a). Extensionality gives equality of maps.

**Theorem 1.9 (extension_restriction).**

$$\forall \{A : Type u\} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A] (\phi : complexStateSpace A), extension \langle restriction \phi .val, restriction_{mem} \phi .val \phi .property\rangle = \phi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.extension_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use ext_selfAdjoint to compare the two complex states after Subtype.ext. On each self-adjoint a, extension_moment equals the embedded restriction of phi, while state_moment identifies the latter with phi(a). Thus extension after restriction recovers the original complex state.

**Theorem 1.10 (extension_affine_iff).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (x y z : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)) (s t : \mathbb{R} ), Eq.\{u + 1\} (\operatorname{coe} z) (HAdd.hAdd.\{u, u, u\} (HSMul.hSMul.\{0, u, u\} s \operatorname{coe} x) (HSMul.hSMul.\{0, u, u\} t \operatorname{coe} y)) \iff Eq.\{u + 1\} (\operatorname{coe} (ReconstructedStateGNS.extension.\{u\} z)) (HAdd.hAdd.\{u, u, u\} (HSMul.hSMul.\{0, u, u\} s \operatorname{coe} (ReconstructedStateGNS.extension.\{u\} x)) (HSMul.hSMul.\{0, u, u\} t \operatorname{coe} (ReconstructedStateGNS.extension.\{u\} y)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.extension_affine_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the forward implication, evaluate the real affine identity at a self-adjoint element, embed the resulting real equality into the complex numbers, and use extension_moment and ext_selfAdjoint. For the reverse implication apply the real linear map restriction to the complex affine identity and simplify with restriction_extension. The coefficients s,t are arbitrary real numbers, without convexity assumptions.

**Theorem 1.11 (extreme_forward).**

$$\forall \{E : Type u_1\} \{F : Type u_2\} [AddCommGroup.\{u_1\} E] [Module.\{0, u_1\} \mathbb{R} E] [AddCommGroup.\{u_2\} F] [Module.\{0, u_2\} \mathbb{R} F] \{S : Set.\{u_1\} E\} \{T : Set.\{u_2\} F\} (e : Equiv.\{u_1 + 1, u_2 + 1\} \operatorname{coe} S \operatorname{coe} T), (\forall (x y z : \operatorname{coe} S) (s t : \mathbb{R} ), Eq.\{u_1 + 1\} (\operatorname{coe} z) (HAdd.hAdd.\{u_1, u_1, u_1\} (HSMul.hSMul.\{0, u_1, u_1\} s \operatorname{coe} x) (HSMul.hSMul.\{0, u_1, u_1\} t \operatorname{coe} y)) \iff Eq.\{u_2 + 1\} (\operatorname{coe} (e z)) (HAdd.hAdd.\{u_2, u_2, u_2\} (HSMul.hSMul.\{0, u_2, u_2\} s \operatorname{coe} (e x)) (HSMul.hSMul.\{0, u_2, u_2\} t \operatorname{coe} (e y)))) \to \forall (x : \operatorname{coe} S), Membership.mem.\{u_1, u_1\} (Set.extremePoints.\{0, u_1\} \mathbb{R} S) \operatorname{coe} x \to Membership.mem.\{u_2, u_2\} (Set.extremePoints.\{0, u_2\} \mathbb{R} T) \operatorname{coe} (e x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.extreme_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use mem_extremePoints_iff_left. Pull the two endpoints of a target open segment back through e.symm, and use haff to pull back its same positive coefficients and sum-one relation. Extremality of x forces the first preimage to equal x; applying e transports that equality to the target endpoint.

**Theorem 1.12 (extreme_equiv).**

$$\forall \{E : Type u_1\} \{F : Type u_2\} [AddCommGroup.\{u_1\} E] [Module.\{0, u_1\} \mathbb{R} E] [AddCommGroup.\{u_2\} F] [Module.\{0, u_2\} \mathbb{R} F] \{S : Set.\{u_1\} E\} \{T : Set.\{u_2\} F\} (e : Equiv.\{u_1 + 1, u_2 + 1\} \operatorname{coe} S \operatorname{coe} T), (\forall (x y z : \operatorname{coe} S) (s t : \mathbb{R} ), Eq.\{u_1 + 1\} (\operatorname{coe} z) (HAdd.hAdd.\{u_1, u_1, u_1\} (HSMul.hSMul.\{0, u_1, u_1\} s \operatorname{coe} x) (HSMul.hSMul.\{0, u_1, u_1\} t \operatorname{coe} y)) \iff Eq.\{u_2 + 1\} (\operatorname{coe} (e z)) (HAdd.hAdd.\{u_2, u_2, u_2\} (HSMul.hSMul.\{0, u_2, u_2\} s \operatorname{coe} (e x)) (HSMul.hSMul.\{0, u_2, u_2\} t \operatorname{coe} (e y)))) \to \forall (x : \operatorname{coe} S), Membership.mem.\{u_1, u_1\} (Set.extremePoints.\{0, u_1\} \mathbb{R} S) \operatorname{coe} x \iff Membership.mem.\{u_2, u_2\} (Set.extremePoints.\{0, u_2\} \mathbb{R} T) \operatorname{coe} (e x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.extreme_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply extreme_forward first to e with haff. For the converse, the same affine equivalence for e.symm follows by substituting inverse images into haff and reversing the equivalence. A second application of extreme_forward and the inverse laws returns extremality of x.

**Theorem 1.13 (real_complex_extreme_iff).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)), Membership.mem.\{u, u\} (Set.extremePoints.\{0, u\} \mathbb{R} (ReconstructedStateGNS.realStateSpace.\{u\} A)) \operatorname{coe} \beta \iff Membership.mem.\{u, u\} (Set.extremePoints.\{0, u\} \mathbb{R} (ReconstructedStateGNS.complexStateSpace.\{u\} A)) \operatorname{coe} (ReconstructedStateGNS.extension.\{u\} \beta )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.real_complex_extreme_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse identities restriction_extension and extension_restriction define realComplexEquiv, and extension_affine_iff preserves every real affine relation. Applying extreme_equiv to these data transports extremality in the whole real state space to extremality in the whole complex state space.

**Theorem 1.14 (provider_mem).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (omega : Physicslib4.GNS.State.\{u\} A), Membership.mem.\{u, u\} (ReconstructedStateGNS.complexStateSpace.\{u\} A) (Physicslib4.GNS.State.toContinuousLinearMap.\{u\} omega )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.provider_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

State.toPositiveLinearMap makes every nonnegative algebra element have nonnegative image, and State.apply_one gives the value 1 at the unit. Consequently the underlying continuous linear functional satisfies exactly complexStateSpace's positivity and normalization conditions.

**Theorem 1.15 (provider_stateSpace_eq).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A], Eq.\{u + 1\} (Physicslib4.GNS.stateSpace.\{u\} A) (ReconstructedStateGNS.complexStateSpace.\{u\} A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.provider_stateSpace_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unpack membership in the range defining Physicslib4.GNS.stateSpace. Each such underlying functional lies in complexStateSpace by provider_mem. Conversely provider bundles any member of complexStateSpace into a State with that same functional, giving the opposite inclusion.

**Theorem 1.16 (original_moment).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)) (a : \operatorname{carrier} (selfAdjoint.\{u\} A)), Eq.\{1\} ((ReconstructedStateGNS.originalState.\{u\} \beta ) \operatorname{coe} a) \operatorname{coe} (\operatorname{coe} \beta a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.original_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

originalState is provider applied to extension, and provider leaves the continuous linear functional unchanged. Therefore extension_moment supplies the original beta moment directly; the bundling adds only positivity and normalization proofs.

**Theorem 1.17 (original_extreme_iff).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)), Membership.mem.\{u, u\} (Set.extremePoints.\{0, u\} \mathbb{R} (ReconstructedStateGNS.realStateSpace.\{u\} A)) \operatorname{coe} \beta \iff Physicslib4.GNS.State.IsExtremePoint.\{u\} (ReconstructedStateGNS.originalState.\{u\} \beta )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.original_extreme_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rewrite State.IsExtremePoint using mem_extremePoints_iff_isExtremePoint, then identify the provider state space with complexStateSpace using provider_stateSpace_eq. The remaining real-to-complex equivalence is real_complex_extreme_iff, so the original whole-state-space extremality is retained.

**Theorem 1.18 (original_pure_iff).**

$$\forall \{A : Type u\} [CStarAlgebra.\{u\} A] [Nontrivial.\{u\} A] [PartialOrder.\{u\} A] [StarOrderedRing.\{u\} A] (\beta : \operatorname{coe} (ReconstructedStateGNS.realStateSpace.\{u\} A)), Membership.mem.\{u, u\} (Set.extremePoints.\{0, u\} \mathbb{R} (ReconstructedStateGNS.realStateSpace.\{u\} A)) \operatorname{coe} \beta \iff Physicslib4.GNS.IsPure.\{u\} (ReconstructedStateGNS.originalState.\{u\} \beta )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.original_pure_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use isPure_iff_isExtremePoint to replace purity of originalState by its convex extremality. The equivalence original_extreme_iff then identifies this with extremality of beta in the whole original real state space.

**Theorem 1.19 (actual_pure_gns).**

$$\forall A \in \operatorname{Type} u,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall beta \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{selfAdjoint}\left(A\right), \mathbb{R}\right),\; (\operatorname{IsRealState}\left(beta\right)) \Rightarrow ((beta \in \operatorname{extremePoints}\left(\mathbb{R}, \operatorname{realStateSpace}\left(A\right)\right)) \Rightarrow (\exists phi \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, A, \mathbb{C}\right),\; (phi \in \operatorname{complexStateSpace}\left(A\right)) \land ((\forall a \in \operatorname{selfAdjoint}\left(A\right),\; phi\left((a:A)\right) = (beta\left(a\right):\mathbb{C})) \land ((\forall psi \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, A, \mathbb{C}\right),\; (psi \in \operatorname{complexStateSpace}\left(A\right)) \Rightarrow ((\forall a \in \operatorname{selfAdjoint}\left(A\right),\; psi\left((a:A)\right) = (beta\left(a\right):\mathbb{C})) \Rightarrow (psi = phi))) \land (\exists H \in \operatorname{Type} u,\; \exists [\operatorname{NormedAddCommGroup}\left(H\right)] , \exists [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)], \exists [\operatorname{CompleteSpace}\left(H\right)] , \exists pi \in \operatorname{StarAlgHom}\left(\mathbb{C}, A, \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)\right),\; \exists Omega \in H,\; (\left\lVert Omega \right\rVert = 1) \land ((\operatorname{Dense}\left(\operatorname{range}\left((a:A) \mapsto pi\left(a\right)\left(Omega\right)\right)\right)) \land ((\forall a \in A,\; phi\left(a\right) = \operatorname{inner}\left(\mathbb{C}, Omega, pi\left(a\right)\left(Omega\right)\right)) \land ((\forall a \in \operatorname{selfAdjoint}\left(A\right),\; \operatorname{inner}\left(\mathbb{C}, Omega, pi\left((a:A)\right)\left(Omega\right)\right) = (beta\left(a\right):\mathbb{C})) \land (\forall T \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; (\forall a \in A,\; pi\left(a\right) \cdot T = T \cdot pi\left(a\right)) \Rightarrow (\exists c \in \mathbb{C},\; T = (c) \cdot (1)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.actual_pure_gns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bundle beta as a real state and use original_pure_iff to obtain purity of originalState. gns_construction gives a same-universe cyclic representation and its exact moments; evaluating the unit moment and State.apply_one gives norm(Omega)=1. ext_selfAdjoint proves uniqueness of the complex extension from its prescribed moments, and isIrreducible_of_isPure gives the scalar commutant conclusion. No representation, density or separability hypothesis is supplied as an input.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.actual_pure_gns`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.exists_extension`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.ext_selfAdjoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.extension_affine_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.extension_moment`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.extension_restriction`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.extreme_equiv`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.extreme_forward`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.original_extreme_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.original_moment`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.original_pure_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.provider_mem`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.provider_stateSpace_eq`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.realCLM_norm_le`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.real_complex_extreme_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.restriction_extension`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.restriction_mem`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.state_abs_le`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS.state_moment`
- Dependency: [D5/S3/Quantum/Algebra/CentralPositiveFunctionalExtension](../CentralPositiveFunctionalExtension.md)
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState](Physicslib4/GNS/ExtremeState.md)
