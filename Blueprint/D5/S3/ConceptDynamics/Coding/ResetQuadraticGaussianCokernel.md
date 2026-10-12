# Reset quadratic Gaussian cokernel

## Abstract

Two primitive integer residual characters classify the full two-step cokernel at q=4m+3.

Sign=Multiplicative Bool, tau=ofAdd true, and each original suffix coordinate is an element of Int[C2] with both integer coefficients retained. M=VertexModule Sign q is the original right-row module, T=transition(resetMatrix q) its original integer transition, and J=resetFlip is right multiplication by [tau]. J squares to identity. The result concerns the ordinary integer cokernel of id+T^2 for every q=4m+3; it imposes neither an order-cone equivalence nor a realization by a full reset automorphism. Other residue classes modulo four are not classified here.

**Definition 1.1 (Two genuine integer time steps).**

$$\forall q \in Nat,\; \operatorname{resetTwoStepDefect}\left(q\right) = \operatorname{endSum}\left(linearIdentity, \operatorname{power}\left(\operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right), 2\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel.resetTwoStepDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The endomorphism is exactly LinearMap.id + (transition(resetMatrix q))^2 on the original full integer row. The square is composition of the genuine transition with itself, not the separate complement-group action.

**Definition 1.2 (A primitive pair of integer characters).**

$$\forall m \in Nat,\; \operatorname{hasType}\left(\operatorname{resetGaussianCharacter}\left(m\right), \operatorname{IntLinearMap}\left(\operatorname{VertexModule}\left(Sign, \operatorname{add}\left(\operatorname{mul}\left(4, m\right), 3\right)\right), \operatorname{Prod}\left(Int, Int\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel.resetGaussianCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let z be the independently constructed quadratic companion codomain shear applied to y. The character is (coeff_1(z.head0)-coeff_tau(z.head0), coeff_1(z.head1)-coeff_tau(z.head1)). The shear incorporates the entire inhomogeneous skip-one tail recurrence. The pair is onto Int x Int: place single 1 k and single 1 l in the residual heads, zero in the residual tails, and use the inverse shear. This uses no half eigenvector and does not discard sign coefficients.

**Theorem 1.3 (The complete integral solvability criterion).**

$$\forall m \in Nat, y \in \operatorname{VertexModule}\left(Sign, \operatorname{add}\left(\operatorname{mul}\left(4, m\right), 3\right)\right),\; \left(\exists v \in \operatorname{VertexModule}\left(Sign, \operatorname{add}\left(\operatorname{mul}\left(4, m\right), 3\right)\right),\; \operatorname{apply}\left(\operatorname{resetTwoStepDefect}\left(\operatorname{add}\left(\operatorname{mul}\left(4, m\right), 3\right)\right), v\right) = y\right) \Leftrightarrow \operatorname{apply}\left(\operatorname{resetGaussianCharacter}\left(m\right), y\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel.reset_two_step_three_mod_four_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual T^2 coordinate formulas identify this defect with the quadratic additive companion. At q=4m+3 the integral normal form is ((id+J)(a+b),(id+J)(b),identity on tails). On Int[C2], the image of id+J consists exactly of rows whose two coefficients are equal; an integral preimage is single 1 k. Thus character zero is necessary and sufficient. For sufficiency, solve the two residual heads as (id+J)(a) and (id+J)(b), then reconstruct with free values a-b,b and the original residual tails. This is a full image criterion, not only a mod-two obstruction.

**Definition 1.4 (The exact cokernel is Int x Int).**

$$\forall m \in Nat,\; \operatorname{hasType}\left(\operatorname{resetGaussianCokernelEquiv}\left(m\right), \operatorname{IntLinearEquiv}\left(\operatorname{quotient}\left(\operatorname{VertexModule}\left(Sign, \operatorname{add}\left(\operatorname{mul}\left(4, m\right), 3\right)\right), \operatorname{range}\left(\operatorname{resetTwoStepDefect}\left(\operatorname{add}\left(\operatorname{mul}\left(4, m\right), 3\right)\right)\right)\right), \operatorname{Prod}\left(Int, Int\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel.resetGaussianCokernelEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete image criterion identifies range(id+T^2) with the kernel of the surjective primitive pair character. The first isomorphism theorem constructs the displayed integer-linear equivalence. In particular the ordinary cokernel is free of rank two, with no additional order-two torsion. Gaussian denotes the period-four recurrence a,b,-a,-b; the displayed target is its integer coordinate pair, not a separately proved Gaussian-ring module equivalence.

Native applicability. The existing resetNativeEquiv q hq identifies the original stationary dimension group with stage-zero integer rows, and resetNativeEquiv_theta states F Theta=T F. Applying it twice gives F(id+Theta^2)=(id+T^2)F. Therefore the same exact image and ordinary cokernel transport to genuine native time. This paragraph describes that application of the existing equivalence; it asserts no full reset-group classification or RH result.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel.resetGaussianCharacter`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel.resetGaussianCokernelEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel.resetTwoStepDefect`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel.reset_two_step_three_mod_four_image`
- Dependency: [D5/S1/Recurrence/QuadraticCompanionDefect](../../../S1/Recurrence/QuadraticCompanionDefect.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect](ResetNativeIntegralDefect.md)
