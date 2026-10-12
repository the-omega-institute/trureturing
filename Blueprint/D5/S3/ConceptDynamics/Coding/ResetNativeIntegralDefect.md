# Native integral reset defect

## Abstract

Integral reset dynamics, a signed primitive character and the arithmetic index of image plus kernel.

M=VertexModule Sign q is the original Fin q -> Int[C2] right-row module. G=DimensionGroup(resetMatrix q) is its original stationary Module.DirectLimit, with forward maps T raised to the stage difference. Sign=Multiplicative Bool and tau=ofAdd true. T is the original transition, whose head is (sum v)[tau] and whose successor coordinates read their predecessors. Theta=resetTheta is genuine time induced by T; the complement group action is a separate operator. NatPositive(q) means 0<q. Every assertion includes q=1 when its parity permits it.

**Definition 1.1 (An integral inverse of the actual transition).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{hasType}\left(\operatorname{resetInverse}\left(q, hq\right), \operatorname{IntEnd}\left(\operatorname{VertexModule}\left(Sign, q\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For q=n+1, P(y)=Fin.snoc (j maps to y(j.succ)) (resetFlip(y(0))-sum over Fin n of y(j.succ)). resetFlip is actual right multiplication by [tau]. It is involutive on both coefficients. The formula uses integer subtraction, so it need not preserve the coordinatewise nonnegative cone.

**Theorem 1.2 (Two exact inverse identities at every positive length).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{endMultiply}\left(\operatorname{resetInverse}\left(q, hq\right), \operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right)\right) = 1 \land \operatorname{endMultiply}\left(\operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{resetInverse}\left(q, hq\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_transition_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

endMultiply is multiplication in Module.End Int M, that is composition. The row sum of P(y) is resetFlip(y(0)), so the head of T(P(y)) is y(0); its tails recover y. In P(T(v)), the prefix is recovered, and subtraction of that prefix from the total sum recovers the last coordinate. The original transition_zero and transition_succ facts supply the coordinate equations.

**Definition 1.3 (The original transition is an integer-linear equivalence).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{hasType}\left(\operatorname{resetTransitionEquiv}\left(q, hq\right), \operatorname{IntLinearEquiv}\left(\operatorname{VertexModule}\left(Sign, q\right), \operatorname{VertexModule}\left(Sign, q\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetTransitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map is exactly T and its inverse is exactly P.

**Definition 1.4 (Faithful identification with stage zero).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{hasType}\left(\operatorname{resetNativeEquiv}\left(q, hq\right), \operatorname{IntLinearEquiv}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{VertexModule}\left(Sign, q\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F=resetNativeEquiv lifts the compatible family P raised to n. The identity P raised to j times T raised to j-i equals P raised to i proves compatibility in the endomorphism ring. Its inverse is the original stage-zero linear map. The direct-limit transition relation and T raised to n times P raised to n equals identity prove both sides. This module equivalence makes no order-cone assertion.

**Theorem 1.5 (The exact stage formula).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), n \in Nat, v \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{apply}\left(\operatorname{resetNativeEquiv}\left(q, hq\right), \operatorname{ModuleDirectLimitOf}\left(Int, Nat, \operatorname{VertexModule}\left(Sign, q\right), \operatorname{stationaryTransition}\left(\operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), n, v\right)\right) = \operatorname{apply}\left(\operatorname{power}\left(\operatorname{resetInverse}\left(q, hq\right), n\right), v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeEquiv_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At stage zero F(of_0(v))=v. At any later natural stage, F(of_n(v))=P raised to n applied to v. This retains the original forward directed system.

**Theorem 1.6 (Stage-zero coordinates preserve genuine time).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), x \in \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right),\; \operatorname{apply}\left(\operatorname{resetNativeEquiv}\left(q, hq\right), \operatorname{apply}\left(\operatorname{resetTheta}\left(q\right), x\right)\right) = \operatorname{apply}\left(\operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{apply}\left(\operatorname{resetNativeEquiv}\left(q, hq\right), x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeEquiv_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original resetTheta_apply_of describes the induced map on each stage. P and T commute because both compositions are identity; their powers therefore give F Theta=T F.

**Definition 1.7 (The primitive integer character on the native group).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{hasType}\left(\operatorname{resetNativeCharacter}\left(q, hq\right), \operatorname{IntLinearMap}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right), Int\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lambda=resetCharacter q composed with F. The finite character sums coeff_1 minus coeff_tau over even suffix indices. Its transport reads the entire original group, rather than a rational quotient or a sign-only replacement.

**Theorem 1.8 (The character changes sign between stages).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right), n \in Nat, v \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{apply}\left(\operatorname{resetNativeCharacter}\left(q, hq\right), \operatorname{ModuleDirectLimitOf}\left(Int, Nat, \operatorname{VertexModule}\left(Sign, q\right), \operatorname{stationaryTransition}\left(\operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), n, v\right)\right) = \operatorname{mul}\left(\operatorname{power}\left(-1, n\right), \operatorname{apply}\left(\operatorname{resetCharacter}\left(q\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_character_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite image criterion applied to v+Tv gives ell(Tv)=-ell(v). Applying this to Pv gives ell(Pv)=-ell(v); induction yields the signed stage formula. The unsigned prescription ell(v) at every stage does not descend, already for the q=1 swap.

**Theorem 1.9 (Time negates the character).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right), x \in \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right),\; \operatorname{apply}\left(\operatorname{resetNativeCharacter}\left(q, hq\right), \operatorname{apply}\left(\operatorname{resetTheta}\left(q\right), x\right)\right) = -\operatorname{apply}\left(\operatorname{resetNativeCharacter}\left(q, hq\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_character_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This follows from F Theta=T F and the finite image criterion, without a second suffix-parity calculation.

**Theorem 1.10 (Every integer is attained).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{Surjective}\left(\operatorname{resetNativeCharacter}\left(q, hq\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_character_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite character is surjective by the suffix-zero identity basis row. F is surjective, so the primitive character on G is surjective.

**Theorem 1.11 (The full native odd kernel is primitive cyclic).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right), x \in \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right),\; \operatorname{apply}\left(\operatorname{resetNativeDefect}\left(q\right), x\right) = 0 \Leftrightarrow \left(\exists k \in Int,\; x = \operatorname{integerScale}\left(k, \operatorname{resetOddClass}\left(q\right)\right) \land \left(\forall l \in Int,\; x = \operatorname{integerScale}\left(l, \operatorname{resetOddClass}\left(q\right)\right) \Rightarrow l = k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_odd_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

c=resetOddClass q is the existing stage-zero class of w_i=(-1)^i([1]-[tau]). The intertwining transports the finite reset_odd_kernel classification, and F(c)=w preserves its unique integer coefficient.

**Theorem 1.12 (Exact native solvability).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right), y \in \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right),\; \left(\exists x \in \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right),\; \operatorname{apply}\left(\operatorname{resetNativeDefect}\left(q\right), x\right) = y\right) \Leftrightarrow \operatorname{apply}\left(\operatorname{resetNativeCharacter}\left(q, hq\right), y\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_odd_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

F(id+Theta)=(id+T)F transports reset_odd_image on the full two-coefficient lattice. A finite integer preimage returns through F inverse to an actual native class.

**Theorem 1.13 (All odd solution fibres).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right),\; \forall y \in \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right),\; \operatorname{apply}\left(\operatorname{resetNativeCharacter}\left(q, hq\right), y\right) = 0 \Rightarrow \left(\forall x \in \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right),\; \operatorname{apply}\left(\operatorname{resetNativeDefect}\left(q\right), x\right) = y \Leftrightarrow \left(\exists k \in Int,\; x = \operatorname{add}\left(\operatorname{resetNativePreimage}\left(q, hq, y\right), \operatorname{integerScale}\left(k, \operatorname{resetOddClass}\left(q\right)\right)\right) \land \left(\forall l \in Int,\; x = \operatorname{add}\left(\operatorname{resetNativePreimage}\left(q, hq, y\right), \operatorname{integerScale}\left(l, \operatorname{resetOddClass}\left(q\right)\right)\right) \Rightarrow l = k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_odd_all_solutions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The particular native solution is F inverse applied to resetPreimage q hq (F y). Transport of reset_odd_all_solutions gives every solution with a unique integer parameter.

**Theorem 1.14 (The exact native image submodule).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right),\; \operatorname{range}\left(\operatorname{resetNativeDefect}\left(q\right)\right) = \operatorname{kernel}\left(\operatorname{resetNativeCharacter}\left(q, hq\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_odd_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The image is precisely the kernel of the primitive signed character.

**Definition 1.15 (The ordinary cokernel is Int).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right),\; \operatorname{hasType}\left(\operatorname{resetNativeOddCokernelEquiv}\left(q, hq, ho\right), \operatorname{IntLinearEquiv}\left(\operatorname{quotient}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{range}\left(\operatorname{resetNativeDefect}\left(q\right)\right)\right), Int\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeOddCokernelEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first isomorphism theorem for Lambda gives G/range(id+Theta) isomorphic to Int. This ordinary cokernel is free cyclic and has no hidden order-two torsion.

**Theorem 1.16 (The kernel pairs with the character by q+1).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right),\; \operatorname{apply}\left(\operatorname{resetNativeCharacter}\left(q, hq\right), \operatorname{resetOddClass}\left(q\right)\right) = \operatorname{intCast}\left(\operatorname{add}\left(q, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On w the even-index character summand is 1+(-1)^i. Summing gives q plus the alternating sum, which is one for odd q by Fin.sum_neg_one_pow. Thus Lambda(c)=q+1, although Lambda itself is onto all integers.

**Theorem 1.17 (The kernel and image meet only at zero).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right),\; \operatorname{submoduleInf}\left(\operatorname{kernel}\left(\operatorname{resetNativeDefect}\left(q\right)\right), \operatorname{range}\left(\operatorname{resetNativeDefect}\left(q\right)\right)\right) = bottomSubmodule$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_kernel_inf_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If x=kc belongs to the image, then 0=Lambda(x)=k(q+1). The positive integer q+1 is nonzero, forcing k=0. submoduleInf denotes intersection.

**Theorem 1.18 (Exact arithmetic membership in image plus kernel).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right), x \in \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right),\; \operatorname{member}\left(x, \operatorname{submoduleSup}\left(\operatorname{range}\left(\operatorname{resetNativeDefect}\left(q\right)\right), \operatorname{kernel}\left(\operatorname{resetNativeDefect}\left(q\right)\right)\right)\right) \Leftrightarrow \operatorname{Divides}\left(\operatorname{intCast}\left(\operatorname{add}\left(q, 1\right)\right), \operatorname{apply}\left(\operatorname{resetNativeCharacter}\left(q, hq\right), x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_sum_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If x=a+kc with a in the image, its character is k(q+1). Conversely, if Lambda(x)=k(q+1), subtract kc: the difference has zero character and hence lies in the image. submoduleSup is the actual sum of integer submodules.

**Definition 1.19 (The combined quotient is ZMod(q+1)).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right),\; \operatorname{hasType}\left(\operatorname{resetNativeCombinedQuotientEquiv}\left(q, hq, ho\right), \operatorname{IntLinearEquiv}\left(\operatorname{quotient}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{submoduleSup}\left(\operatorname{range}\left(\operatorname{resetNativeDefect}\left(q\right)\right), \operatorname{kernel}\left(\operatorname{resetNativeDefect}\left(q\right)\right)\right)\right), \operatorname{ZMod}\left(\operatorname{add}\left(q, 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeCombinedQuotientEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reduce Lambda modulo q+1. The exact divisibility criterion identifies its kernel with range(id+Theta) plus ker(id+Theta). Integer-cast surjectivity and Lambda surjectivity give the displayed integer-linear equivalence. At q=1 this quotient is ZMod 2 while the ordinary cokernel remains Int.

**Theorem 1.20 (No integer-linear equivariant section).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right),\; \neg \left(\exists s \in \operatorname{IntLinearMap}\left(Int, \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right)\right),\; \operatorname{compose}\left(\operatorname{resetNativeCharacter}\left(q, hq\right), s\right) = linearIdentity \land \left(\forall n \in Int,\; \operatorname{apply}\left(\operatorname{resetTheta}\left(q\right), \operatorname{apply}\left(s, n\right)\right) = \operatorname{apply}\left(s, -n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_no_equivariant_linear_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equivariance forces s(1) into the kernel, hence s(1)=kc. The section equation gives 1=k(q+1), impossible for positive q. The obstruction concerns additive or integer-linear sections. It does not forbid set sections: at q=1 the nonadditive map n maps to (max(n,0),max(-n,0)) is equivariant for coordinate swap. The underlying integer-linear surjection splits after forgetting the time action.

**Theorem 1.21 (Complete fibres for every positive length).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), y \in \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right), x \in \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right),\; \left(\operatorname{Even}\left(q\right) \Rightarrow \left(\operatorname{apply}\left(\operatorname{resetNativeDefect}\left(q\right), x\right) = y \Leftrightarrow x = \operatorname{resetNativePreimage}\left(q, hq, y\right)\right)\right) \land \left(\operatorname{Odd}\left(q\right) \Rightarrow \left(\operatorname{apply}\left(\operatorname{resetNativeDefect}\left(q\right), x\right) = y \Leftrightarrow \left(\operatorname{apply}\left(\operatorname{resetNativeCharacter}\left(q, hq\right), y\right) = 0 \land \left(\exists k \in Int,\; x = \operatorname{add}\left(\operatorname{resetNativePreimage}\left(q, hq, y\right), \operatorname{integerScale}\left(k, \operatorname{resetOddClass}\left(q\right)\right)\right) \land \left(\forall l \in Int,\; x = \operatorname{add}\left(\operatorname{resetNativePreimage}\left(q, hq, y\right), \operatorname{integerScale}\left(l, \operatorname{resetOddClass}\left(q\right)\right)\right) \Rightarrow l = k\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_all_solutions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive even q the transported finite solver gives the unique solution, so the native kernel and cokernel vanish. For positive odd q, vanishing of Lambda is exactly solvability and the full fibre is the particular solution plus Zc. Both cases use the original integer transition and the original stationary colimit.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetInverse`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeCharacter`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeCombinedQuotientEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeEquiv_stage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeEquiv_theta`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetNativeOddCokernelEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.resetTransitionEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_all_solutions`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_character_stage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_character_surjective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_character_theta`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_kernel_inf_range`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_no_equivariant_linear_section`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_odd_all_solutions`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_odd_image`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_odd_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_odd_range`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_pairing`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_native_sum_criterion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect.reset_transition_inverse`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect](ResetFiniteIntegralDefect.md)
