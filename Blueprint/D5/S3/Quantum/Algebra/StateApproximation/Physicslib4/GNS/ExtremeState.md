# Purity and whole-state-space extremality

## Abstract

Purity and whole-state-space extremality

A state is pure when every positive functional dominated by it is a scalar multiple of it. This is equivalent to extremality in the entire convex state space. For positive continuous functionals, the operator norm is the real value at the unit; normalization then gives omega(1)=1. Restriction or a chosen family of states is not substituted for the whole state space.

**Theorem 1.1 (norm_eq_re_apply_one_of_positive).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] [Nontrivial.\{u_1\} A] \{\phi : ContinuousLinearMap.\{0, 0, u_1, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} \}, (\forall (a : A), LE.le.\{0\} 0 (\phi (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} a) a))) \to Eq.\{1\} (Norm.norm.\{u_1\} \phi ) (\phi 1).re$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.norm_eq_re_apply_one_of_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply cauchy_schwarz_inequality with first argument 1, then use CStarRing.norm_star_mul_self and the operator norm bound to obtain norm(phi(b)) squared at most Re(phi(1)) times norm(phi) times norm(b) squared. The induced operator norm estimate and nonnegativity imply norm(phi) at most Re(phi(1)), treating norm(phi)=0 separately. Evaluating at 1, whose norm is 1 in a nontrivial C*-algebra, gives the reverse inequality.

**Theorem 1.2 (apply_one).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] (omega : Physicslib4.GNS.State.\{u_1\} A), Eq.\{1\} (omega 1) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.apply_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The helper nontrivial_of_state excludes the zero algebra using the normalized operator norm. Then norm_eq_re_apply_one_of_positive identifies the real part of omega(1) with 1, while positivity at 1 forces its imaginary part to vanish. Complex extensionality gives the value 1.

**Theorem 1.3 (isExtremePoint_of_isPure).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] (omega : Physicslib4.GNS.State.\{u_1\} A), Physicslib4.GNS.IsPure.\{u_1\} omega \to Physicslib4.GNS.State.IsExtremePoint.\{u_1\} omega$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.isExtremePoint_of_isPure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a decomposition with 0<t<1, the positive functional psi=t omega1 is dominated by omega because the remaining term (1-t) omega2 is positive. Purity makes psi a scalar multiple of omega; State.apply_one fixes that scalar to t. Cancellation first identifies omega1 with omega, and then the decomposition identifies omega2 with omega.

**Theorem 1.4 (isPure_of_isExtremePoint).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] (omega : Physicslib4.GNS.State.\{u_1\} A), Physicslib4.GNS.State.IsExtremePoint.\{u_1\} omega \to Physicslib4.GNS.IsPure.\{u_1\} omega$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.isPure_of_isExtremePoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a dominated positive psi, norm_eq_re_apply_one_of_positive gives lambda=Re(psi(1))=norm(psi) in [0,1]. If lambda=0 then psi=0; if lambda=1 the positive complement omega-psi has norm zero. Otherwise normalize psi and omega-psi by lambda and 1-lambda to obtain two states in a genuine convex decomposition of omega; extremality equates these states and yields psi=lambda omega.

**Theorem 1.5 (isPure_iff_isExtremePoint).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] (omega : Physicslib4.GNS.State.\{u_1\} A), Physicslib4.GNS.IsPure.\{u_1\} omega \iff Physicslib4.GNS.State.IsExtremePoint.\{u_1\} omega$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.isPure_iff_isExtremePoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two implications are isExtremePoint_of_isPure and isPure_of_isExtremePoint. Their conjunction identifies the order-theoretic domination definition of purity with the pointwise convex-decomposition definition of extremality; no new characterization of representations is required here.

**Theorem 1.6 (toContinuousLinearMap_injective).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A], Function.Injective.\{u_1 + 1, u_1 + 1\} Physicslib4.GNS.State.toContinuousLinearMap.\{u_1\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.toContinuousLinearMap_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A State consists of its continuous linear functional and proofs of positivity and normalization. Equality of the functional therefore determines equality of states, since the remaining fields are propositions; State.mk.injEq implements this extensionality.

**Theorem 1.7 (mem_extremePoints_iff_isExtremePoint).**

$$\forall \{A : Type u_1\} [CStarAlgebra.\{u_1\} A] (omega : Physicslib4.GNS.State.\{u_1\} A), Membership.mem.\{u_1, u_1\} (Set.extremePoints.\{0, u_1\} \mathbb{R} (Physicslib4.GNS.stateSpace.\{u_1\} A)) (Physicslib4.GNS.State.toContinuousLinearMap.\{u_1\} omega ) \iff Physicslib4.GNS.State.IsExtremePoint.\{u_1\} omega$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.mem_extremePoints_iff_isExtremePoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translate a pointwise convex decomposition into membership of an openSegment in the real vector space of continuous linear functionals. In the forward direction, Mathlib's mem_extremePoints equates the endpoint functionals and State.toContinuousLinearMap_injective equates their states. Conversely write the positive segment coefficients as t and 1-t, apply State.IsExtremePoint, and use their sum being 1 to identify both endpoints with omega.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.apply_one`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.isExtremePoint_of_isPure`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.isPure_iff_isExtremePoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.isPure_of_isExtremePoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.mem_extremePoints_iff_isExtremePoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.norm_eq_re_apply_one_of_positive`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/ExtremeState.toContinuousLinearMap_injective`
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/CauchySchwarz](CauchySchwarz.md)
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/Irreducibility](Irreducibility.md)
