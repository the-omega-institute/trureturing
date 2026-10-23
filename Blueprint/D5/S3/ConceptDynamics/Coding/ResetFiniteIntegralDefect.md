# Finite integral reset defect

## Abstract

Complete finite integral reset defect on the original right-row lattice.

Sign=Multiplicative Bool is the original two-element group, tau=ofAdd true, and VertexModule Sign q is Fin q -> MonoidAlgebra Int Sign. Each coordinate retains its identity and tau coefficients. T is the existing transition(resetMatrix q), using integerMatrix and right-row multiplication. At suffix zero it is right multiplication of the full row sum by tau; at each successor it reads the preceding coordinate. resetDefect q=L=id+T. NatPositive(q) means 0<q; Int denotes the integers. All positive q, including one, are covered. No rational replacement, positivity, mixing or geometric conjugacy hypothesis is used.

resetCharacter q is ell(y)=sum over even i<q of coeff_1(y_i)-coeff_tau(y_i). It is an Int-linear map. resetPreimage first applies the finite-companion codomain shear to y. For even q its initial value is the entire residual z. For odd q its initial value is single 1 (coeff_1(z)). It then uses the inverse adjacent-sum recurrence. The odd choice solves the residual precisely when its two coefficients agree. No division by two appears.

**Theorem 1.1 (The additive companion is the actual original right-row operator).**

$$\forall n \in Nat, v \in \operatorname{VertexModule}\left(Sign, \operatorname{succ}\left(n\right)\right),\; \operatorname{apply}\left(\operatorname{resetDefect}\left(\operatorname{succ}\left(n\right)\right), v\right) = \operatorname{companion}\left(resetFlip, n, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_defect_companion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

resetFlip is right multiplication by single tau 1, and companion is the finite additive map with head v(0)+resetFlip(sum v) and adjacent-sum tails. The equality directly reuses the original transition_zero and transition_succ coordinate facts. It identifies the actual operator without replacing either integer coefficient, and supplies the finite elimination and subsequent transition calculations.

**Theorem 1.2 (Unique integral solution at every positive even length).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{Even}\left(q\right) \Rightarrow \left(\forall y \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{apply}\left(\operatorname{resetDefect}\left(q\right), \operatorname{resetPreimage}\left(q, hq, y\right)\right) = y \land \left(\forall v \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{apply}\left(\operatorname{resetDefect}\left(q\right), v\right) = y \Leftrightarrow v = \operatorname{resetPreimage}\left(q, hq, y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_even_unique_solution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The separately defined domain and codomain equivalences reduce the even operator to identity on the entire integral carrier. The displayed solver is its unique inverse value. This is a finite lattice statement about the actual right-row map.

**Theorem 1.3 (The character is onto Int).**

$$\forall q \in Nat,\; \operatorname{NatPositive}\left(q\right) \Rightarrow \operatorname{Surjective}\left(\operatorname{resetCharacter}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_character_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Surjective means every integer is attained. Put single 1 k in the zero suffix and zero in all other suffixes; ell of this row is k. Thus the character is primitive, rather than an even-valued character obtained by using an anti-vector basis.

**Theorem 1.4 (Solvability is exactly vanishing of the primitive character).**

$$\forall q \in Nat,\; \left(\operatorname{NatPositive}\left(q\right) \land \operatorname{Odd}\left(q\right)\right) \Rightarrow \left(\forall y \in \operatorname{VertexModule}\left(Sign, q\right),\; \left(\exists v \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{apply}\left(\operatorname{resetDefect}\left(q\right), v\right) = y\right) \Leftrightarrow \operatorname{apply}\left(\operatorname{resetCharacter}\left(q\right), y\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_odd_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the codomain shear, the residual coefficient difference equals ell(y). When it is zero the residual is d(1+tau), and the initial value d[1] solves (id+rightTau)a=d(1+tau). The tail recurrence supplies an explicit integral preimage. Conversely the residual of L(v) has equal coefficients, so ell annihilates the whole image.

**Theorem 1.5 (The entire odd kernel has a unique integer generator coefficient).**

$$\forall q \in Nat,\; \left(\operatorname{NatPositive}\left(q\right) \land \operatorname{Odd}\left(q\right)\right) \Rightarrow \left(\forall v \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{apply}\left(\operatorname{resetDefect}\left(q\right), v\right) = 0 \Leftrightarrow \left(\exists k \in Int,\; v = \operatorname{integerScale}\left(k, \operatorname{resetOddVector}\left(q\right)\right) \land \left(\forall l \in Int,\; v = \operatorname{integerScale}\left(l, \operatorname{resetOddVector}\left(q\right)\right) \Rightarrow l = k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_odd_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

existsUnique means there exists exactly one integer k satisfying the equation. resetOddVector is the existing original row w_i=(-1)^i([1]-[tau]). Zero adjacent sums determine every coordinate from v_0; the residual equation forces v_0 to be k([1]-[tau]). Its identity coefficient recovers k uniquely. The earlier transition equation T(w)=-w supplies the reverse direction.

**Theorem 1.6 (All solutions differ by a unique multiple of the odd row).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{Odd}\left(q\right) \Rightarrow \left(\forall y \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{apply}\left(\operatorname{resetCharacter}\left(q\right), y\right) = 0 \Rightarrow \left(\forall v \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{apply}\left(\operatorname{resetDefect}\left(q\right), v\right) = y \Leftrightarrow \left(\exists k \in Int,\; v = \operatorname{add}\left(\operatorname{resetPreimage}\left(q, hq, y\right), \operatorname{integerScale}\left(k, \operatorname{resetOddVector}\left(q\right)\right)\right) \land \left(\forall l \in Int,\; v = \operatorname{add}\left(\operatorname{resetPreimage}\left(q, hq, y\right), \operatorname{integerScale}\left(l, \operatorname{resetOddVector}\left(q\right)\right)\right) \Rightarrow l = k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_odd_all_solutions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract the explicit particular solution. The difference lies in the full kernel, so the unique coefficient in the kernel theorem classifies every solution. Nonvanishing ell excludes any solution by the image theorem.

**Theorem 1.7 (The exact sequence on the full integer lattice).**

$$\forall q \in Nat,\; \left(\operatorname{NatPositive}\left(q\right) \land \operatorname{Odd}\left(q\right)\right) \Rightarrow \operatorname{range}\left(\operatorname{resetDefect}\left(q\right)\right) = \operatorname{kernel}\left(\operatorname{resetCharacter}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_odd_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

range and kernel are the Int-linear submodules of the displayed maps. Together with the surjective character, this equality gives exactness on the original lattice. It is used to identify its cokernel.

**Definition 1.8 (The full odd cokernel is Int).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right),\; \operatorname{hasType}\left(\operatorname{resetOddCokernelEquiv}\left(q, hq, ho\right), \operatorname{IntLinearEquiv}\left(\operatorname{quotient}\left(\operatorname{VertexModule}\left(Sign, q\right), \operatorname{range}\left(\operatorname{resetDefect}\left(q\right)\right)\right), Int\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.resetOddCokernelEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

hasType displays the definition's exact result type. IntLinearEquiv is a linear equivalence over Int, and quotient is the whole module modulo the displayed image. The equivalence is the first isomorphism theorem for ell after replacing its kernel by range(L). The cokernel is free cyclic and has no order-two torsion. At q=1, T(a,b)=(b,a), L(a,b)=(a+b,a+b), the kernel is the anti-diagonal and the image is the primitive diagonal. The vectors (1,1),(1,-1) have determinant -2 and do not form an integral basis. The generic scalar specialization A=Int,J=id instead leaves multiplication by two, so involution alone does not justify the free-cokernel conclusion. These results concern the finite carrier; transport to the stationary colimit requires a separate identification with the genuine shift action.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.resetOddCokernelEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_character_surjective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_defect_companion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_even_unique_solution`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_odd_all_solutions`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_odd_image`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_odd_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect.reset_odd_range`
- Dependency: [D5/S1/Recurrence/FiniteCompanionDefect](../../../S1/Recurrence/FiniteCompanionDefect.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction](ResetNativeOddObstruction.md)
