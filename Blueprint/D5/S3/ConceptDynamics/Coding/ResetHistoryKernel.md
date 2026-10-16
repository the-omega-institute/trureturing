# Original dynamics and cyclic arithmetic

## Abstract

Finite alternating subgroups and their simultaneous finite-support product in the original Reset kernel.

**Theorem 1.1 (Original full-rho commutation).**

$$\forall q \in Nat, hq \in 0 < q, h \in \operatorname{ResetFullAut}\left(q\right), x \in \operatorname{Native}\left(q\right),\; \operatorname{rho}\left(q, hq, h, \operatorname{resetTheta}\left(q, x\right)\right) = \operatorname{resetTheta}\left(q, \operatorname{rho}\left(q, hq, h, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.rho_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing owning argument applies the actual representation to the literal fullAutSubgroup shift-commutation law and uses rho_unitShift. It is public for ResetNativeUnitNormalForm's complete original-rho consumer.

**Theorem 1.2 (The consumed general scalar argument).**

$$\forall q \in Nat, hq \in 0 < q, A \in \operatorname{IntLinearEnd}\left(\operatorname{Native}\left(q\right)\right), ht \in \operatorname{commutesWithForwardTime}\left(q, A\right), b \in \operatorname{QF}\left(q\right),\; \operatorname{centralizingMap}\left(q, hq, A, ht, b\right) = \operatorname{multiply}\left(b, \operatorname{centralizingMap}\left(q, hq, A, ht, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.centralizingMap_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

commutesWithForwardTime(q,A) means forall x, A(resetTheta(q,x))=resetTheta(q,A(x)). centralizingMap transports A by nativeIntEquiv and promotes it to Int[X]-linearity with LinearMap.ofAEval. Polynomial-quotient surjectivity gives the scalar law. The original chartMap and chartMap_scalar specialize this same owning argument to actual rho. ResetNativeUnitNormalForm consumes it for both A and its inverse. This generalized helper supplies no new component-unit classification.

The original rho acts on DimensionGroup(resetMatrix q) by actual beam pushforward. Every full history automorphism commutes with UNIT shift; rho_unitShift identifies its native image with forward resetTheta. nativePolynomialEquiv then makes the transported image polynomial-linear on QF=Z[X]/(F q). Its value at 1 determines it as multiplication by that value, so actual image maps commute. No ring is installed on Native.

The live nonbinding input is MarkerPermutationAction's faithful guarded action on ALL original Reset histories. Its marker and eligibility invariance are indispensable to the inverse and group law. Reindexing, cyclicity, centralizer commutativity and commutator transport are consumed library applications, not separate mathematical contributions. The classical marker method is attributed in the owning MarkerPermutationAction Scribe and the Boyle–Lind–Rudolph library note.

**Definition 1.3 (The prescribed finite symmetric group action).**

$$\forall q \in Nat, k \in Nat, hq \in 2 \le q, hk \in 2 \le k,\; \operatorname{symmetricAction}\left(q, k, hq, hk\right):\operatorname{MonoidHom}\left(\operatorname{Perm}\left(\operatorname{Fin}\left(2^{k}\right)\right), \operatorname{ResetFullAut}\left(q\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.symmetricAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin(2^k) is reindexed by the existing cardinal equivalence with Fin k→Bool. This transports the actual resetAction without changing any graph, history, shift, topology or representation. Its radius is 12k+5.

**Definition 1.4 (Alternating permutations land in the actual kernel).**

$$\forall q \in Nat, k \in Nat, hq \in 2 \le q, hk \in 2 \le k, hq0 \in 0 < q,\; \operatorname{alternatingKernelEmbedding}\left(q, k, hq, hk, hq0\right):\operatorname{MonoidHom}\left(\operatorname{alternatingGroup}\left(\operatorname{Fin}\left(2^{k}\right)\right), \operatorname{kernel}\left(\operatorname{rho}\left(q, hq0\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.alternatingKernelEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The hom restricts symmetricAction and codRestricts to (rho q hq0).ker. Every three-cycle is conjugate to its square in Sym, hence a commutator by mem_commutatorSet_of_isConj_sq. closure_three_cycles_eq_alternating and abelian rho image kill the entire alternating group. This includes k=2 and A4; it does not assume A4 perfect or use a cardinal>=5 theorem.

**Theorem 1.5 (Uniform original-kernel injectivity).**

$$\forall q \in Nat, k \in Nat, hq \in 2 \le q, hk \in 2 \le k, hq0 \in 0 < q,\; \operatorname{FunctionInjective}\left(\operatorname{alternatingKernelEmbedding}\left(q, k, hq, hk, hq0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.alternatingKernelEmbedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The injectivity is inherited from the genuine original-history action, whose guarded words are realized by existing positive-word extension. hq0 can be any proof of 0<q, which follows from q>=2. For k>=2 the alternating groups are nonabelian, including A4, and their factorial orders are unbounded as k grows. No cross-k compatibility, complete kernel classification or locally finite whole-kernel conclusion is claimed.

**Definition 1.6 (A countable product with finite support).**

$$FiniteGapAlternating:Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.FiniteGapAlternating` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is Mathlib RestrictedProduct with n-th fiber Alt(Fin(2^(n+2))), bottom subgroups, and Filter.cofinite. A tuple has finitely many nonidentity coordinates, multiplied coordinatewise in their original noncommutative groups. The coordinate n=0 is A4.

**Definition 1.7 (Simultaneous action in the original kernel).**

$$\forall q \in Nat, hq \in 2 \le q, hqzero \in 0 < q,\; \operatorname{gapProductKernelEmbedding}\left(q, hq, hqzero\right):\operatorname{MonoidHom}\left(FiniteGapAlternating, \operatorname{kernel}\left(\operatorname{rho}\left(q, hqzero\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.gapProductKernelEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the actual signed edge b: (0,zeta)→(0,1), and a: (0,1)→(0,zeta). With c_h the chain 0→1 and d_h the reset from 1, U=a c_zeta d_zeta and V=c_one d_one c_zeta d_zeta are b-free loops at (0,1), of lengths 3 and 4. A bit is U^4 or V^3. Concatenating n+2 blocks and closing with a gives d(n)=12(n+2)+1 edges from target(b) to source(b). The first edges of the two blocks differ, so the codes are injective. All edges are transported through originalEdge with their actual labels, numbers and absolute signs. The chain requires q>=2.

**Theorem 1.8 (Joint faithfulness on all original histories).**

$$\forall q \in Nat, hq \in 2 \le q, hqzero \in 0 < q,\; \operatorname{FunctionInjective}\left(\operatorname{gapProductKernelEmbedding}\left(q, hq, hqzero\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.gapProductKernelEmbedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SeparatorGapAction proves that overlapping interiors between consecutive b edges have the same endpoints. It proves exact separator preservation, both directions of eligibility invariance, and cross-length commutation on arbitrary bilateral sequences. The legal seams use the distinct source and target of b. Its finite-support homomorphism acts on ALL History(ResetGraph q), commutes with the actual unit shift and has a real continuous inverse. On a realized word b D(n,i) b, every other length fixes the central data while coordinate n outputs D(n,g(n)(i)); this determines every coordinate of the tuple. Noncoded gaps, extra q>2 edges and arbitrary exterior tails are included. The original rho has commuting images by the cyclic integer chart. Alternating factors are killed as restrictions of these new symmetric actions, using three-cycle commutators in Sym, including A4. Subgroup closure places the finite product in the SAME rho kernel. The classical marker method is discussed in Library/FiniteGroups/boylelindrudolph1988automorphism.md. There is no q=1 claim, unrestricted infinite-product continuity, publication novelty claim or classification of the whole kernel.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.FiniteGapAlternating`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.alternatingKernelEmbedding`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.alternatingKernelEmbedding_injective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.centralizingMap_scalar`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.gapProductKernelEmbedding`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.gapProductKernelEmbedding_injective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.rho_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.symmetricAction`
- Dependency: [D5/S3/ConceptDynamics/Coding/MarkerPermutationAction](MarkerPermutationAction.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart](ResetNativeIntegerChart.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/SeparatorGapAction](SeparatorGapAction.md)
