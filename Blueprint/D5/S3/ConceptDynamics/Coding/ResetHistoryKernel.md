# Original dynamics and cyclic arithmetic

## Abstract

Large finite nonabelian subgroups in the original Reset beam representation kernel.

The original rho acts on DimensionGroup(resetMatrix q) by actual beam pushforward. Every full history automorphism commutes with UNIT shift; rho_unitShift identifies its native image with forward resetTheta. nativePolynomialEquiv then makes the transported image polynomial-linear on QF=Z[X]/(F q). Its value at 1 determines it as multiplication by that value, so actual image maps commute. No ring is installed on Native.

The live nonbinding input is MarkerPermutationAction's faithful guarded action on ALL original Reset histories. Its marker and eligibility invariance are indispensable to the inverse and group law. Reindexing, cyclicity, centralizer commutativity and commutator transport are consumed library applications, not separate mathematical contributions. The classical marker method is attributed in the owning MarkerPermutationAction Scribe and the Boyle–Lind–Rudolph library note.

**Definition 1.1 (The prescribed finite symmetric group action).**

$$\forall q \in Nat, k \in Nat, hq \in 2 \le q, hk \in 2 \le k,\; \operatorname{symmetricAction}\left(q, k, hq, hk\right):\operatorname{MonoidHom}\left(\operatorname{Perm}\left(\operatorname{Fin}\left(2^{k}\right)\right), \operatorname{ResetFullAut}\left(q\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.symmetricAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin(2^k) is reindexed by the existing cardinal equivalence with Fin k→Bool. This transports the actual resetAction without changing any graph, history, shift, topology or representation. Its radius is 12k+5.

**Definition 1.2 (Alternating permutations land in the actual kernel).**

$$\forall q \in Nat, k \in Nat, hq \in 2 \le q, hk \in 2 \le k, hq0 \in 0 < q,\; \operatorname{alternatingKernelEmbedding}\left(q, k, hq, hk, hq0\right):\operatorname{MonoidHom}\left(\operatorname{alternatingGroup}\left(\operatorname{Fin}\left(2^{k}\right)\right), \operatorname{kernel}\left(\operatorname{rho}\left(q, hq0\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.alternatingKernelEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The hom restricts symmetricAction and codRestricts to (rho q hq0).ker. Every three-cycle is conjugate to its square in Sym, hence a commutator by mem_commutatorSet_of_isConj_sq. closure_three_cycles_eq_alternating and abelian rho image kill the entire alternating group. This includes k=2 and A4; it does not assume A4 perfect or use a cardinal>=5 theorem.

**Theorem 1.3 (Uniform original-kernel injectivity).**

$$\forall q \in Nat, k \in Nat, hq \in 2 \le q, hk \in 2 \le k, hq0 \in 0 < q,\; \operatorname{FunctionInjective}\left(\operatorname{alternatingKernelEmbedding}\left(q, k, hq, hk, hq0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.alternatingKernelEmbedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The injectivity is inherited from the genuine original-history action, whose guarded words are realized by existing positive-word extension. hq0 can be any proof of 0<q, which follows from q>=2. For k>=2 the alternating groups are nonabelian, including A4, and their factorial orders are unbounded as k grows. No cross-k compatibility, complete kernel classification or locally finite whole-kernel conclusion is claimed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.alternatingKernelEmbedding`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.alternatingKernelEmbedding_injective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetHistoryKernel.symmetricAction`
- Dependency: [D5/S3/ConceptDynamics/Coding/MarkerPermutationAction](MarkerPermutationAction.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart](ResetNativeIntegerChart.md)
