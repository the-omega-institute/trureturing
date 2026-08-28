# Compatible Precision Tower Monotonicity

## Abstract

Adjacent levels of a compatible prime-indexed precision tower are ordered by refinement, with equality kernels ordered in reverse.

**Theorem 1.1 (Compatible adjacent precision levels refine monotonically).**

$$\forall X: \operatorname{Type},\\{}O: (p: \mathbb{N}, \operatorname{NatPrime}\left(p\right)) \to \mathbb{N} \to \operatorname{Type},\\{}q: \forall p: \mathbb{N}, \operatorname{NatPrime}\left(p\right), k: \mathbb{N}, X \to O_{p,k},\\{}rho: \forall p: \mathbb{N}, \operatorname{NatPrime}\left(p\right), k: \mathbb{N}, O_{p,k+1} \to O_{p,k},\\{}(\forall p, k, q_{p,k} = rho_{p,k+1,k} \circ q_{p,k+1}) \Rightarrow \forall p: \mathbb{N}, \operatorname{NatPrime}\left(p\right), k: \mathbb{N},\\{}\operatorname{Refines}\left(q_{p,k}, q_{p,k+1}\right) \land \operatorname{ker}\left(q_{p,k+1}\right) \subseteq \operatorname{ker}\left(q_{p,k}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/CompatiblePrecisionTowerMonotonicity.compatible_precision_tower_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p range over prime natural numbers. At every precision k, the readout q maps states into its level-dependent output type. A lowering map from level k + 1 to level k is required to recover the coarser readout exactly.

That lowering map is the canonical factor witnessing refinement. The repository's relative-identity refinement theorem then applies the same compatibility equation to contain the finer equality kernel in the coarser one.

Both clauses of theorem 7.1 are public: adjacent readout refinement and reverse inclusion of their equality kernels. No claim about the inverse limit or independence between levels is included.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/CompatiblePrecisionTowerMonotonicity.compatible_precision_tower_monotonicity`
- Dependency: [D5/S0/Rewriting/Quotients/RelativeIdentityRefinement](../../../S0/Rewriting/Quotients/RelativeIdentityRefinement.md)
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
