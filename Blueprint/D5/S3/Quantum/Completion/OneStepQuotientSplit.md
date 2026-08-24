# One-Step Quotient Split

## Abstract

One orthogonal shell canonically splits successive Hilbert quotients.

**Theorem 1.1 (One orthogonal shell gives a split quotient sequence).**

$$\begin{gathered}\forall k, H, S, E,\\{}\operatorname{Hilbert}\left(k, H\right), \operatorname{HasOrthogonalProjection}\left(S\right), \operatorname{HasOrthogonalProjection}\left(E + S\right),\\{}\operatorname{Complete}\left(E\right), S \perp E \Rightarrow \\{}\operatorname{Injective}\left(\operatorname{shellEmbedding}\left(S, E\right)\right) \land \operatorname{Surjective}\left(\operatorname{stepMap}\left(S, E\right)\right) \land\\{}\operatorname{range}\left(\operatorname{shellEmbedding}\left(S, E\right)\right) = \operatorname{ker}\left(\operatorname{stepMap}\left(S, E\right)\right) \land\\{}(\forall e\in E, \operatorname{shellEmbedding}\left(S, E\right)(e) = \operatorname{class}\left(e, S\right)) \land\\{}(\forall e\in E, \operatorname{shellKernelEquiv}\left(S, E\right)(e) = \operatorname{shellEmbedding}\left(S, E\right)(e)) \land\\{}\operatorname{successiveQuotientShellEquiv}\left(S, E\right): \operatorname{Quotient}\left(E + S, S\right) \to E \land\\{}\operatorname{quotientShellSplit}\left(S, E\right): \operatorname{Quotient}\left(H, S\right) \to \operatorname{L2Sum}\left(E, \operatorname{Quotient}\left(H, E + S\right)\right) \land\\{}(\forall e\in E, \operatorname{fst}\left(\operatorname{quotientShellSplit}\left(S, E\right)(\operatorname{shellEmbedding}\left(S, E\right)(e))\right) = e).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/OneStepQuotientSplit.one_step_quotient_split_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be the old visible subspace of a real-or-complex Hilbert space and E an orthogonal shell. The next visible space is constructed as E plus S, and both quotient maps are the canonical submodule quotient maps.

The shell map is injective, the step map is surjective, and the range of the former is exactly the kernel of the latter. The public computation rule sends e to its class modulo S.

The named kernel equivalence and second-isomorphism-law equivalence identify both the kernel and the literal successive quotient with E. The named Hilbert equivalence splits the old quotient as the L2 product of E and the next quotient, with E as its first coordinate.

The proof applies the repository's canonical quotient-orthogonal isometry and Mathlib's factor map, kernel formula, second isomorphism law, and orthogonal decomposition. No existing declaration combined all public clauses.

## References

- Truth anchor: `D5/S3/Quantum/Completion/OneStepQuotientSplit.one_step_quotient_split_exact`
- Dependency: [D5/S3/Quantum/Algebra/QuotientOrthogonalComplement](../Algebra/QuotientOrthogonalComplement.md)
