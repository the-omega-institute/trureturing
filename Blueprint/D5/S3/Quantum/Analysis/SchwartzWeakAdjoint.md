# Compact Tests and the Schwartz Adjoint

## Abstract

Compact smooth tests characterize the adjoint of the actual Schwartz differential operator.

**Theorem 1.1 (The full differential sum has a densely defined symmetric Schwartz domain).**

$$\forall d \in Nat, a \in \operatorname{Fin}\left(d\right) \to \mathbb{R}, b \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \operatorname{DenseDomain}\left(\operatorname{S}\left(d, a, b\right)\right) \land \left(\operatorname{Symmetric}\left(\operatorname{S}\left(d, a, b\right)\right) \land \left(\operatorname{Closable}\left(\operatorname{S}\left(d, a, b\right)\right) \land \left(\forall f \in \operatorname{H}\left(d\right), g \in \operatorname{H}\left(d\right),\; \operatorname{Weak}\left(d, a, b, f, g\right) \Leftrightarrow \operatorname{GraphMember}\left(\operatorname{adjoint}\left(\operatorname{S}\left(d, a, b\right)\right), f, g\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/SchwartzWeakAdjoint.compact_test_adjoint_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural dimension d, H is the actual complex Lebesgue L2 space on EuclideanSpace Real (Fin d). The coefficients a and b are arbitrary real functions on Fin d. J embeds a Schwartz function as its actual L2 class. The differential D is the finite sum of minus a of j times its second coordinate derivative plus b of j times coordinate j squared times the function.

S has precisely the range of J as its domain and sends J of phi to J of D phi. It has dense domain, is symmetric and is closable. For arbitrary L2 vectors f and g, Weak means that the inner product of J D psi with f equals that of J psi with g for every smooth compactly supported function psi on the actual Euclidean space, using its canonical Schwartz realization. Weak holds exactly when the pair f and g lies in the graph of the actual adjoint of S.

A compact smooth bump and simultaneous cutoff convergence of J psi and J D psi extend the identity to all Schwartz tests. Real bilinear integration by parts with conjugate z times w gives symmetry of the second derivatives. The real quadratic potential is symmetric pointwise. The closed adjoint contains S.

No derivative or potential term is required to be separately square integrable for f or g. Dimension zero and coefficients of either sign are included.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/SchwartzWeakAdjoint.compact_test_adjoint_graph`
- Dependency: [D5/S3/Quantum/Analysis/SchwartzCutoffGraph](SchwartzCutoffGraph.md)
