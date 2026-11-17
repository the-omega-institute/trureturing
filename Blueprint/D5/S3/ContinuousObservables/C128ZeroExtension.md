# Zero Extension of Whole Matrix C0 Fields

## Abstract

The full matrix zero-extension ideal on the compact unit interval.

**Theorem 1.1 (Whole zero extension and inverse restriction).**

$$(\operatorname{Isometry}(extensionHom)) \land (\operatorname{range}(extensionHom)=J) \land (\operatorname{IsClosed}(J)) \land (\forall (g: J), \operatorname{Ext}(\operatorname{Res}(g))=g) \land (\forall (f: A), \forall (t: U), \operatorname{Ext}(f, \operatorname{inc}(t))=\operatorname{f}(t)) \land (\forall (g: \operatorname{ContinuousMap}(Y, M)), g\in J \Rightarrow \forall (h: \operatorname{ContinuousMap}(Y, M)), (gh\in J) \land (\operatorname{star}(g)\in J))$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/C128ZeroExtension.whole_zero_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Y is the closed real interval [0,1]. U is (0,1/4) with every reciprocal 1/n removed for natural n at least 5. M is CStarMatrix (Fin 2) (Fin 2) C with its operator norm. A is the entire algebra C0(U,M), and J is independently defined as all continuous M-valued fields on Y that vanish off U. Ext is extension by zero, Res is restriction, and inc is the original inclusion U into Y.

The complex linear map extensionHom preserves multiplication and star. It is an isometry onto all of J. The ideal J is closed, is closed under right multiplication by every ambient continuous field, and is star invariant; left multiplication is part of its Ideal structure. For every g in J, Ext(Res(g))=g; every f in A is recovered pointwise on U. All norms are the inherited matrix operator uniform norms.

The collapse of the complement of U to the added point of OnePoint U is continuous: open neighborhoods of that point have compact complement in U, whose image is closed in the real line. Composing this collapse with the existing OnePoint extension proves continuity at every endpoint and deleted reciprocal. Conversely, every positive norm-level set of a field in J is compact in Y and lies wholly in U. Pulling these level sets back proves that its restriction vanishes at infinity. No compact-support condition is imposed on a field in A.

The selfadjoint restriction uses this whole ideal. This result supplies no polynomial-domain completeness, multiplier reconstruction, norm recovery on original polynomial labels, complete quantum model, or physical realization.

## References

- Truth anchor: `D5/S3/ContinuousObservables/C128ZeroExtension.whole_zero_extension`
- Dependency: [D5/S3/ContinuousObservables/C0Multipliers](C0Multipliers.md)
