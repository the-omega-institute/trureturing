# Section Coboundary Criterion

## Abstract

An additive section exists exactly when the canonical kernel carry is a coboundary.

**Theorem 1.1 (Section existence and the carry coboundary criterion).**

$$\forall X, B, q, r, \operatorname{AddCommGroup}\left(X\right) \land \operatorname{AddCommGroup}\left(B\right) \land q: \operatorname{AddMonoidHom}\left(X, B\right) \land r: B \to X \land \operatorname{RightInverse}\left(r, q\right) \land \operatorname{r}(0) = 0 \Rightarrow \left(\exists s': \operatorname{AddMonoidHom}\left(B, X\right), \operatorname{RightInverse}\left(s', q\right) \Leftrightarrow \exists beta: B \to \operatorname{ker}(q), \forall a, b\in B, \operatorname{kernelCarry}(q, r, a, b) + \operatorname{additiveCoboundary}(q, beta, a, b) = 0\right) \land \left(\left(\neg \exists beta: B \to \operatorname{ker}(q), \forall a, b\in B, \operatorname{kernelCarry}(q, r, a, b) + \operatorname{additiveCoboundary}(q, beta, a, b) = 0\right) \Rightarrow \left(\neg \exists s': \operatorname{AddMonoidHom}\left(B, X\right), \operatorname{RightInverse}\left(s', q\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Cocycles/ExtensionSectionCoboundary.extension_section_iff_coboundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For additive commutative groups X and B, q is an additive quotient map and s is a set-theoretic right inverse with s(0)=0. The kernel-valued carry is the existing canonical construction, and the displayed coboundary is formed from a map beta into that kernel.

A homomorphic right-inverse section exists exactly when the carry is cancelled by such a coboundary. Consequently, absence of a coboundary witness rules out every additive section.

## References

- Truth anchor: `D5/S1/Deficit/Cocycles/ExtensionSectionCoboundary.extension_section_iff_coboundary`
- Dependency: [D5/S1/Deficit/Cocycles/AdditiveCarryCocycle](AdditiveCarryCocycle.md)
