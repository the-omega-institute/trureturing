# Global Section Carry Criterion

## Abstract

An additive section exists exactly when canonical carry is cancelled by section carry.

**Theorem 1.1 (Section existence and canonical carry cancellation).**

$$\forall X, B, q, r, \operatorname{AddCommGroup}\left(X\right) \land \operatorname{AddCommGroup}\left(B\right) \land q: \operatorname{AddMonoidHom}\left(X, B\right) \land r: B \to X \land \operatorname{RightInverse}\left(r, q\right) \land \operatorname{r}(0) = 0 \Rightarrow \left(\exists s': \operatorname{AddMonoidHom}\left(B, X\right), \operatorname{RightInverse}\left(s', q\right) \Leftrightarrow \exists beta: B \to \operatorname{ker}(q), \forall a, b\in B, \operatorname{kernelCarry}(q, r, a, b) + \operatorname{sectionCarry}(beta, a, b) = 0\right) \land \left(\left(\neg \exists beta: B \to \operatorname{ker}(q), \forall a, b\in B, \operatorname{kernelCarry}(q, r, a, b) + \operatorname{sectionCarry}(beta, a, b) = 0\right) \Rightarrow \left(\neg \exists s': \operatorname{AddMonoidHom}\left(B, X\right), \operatorname{RightInverse}\left(s', q\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Cocycles/GlobalSectionCarryCriterion.global_section_iff_section_carry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For additive commutative groups X and B, q is an additive quotient map and r is a normalized set-theoretic right inverse. The kernel-valued carry and the carry of beta are both instances of the repository's canonical section-carry construction.

A homomorphic right-inverse section exists exactly when a kernel-valued change of section cancels the canonical carry. Consequently, absence of a cancellation witness rules out every additive section.

## References

- Truth anchor: `D5/S1/Deficit/Cocycles/GlobalSectionCarryCriterion.global_section_iff_section_carry`
- Dependency: [D5/S1/Deficit/Cocycles/AdditiveCarryCocycle](AdditiveCarryCocycle.md)
